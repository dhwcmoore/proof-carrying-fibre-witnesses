#!/usr/bin/env python3
"""Run the current Phase-1 checks and record evidence; never declare closure."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

import audit
import differential


ROOT = audit.IMPL.parent
OUTPUT = audit.IMPL / "release-audit"


def git_files(root):
    result = subprocess.run(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
                            cwd=root, check=True, capture_output=True)
    return set(result.stdout.decode().rstrip("\0").split("\0")) - {"MANIFEST.sha256"}


def verify_manifest(root, files):
    entries = {}
    for line in (root / "MANIFEST.sha256").read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if not match:
            raise audit.AuditError("malformed manifest entry")
        digest, name = match.groups()
        path = PurePosixPath(name)
        if path.is_absolute() or ".." in path.parts or path.as_posix() != name or name in entries:
            raise audit.AuditError(f"unsafe or duplicate manifest path: {name}")
        entries[name] = digest
    if set(entries) != files:
        raise audit.AuditError(f"manifest coverage differs: {sorted(set(entries) ^ files)}")
    for name, expected in entries.items():
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise audit.AuditError(f"manifest entry is not a regular file: {name}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise audit.AuditError(f"manifest digest mismatch: {name}")
    return len(entries)


def check_plan(data, impl=audit.IMPL):
    makefile = (impl / "Makefile").read_text()
    compiled = re.findall(r"^\tcoqc -Q rocq PCFW rocq/(\w+)\.v$", makefile, re.M)
    if compiled != data["compiled_modules"]:
        raise audit.AuditError("Makefile compilation order/coverage differs from _CoqProject")
    match = re.search(r"^\tcoqchk ([\s\S]*?)(?=\n\n)", makefile, re.M)
    checked = re.findall(r"PCFW\.(\w+)", match[1]) if match else []
    if len(checked) != len(set(checked)) or set(checked) != set(data["substantive_modules"]):
        raise audit.AuditError("coqchk coverage differs from substantive release modules")
    harnesses = sorted(p.stem for p in (impl / "ocaml").glob("test_*.ml"))
    invoked = re.findall(r"^\t\./ocaml/(test_\w+)$", makefile, re.M)
    if not harnesses or sorted(invoked) != harnesses:
        raise audit.AuditError("Makefile does not run every existing OCaml harness exactly once")
    return harnesses


def validate_check_log(text, data, harnesses):
    compiled = re.findall(r"^coqc -Q rocq PCFW rocq/(\w+)\.v$", text, re.M)
    if compiled != data["compiled_modules"]:
        raise audit.AuditError("check log does not confirm all formal/extraction compilations")
    if text.count("Modules were successfully checked") != 1:
        raise audit.AuditError("missing or unexpected coqchk success report")
    inspected = re.findall(r"^PASS: (\d+) release declarations inspected; no global axioms$", text, re.M)
    if inspected != [str(len(data["release_set"]))]:
        raise audit.AuditError("check log does not confirm the complete assumption audit")
    if len(re.findall(r"^PASS: project source token audit;", text, re.M)) != 1:
        raise audit.AuditError("check log does not confirm the source token audit")
    integer = re.findall(r"^PASS: integer structural audit; (\d+) extracted interfaces; no native int or historical mirror dependency$", text, re.M)
    if integer != [str(len(data["extraction_modules"]))]:
        raise audit.AuditError("check log does not confirm the integer structural audit")
    compared = re.findall(r"^PASS: differential battery; (\d+) cases; finite-case evidence only$", text, re.M)
    if compared != [str(len(differential.cases()))]:
        raise audit.AuditError("check log does not confirm the differential battery")
    invoked = re.findall(r"^\./ocaml/(test_\w+)$", text, re.M)
    if sorted(invoked) != harnesses:
        raise audit.AuditError("check log does not confirm every harness execution")


def validate_numeric_evidence(integers, compared, data):
    if integers["result"] != "PASS" or integers["extracted_module_count"] != len(data["extraction_modules"]) or integers["native_int_extracted_interface_count"] != 0:
        raise audit.AuditError("integer evidence is incomplete")
    cases = differential.cases()
    recorded = compared["cases"]
    if compared["result"] != "PASS" or compared["case_count"] != len(cases) or len(recorded) != len(cases):
        raise audit.AuditError("differential evidence is incomplete")
    for expected, actual in zip(cases, recorded):
        if any(actual[key] != expected[key] for key in ("input", "oracle_expression", "oracle_kind")) or actual["result"] != "PASS" or actual["oracle_result"] != actual["ocaml_result"]:
            raise audit.AuditError("differential case evidence differs")
    actual_count = sum(c["oracle_kind"].startswith("actual Gallina") for c in recorded)
    if compared["actual_Gallina_case_count"] != actual_count or compared["reference_Z_case_count"] != len(recorded) - actual_count:
        raise audit.AuditError("differential oracle counts differ")


def run_make(target, log):
    # Do not inherit -i/-k/-n/-s or jobserver flags from an enclosing make.
    # Library overrides are explicitly exported by the implementation Makefile.
    environment = dict(os.environ)
    for name in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES", "GNUMAKEFLAGS"):
        environment.pop(name, None)
    with log.open("w") as output:
        result = subprocess.run(["make", "--no-print-directory", target], cwd=audit.IMPL,
                                env=environment, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise audit.AuditError(f"make {target} failed ({result.returncode}); see {log}")


def main():
    OUTPUT.mkdir(exist_ok=True)
    summary_path = OUTPUT / "summary.json"
    summary = {"schema_version": 1, "started_utc": datetime.now(timezone.utc).isoformat(),
               "release_status": "OPEN / NOT YET CLOSED", "verification_status": "FAILED",
               "commit_sha": None, "toolchain_versions": {}, "substantive_module_count": None,
               "coqchk_result": "NOT_RUN", "theorem_assumption_audit_count": None,
               "assumption_audit_result": "NOT_RUN", "harness_count": None,
               "harness_result": "NOT_RUN", "manifest_verification_result": "NOT_RUN",
               "integer_structural_audit_result": "NOT_RUN", "differential_result": "NOT_RUN",
               "integration_harness_result": "NOT_RUN"}
    # Invalidate any previous passing summary before starting required checks.
    summary_path.write_text(json.dumps(summary, indent=2) + "\n")
    stage = "metadata"
    try:
        summary["commit_sha"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        summary["git_status"] = subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=ROOT, text=True).splitlines()
        for tool, command in {"coq": ["coqc", "--version"], "ocaml": ["ocamlc", "-version"],
                              "python": [sys.executable, "--version"]}.items():
            summary["toolchain_versions"][tool] = subprocess.check_output(command, text=True).strip()
        summary["library_paths"] = {key: os.environ.get(key) for key in ("OCAML_LIB", "ZARITH", "SHALIB")}
        stage = "manifest"
        summary["manifest_entry_count"] = verify_manifest(ROOT, git_files(ROOT))
        summary["manifest_sha256"] = hashlib.sha256((ROOT / "MANIFEST.sha256").read_bytes()).hexdigest()
        summary["manifest_verification_result"] = "PASS"
        stage = "source inventory"
        data = audit.inventory()
        harnesses = check_plan(data)
        audit.check_tokens(data)
        (OUTPUT / "inventory.json").write_text(json.dumps(data, indent=2) + "\n")
        summary.update(substantive_module_count=len(data["substantive_modules"]),
                       compiled_module_count=len(data["compiled_modules"]),
                       extraction_module_count=len(data["extraction_modules"]),
                       theorem_assumption_audit_count=len(data["release_set"]),
                       legacy_assumption_request_count=len(data["legacy_requests"]),
                       premise_declaration_count=len(data["premise_declarations"]),
                       harness_count=len(harnesses))
        stage = "clean"
        run_make("clean", OUTPUT / "clean.log")
        stage = "make check"
        summary.update(coqchk_result="NOT_CONFIRMED", assumption_audit_result="NOT_CONFIRMED",
                       harness_result="NOT_CONFIRMED")
        run_make("check", OUTPUT / "check.log")
        stage = "check evidence"
        validate_check_log((OUTPUT / "check.log").read_text(), data, harnesses)
        summary.update(coqchk_result="PASS", assumption_audit_result="PASS", harness_result="PASS")
        integers = json.loads((OUTPUT / "integer-correspondence.json").read_text())
        compared = json.loads((OUTPUT / "differential.json").read_text())
        validate_numeric_evidence(integers, compared, data)
        integration = [h for h in harnesses if h == "test_phase1_integration"]
        if not integration:
            raise audit.AuditError("typed integration harness missing")
        summary.update(integer_structural_audit_result="PASS",
                       exact_integer_extracted_module_count=integers["extracted_module_count"],
                       native_int_extracted_interface_count=integers["native_int_extracted_interface_count"],
                       historical_native_demo_count=integers["historical_native_demo_count"],
                       normative_wrapper_count=integers["normative_wrapper_count"],
                       differential_result="PASS", differential_case_count=compared["case_count"],
                       differential_actual_Gallina_case_count=compared["actual_Gallina_case_count"],
                       differential_reference_Z_case_count=compared["reference_Z_case_count"],
                       integration_harness_count=len(integration), integration_harness_result="PASS",
                       integration_boundary="empty typed campaign; existing auth/record checks; abstract digest; no model/parser/capture hooks")
        # Detect source changes during the build as well as before it.
        stage = "manifest recheck"
        verify_manifest(ROOT, git_files(ROOT))
        summary["verification_status"] = "PASS"
    except (audit.AuditError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        if stage.startswith("manifest"):
            summary["manifest_verification_result"] = "FAIL"
        summary["failed_stage"] = stage
        summary["error"] = str(error)
        print(f"FAIL: {stage}: {error}", file=sys.stderr)
        return 1
    finally:
        summary["finished_utc"] = datetime.now(timezone.utc).isoformat()
        summary_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"PASS: current release checks; Phase 1 OPEN / NOT YET CLOSED; summary: {summary_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
