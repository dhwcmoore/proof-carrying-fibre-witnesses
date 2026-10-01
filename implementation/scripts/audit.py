#!/usr/bin/env python3
"""Fail-closed checks for the project-owned Rocq release surface."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


IMPL = Path(__file__).resolve().parents[1]
THEOREM = re.compile(r"\b(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example)\s+(\w+)")
FORBIDDEN = re.compile(r"\b(?:Admitted|admit|Axiom|Parameter|Axioms|Parameters)\b")


class AuditError(RuntimeError):
    pass


def source_code(text):
    """Blank nested comments and Coq strings, preserving offsets and lines.

    Coq strings escape quotes by doubling them. Comment delimiters inside a
    string are ordinary characters; quotes inside comments have no effect.
    Unterminated input fails rather than hiding the remaining source.
    """
    out = list(text)
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text[i:i + 2] == "(*":
                depth += 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if text[i:i + 2] == "*)":
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
                continue
        elif quoted:
            if text[i:i + 2] == '""':
                out[i:i + 2] = "  "
                i += 2
                continue
            if text[i] == '"':
                quoted = False
        elif text[i:i + 2] == "(*":
            depth = 1
            out[i:i + 2] = "  "
            i += 2
            continue
        elif text[i] == '"':
            quoted = True
        else:
            i += 1
            continue
        if text[i] != "\n":
            out[i] = " "
        i += 1
    if depth or quoted:
        raise AuditError("unterminated comment or string")
    return "".join(out)


def inventory(impl=IMPL):
    project = (impl / "_CoqProject").read_text()
    files = re.findall(r"^rocq/(\w+\.v)$", project, re.M)
    if not files or len(files) != len(set(files)):
        raise AuditError("empty or duplicate _CoqProject module inventory")
    actual = {str(p.relative_to(impl / "rocq")) for p in (impl / "rocq").rglob("*.v")}
    scripts = {p.name for p in (impl / "rocq").glob("Print*Assumptions.v")}
    if actual != set(files) | scripts:
        raise AuditError(f"unclassified/missing project source: {sorted(actual ^ (set(files) | scripts))}")
    substantive = [Path(f).stem for f in files if not f.startswith("Extract")]
    extracted = [Path(f).stem for f in files if f.startswith("Extract")]
    declarations = []
    premises = []
    forbidden = []
    requested = []
    for name in sorted(actual):
        code = source_code((impl / "rocq" / name).read_text())
        for match in FORBIDDEN.finditer(code):
            forbidden.append(f"rocq/{name}:{code[:match.start()].count(chr(10)) + 1}: {match[0]}")
        for match in re.finditer(r"\b(Hypotheses|Hypothesis|Variables|Variable)\s+(\w+)", code):
            premises.append({"module": Path(name).stem, "kind": match[1],
                             "first_name": match[2], "line": code[:match.start()].count("\n") + 1})
        found = [f"{Path(name).stem}.{m[1]}" for m in THEOREM.finditer(code)]
        if Path(name).stem in substantive:
            declarations.extend(found)
        elif found:
            raise AuditError(f"theorem-like declaration outside substantive release modules: {name}")
        if name in scripts:
            imports = re.findall(r"From PCFW Require Import ([\w\s]+)\.", code)
            imported = " ".join(imports).split()
            for symbol in re.findall(r"Print Assumptions ([\w.]+)\.", code):
                if "." not in symbol:
                    if len(imported) != 1:
                        raise AuditError(f"ambiguous legacy request: {name}: {symbol}")
                    symbol = f"{imported[0]}.{symbol}"
                requested.append(symbol)
    if not declarations or len(declarations) != len(set(declarations)):
        raise AuditError("empty or duplicate theorem release inventory")
    # Legacy requests remain checked even if their target disappears from source.
    release_set = sorted(set(declarations) | set(requested))
    return {"compiled_modules": [Path(f).stem for f in files],
            "substantive_modules": substantive, "extraction_modules": extracted,
            "theorem_declarations": declarations, "legacy_requests": requested,
            "release_set": release_set, "premise_declarations": premises,
            "forbidden": forbidden}


def check_tokens(data):
    if data["forbidden"]:
        raise AuditError("forbidden Rocq source tokens:\n" + "\n".join(data["forbidden"]))
    print(f"PASS: project source token audit; {len(data['premise_declarations'])} section-premise declarations inventoried separately")


def audit_program(data):
    lines = ["From Coq Require Import String.",
             "From PCFW Require Import " + " ".join(data["substantive_modules"]) + "."]
    for symbol in data["release_set"]:
        lines.extend([f'Goal True. idtac "PCFW_BEGIN:{symbol}". Abort.',
                      f"Print Assumptions {symbol}.",
                      f'Goal True. idtac "PCFW_END:{symbol}". Abort.'])
    return "\n".join(lines) + "\n"


def validate_assumptions(result, symbols):
    output = result.stdout + "\n" + result.stderr
    if result.returncode != 0:
        raise AuditError(f"assumption inspection process failed ({result.returncode}):\n{output}")
    if re.search(r"\b(?:Error|Anomaly|Axioms|Assumptions)\s*:", output, re.I):
        raise AuditError("Coq error or unexpected assumptions:\n" + output)
    marker_lines = re.findall(r"^PCFW_(?:BEGIN|END):.*$", output, re.M)
    expected = [marker for s in symbols for marker in (f"PCFW_BEGIN:{s}", f"PCFW_END:{s}")]
    if marker_lines != expected:
        raise AuditError("missing, duplicated or reordered theorem inspection markers:\n" + output)
    for symbol in symbols:
        begin = f"PCFW_BEGIN:{symbol}\n"
        end = f"PCFW_END:{symbol}\n"
        block = output.split(begin, 1)[1].split(end, 1)[0]
        if block.strip() != "Closed under the global context":
            raise AuditError(f"unexpected assumption inspection for {symbol}:\n{block}")
    if output.count("Closed under the global context") != len(symbols):
        raise AuditError("assumption result count does not match requested release set")


def check_assumptions(data, impl=IMPL, log=None):
    with tempfile.TemporaryDirectory(prefix="pcfw-assumptions-") as directory:
        program = Path(directory) / "ReleaseAssumptions.v"
        program.write_text(audit_program(data))
        result = subprocess.run(["coqc", "-Q", "rocq", "PCFW", str(program)],
                                cwd=impl, text=True, capture_output=True)
    if log:
        Path(log).write_text(result.stdout + "\n" + result.stderr)
    validate_assumptions(result, data["release_set"])
    # Preserve inspection evidence and compiler warnings in the build log.
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    print(f"PASS: {len(data['release_set'])} release declarations inspected; no global axioms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["tokens", "assumptions", "inventory"])
    parser.add_argument("--log", type=Path)
    args = parser.parse_args()
    try:
        data = inventory()
        if args.mode == "tokens":
            check_tokens(data)
        elif args.mode == "assumptions":
            check_assumptions(data, log=args.log)
        else:
            print(json.dumps(data, indent=2))
    except (AuditError, OSError) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    main()
