#!/usr/bin/env python3
"""Adversarial checks of the release gates using temporary fixtures only."""

from contextlib import redirect_stderr, redirect_stdout
import io
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import audit
import release


class AuditTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        text = '(* Admitted (* Axiom *) Parameter *)\nDefinition s := "admit (* ""Axiom"" *)".\nLemma ok : True. Proof. exact I. Qed.'
        code = audit.source_code(text)
        self.assertEqual(len(text), len(code))
        self.assertEqual(text.count("\n"), code.count("\n"))
        self.assertIsNone(audit.FORBIDDEN.search(code))
        self.assertEqual(audit.THEOREM.findall(code), ["ok"])

    def test_unterminated_comment_and_string(self):
        for text in ('(* unclosed', 'Definition s := "unclosed'):
            with self.subTest(text=text), self.assertRaises(audit.AuditError):
                audit.source_code(text)

    def test_each_forbidden_token(self):
        with tempfile.TemporaryDirectory() as directory:
            impl = Path(directory)
            (impl / "rocq").mkdir()
            (impl / "_CoqProject").write_text("rocq/Fixture.v\n")
            module = impl / "rocq" / "Fixture.v"
            for token in ("Admitted", "admit", "Axiom", "Parameter", "Axioms", "Parameters"):
                module.write_text(f"(* harmless {token} *)\n{token}.\nLemma ok : True. Proof. exact I. Qed.\n")
                data = audit.inventory(impl)
                self.assertEqual(data["forbidden"], [f"rocq/Fixture.v:2: {token}"])
                with self.subTest(token=token), self.assertRaises(audit.AuditError):
                    audit.check_tokens(data)
            module.write_text("(* Admitted (* Axiom *) Parameter admit *)\nLemma ok : True. Proof. exact I. Qed.\n")
            with redirect_stdout(io.StringIO()):
                audit.check_tokens(audit.inventory(impl))

    def test_section_premises_are_separate(self):
        with redirect_stdout(io.StringIO()):
            audit.check_tokens({"forbidden": [], "premise_declarations": [{"kind": "Hypothesis"}]})
        self.assertIsNone(audit.FORBIDDEN.search("Hypothesis h : True. Variable x : nat."))

    def test_assumption_output_contract(self):
        good = "PCFW_BEGIN:M.ok\nClosed under the global context\nPCFW_END:M.ok\n"
        audit.validate_assumptions(subprocess.CompletedProcess([], 0, good, ""), ["M.ok"])
        failures = [
            (0, good, "Error: unresolved name"),  # exit 0 must not mask an error
            (0, good.replace("Closed under the global context", "Axioms:\nM.a : True"), ""),
            (0, "", ""),
            (0, good + good, ""),
            (0, good.replace("PCFW_END:M.ok", "PCFW_END:M.other"), ""),
            (0, good.replace("Closed under the global context", ""), ""),
            (0, good, "Anomaly: unexpected failure"),
            (1, good, ""),
        ]
        for status, stdout, stderr in failures:
            with self.subTest(status=status, stdout=stdout, stderr=stderr), self.assertRaises(audit.AuditError):
                audit.validate_assumptions(subprocess.CompletedProcess([], status, stdout, stderr), ["M.ok"])

    def test_real_coq_closed_missing_and_axiom(self):
        # Real compiler runs, with no changes to project source or theorem statements.
        with tempfile.TemporaryDirectory(prefix="pcfw-negative-") as directory:
            impl = Path(directory)
            (impl / "rocq").mkdir()
            module = impl / "rocq" / "Fixture.v"
            (impl / "_CoqProject").write_text("-Q rocq PCFW\nrocq/Fixture.v\n")
            module.write_text("Lemma ok : True. Proof. exact I. Qed.\n")
            subprocess.run(["coqc", "-Q", "rocq", "PCFW", str(module)], cwd=impl, check=True, capture_output=True)
            with redirect_stdout(io.StringIO()):
                audit.check_assumptions(audit.inventory(impl), impl)
            (impl / "rocq" / "PrintFixtureAssumptions.v").write_text("From PCFW Require Import Fixture.\nPrint Assumptions Missing.\n")
            with self.assertRaises(audit.AuditError):
                audit.check_assumptions(audit.inventory(impl), impl)
            (impl / "rocq" / "PrintFixtureAssumptions.v").unlink()
            module.write_text("Axiom a : True. Lemma ok : True. Proof. exact a. Qed.\n")
            subprocess.run(["coqc", "-Q", "rocq", "PCFW", str(module)], cwd=impl, check=True, capture_output=True)
            data = audit.inventory(impl)
            with self.assertRaises(audit.AuditError):
                audit.check_tokens(data)
            with self.assertRaises(audit.AuditError):
                audit.check_assumptions(data, impl)
            module.write_text("Lemma ok : True. Proof. exact I. Qed.\n")
            subprocess.run(["coqc", "-Q", "rocq", "PCFW", str(module)], cwd=impl, check=True, capture_output=True)
            with redirect_stdout(io.StringIO()):
                audit.check_tokens(audit.inventory(impl))
                audit.check_assumptions(audit.inventory(impl), impl)

    def test_unbuilt_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            impl = Path(directory)
            (impl / "rocq").mkdir()
            (impl / "_CoqProject").write_text("rocq/Fixture.v\n")
            (impl / "rocq" / "Fixture.v").write_text("Lemma ok : True. Proof. exact I. Qed.")
            (impl / "rocq" / "Unbuilt.v").write_text("Lemma other : True. Proof. exact I. Qed.")
            with self.assertRaises(audit.AuditError):
                audit.inventory(impl)


class ReleaseTests(unittest.TestCase):
    def test_manifest_tamper_coverage_and_restore(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.txt"
            source.write_text("original\n")
            manifest = root / "MANIFEST.sha256"
            entry = hashlib.sha256(source.read_bytes()).hexdigest() + "  source.txt\n"
            manifest.write_text(entry)
            self.assertEqual(release.verify_manifest(root, {"source.txt"}), 1)
            source.write_text("harmless corruption\n")
            with self.assertRaises(audit.AuditError):
                release.verify_manifest(root, {"source.txt"})
            source.write_text("original\n")
            for contents, files in [("", {"source.txt"}), (entry + entry, {"source.txt"}),
                                    (entry, {"source.txt", "unlisted.txt"}),
                                    (entry, set()), ("bad manifest\n", {"source.txt"}),
                                    ("0" * 64 + "  ../escape.txt\n", {"../escape.txt"})]:
                manifest.write_text(contents)
                with self.subTest(contents=contents, files=files), self.assertRaises(audit.AuditError):
                    release.verify_manifest(root, files)
            manifest.write_text(entry)
            self.assertEqual(release.verify_manifest(root, {"source.txt"}), 1)

    def test_build_plan_coverage(self):
        data = audit.inventory()
        self.assertEqual(len(release.check_plan(data)), len(list((audit.IMPL / "ocaml").glob("test_*.ml"))))
        with tempfile.TemporaryDirectory() as directory:
            impl = Path(directory)
            (impl / "ocaml").mkdir()
            for source in (audit.IMPL / "ocaml").glob("test_*.ml"):
                (impl / "ocaml" / source.name).touch()
            original = (audit.IMPL / "Makefile").read_text()
            for broken in (original.replace("\t./ocaml/test_stage1\n", ""),
                           original.replace("PCFW.ManifestPipeline\n", "\n"),
                           original.replace("\tcoqc -Q rocq PCFW rocq/Stage1.v\n", "")):
                (impl / "Makefile").write_text(broken)
                with self.subTest(broken=broken), self.assertRaises(audit.AuditError):
                    release.check_plan(data, impl)

    def test_check_evidence_missing_required_steps(self):
        data = {"compiled_modules": ["M", "ExtractM"], "release_set": ["M.ok"]}
        lines = ["coqc -Q rocq PCFW rocq/M.v", "coqc -Q rocq PCFW rocq/ExtractM.v",
                 "Modules were successfully checked", "PASS: 1 release declarations inspected; no global axioms",
                 "PASS: project source token audit; 0 section-premise declarations inventoried separately",
                 "./ocaml/test_fixture"]
        release.validate_check_log("\n".join(lines) + "\n", data, ["test_fixture"])
        for i in range(len(lines)):
            with self.subTest(removed=lines[i]), self.assertRaises(audit.AuditError):
                release.validate_check_log("\n".join(lines[:i] + lines[i + 1:]) + "\n", data, ["test_fixture"])

    def test_real_make_failure_stops_even_with_inherited_ignore_flags(self):
        with tempfile.TemporaryDirectory() as directory:
            impl = Path(directory)
            (impl / "Makefile").write_text("check:\n\tfalse\n\ttouch must_not_run\n")
            with patch.object(audit, "IMPL", impl), patch.dict("os.environ", {"MAKEFLAGS": "-i -k"}):
                with self.assertRaises(audit.AuditError):
                    release.run_make("check", impl / "check.log")
            self.assertFalse((impl / "must_not_run").exists())
            (impl / "Makefile").write_text("check:\n\ttrue\n")
            with patch.object(audit, "IMPL", impl):
                release.run_make("check", impl / "check.log")

    def test_failed_release_replaces_stale_passing_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            (output / "summary.json").write_text('{"verification_status":"PASS"}')
            with patch.object(release, "OUTPUT", output), patch.object(release, "verify_manifest", side_effect=audit.AuditError("simulated manifest failure")):
                with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                    self.assertEqual(release.main(), 1)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["verification_status"], "FAILED")
            self.assertEqual(summary["release_status"], "OPEN / NOT YET CLOSED")
            self.assertEqual(summary["failed_stage"], "manifest")


if __name__ == "__main__":
    unittest.main(verbosity=2)
