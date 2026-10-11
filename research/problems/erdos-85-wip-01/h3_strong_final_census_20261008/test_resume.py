"""Small metadata-only regression checks; never invoke Lean or cloud jobs."""

import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("resume", Path(__file__).with_name("resume.py"))
resume = importlib.util.module_from_spec(spec)
spec.loader.exec_module(resume)


class PrefixChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.research = self.root / "research"
        self.research.mkdir()
        self.output = self.root / "output"
        self.output.mkdir()
        self.addCleanup(patch.stopall)
        patch.object(resume, "RESEARCH", self.research).start()
        self.sources = []
        for name in ["A", "B"]:
            source = self.research / (name + ".lean")
            source.write_text("#print axioms " + name + ".result\n")
            self.sources.append((name, source))
        self.library = ["Proofs.Dependency"]
        (self.output / "dependencies.log").write_text("Build completed successfully.\n")
        shutil.copyfile(self.sources[0][1], self.output / "A.lean")
        (self.output / "A.log").write_text("'A.result' depends on axioms: [propext, Quot.sound]\n")
        (self.output / "A.olean").write_bytes(b"synthetic object, never loaded into Lean")
        self.entry = {
            "module": "A", "status": "PASS", "exit_code": 0, "source": "A.lean",
            "source_sha256": resume.digest(self.output / "A.lean"),
            "log_sha256": resume.digest(self.output / "A.log"),
            "olean_sha256": resume.digest(self.output / "A.olean"),
            "command": ["lean", "-R", str(self.output), "-o",
                        str(self.output / "A.olean"), str(self.output / "A.lean")],
            "axiom_exports": [{"theorem": "A.result", "axioms": ["propext", "Quot.sound"]}],
        }
        self.receipt = {
            "status": "RUNNING", "lean_threads": 1,
            "inputs": {n: {"source": str(p.relative_to(self.research)), "sha256": resume.digest(p)}
                       for n, p in self.sources},
            "dependency_build": {"command": ["lake", "build", *self.library], "exit_code": 0,
                                 "log_sha256": resume.digest(self.output / "dependencies.log")},
            "results": [self.entry],
        }
        self.save()

    def save(self):
        (self.output / "RUN.json").write_text(json.dumps(self.receipt))
        (self.output / "A.run.json").write_text(json.dumps(self.entry))

    def validate(self):
        return resume.validate_prefix(self.output, self.sources, self.library)

    def test_valid_prefix_and_snapshot(self):
        _, prefix, digest = self.validate()
        self.assertEqual(prefix, [self.entry])
        snapshot = self.root / "snapshot"
        shutil.copytree(self.output, snapshot)
        _, copied, copied_digest = resume.validate_prefix(
            snapshot, self.sources, self.library, self.output)
        self.assertEqual((copied, copied_digest), (prefix, digest))
        with self.assertRaisesRegex(ValueError, "Wrong command"):
            resume.validate_prefix(snapshot, self.sources, self.library)

    def test_changed_artifacts(self):
        for suffix in ["lean", "log", "olean", "run.json"]:
            with self.subTest(suffix=suffix):
                path = self.output / ("A." + suffix)
                original = path.read_bytes()
                path.write_text("{}" if suffix == "run.json" else "changed")
                with self.assertRaises(ValueError):
                    self.validate()
                path.write_bytes(original)

    def test_changed_planned_source(self):
        self.sources[1][1].write_text("changed uncompiled source")
        with self.assertRaisesRegex(ValueError, "inventory changed"):
            self.validate()

    def test_changed_dependency_log(self):
        (self.output / "dependencies.log").write_text("changed")
        with self.assertRaisesRegex(ValueError, "Dependency evidence"):
            self.validate()

    def test_wrong_order_and_extra_result(self):
        self.receipt["results"] = [dict(self.entry, module="B")]
        self.save()
        with self.assertRaisesRegex(ValueError, "exact dependency prefix"):
            self.validate()
        self.receipt["results"] = [self.entry] * 3
        self.save()
        with self.assertRaisesRegex(ValueError, "Too many"):
            self.validate()

    def test_report_missing_or_nonstandard_even_with_matching_hash(self):
        for log, reports in [
            ("", []),
            ("'A.result' depends on axioms: [newAxiom]\n",
             [{"theorem": "A.result", "axioms": ["newAxiom"]}]),
            ("'Other.result' depends on axioms: [propext]\n",
             [{"theorem": "Other.result", "axioms": ["propext"]}]),
        ]:
            with self.subTest(log=log):
                (self.output / "A.log").write_text(log)
                self.entry.update(log_sha256=resume.digest(self.output / "A.log"),
                                  axiom_exports=reports)
                self.save()
                with self.assertRaises(ValueError):
                    self.validate()

    def test_nonzero_success_refused(self):
        self.entry["exit_code"] = 1
        self.save()
        with self.assertRaisesRegex(ValueError, "Nonzero prefix exit"):
            self.validate()

    def test_terminal_failure_is_not_reused(self):
        self.receipt["status"] = "MODULE_FAILURE"
        self.receipt["results"].append({"module": "B", "status": "FAIL"})
        self.save()
        self.assertEqual(self.validate()[1], [self.entry])
        self.entry["status"] = "FAIL"
        self.save()
        with self.assertRaisesRegex(ValueError, "Failure is not the final"):
            self.validate()

    def test_successful_receipt_is_not_resumed(self):
        self.receipt["status"] = "PASS"
        self.save()
        with self.assertRaisesRegex(ValueError, "interrupted or failed"):
            self.validate()


class TerminalChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.job = "20261008T010203-erdos85__h3-census-20261008-123"
        self.directory = self.root / "jobs" / self.job
        self.directory.mkdir(parents=True)
        self.output = self.root / "repository/research/result"
        self.output.mkdir(parents=True)
        (self.output / "RUN.json").write_text('{"status":"RUNNING"}')
        (self.directory / "exit").write_text("124\n")
        (self.directory / "pid").write_text("999999999\n")
        (self.directory / "log").write_text(
            "[e85] commit " + "a" * 40 + " (test)\n"
            "Command: lake env python3 ../research/problems/erdos-85-wip-01/"
            "h3_strong_final_census_20261008/check.py --output ../research/result\n")
        self.record = self.root / "terminal.json"
        self.addCleanup(patch.stopall)
        patch.object(resume, "JOBS", self.root / "jobs").start()
        patch.object(resume, "HOST_REPOSITORY", self.root / "repository").start()
        patch.object(resume.checker, "plan", return_value=([], [], ["Proofs.A"])).start()
        patch.object(resume, "library_unchanged", return_value=1).start()
        patch.object(resume, "library_hashes", return_value={"proofs/Proofs/A.lean": "f" * 64}).start()
        original_exists = Path.exists
        def exists(path):
            return False if str(path) == "/.dockerenv" else original_exists(path)
        patch.object(Path, "exists", exists).start()

    def capture(self):
        resume.capture_terminal(self.job, self.output, self.record)

    def test_terminal_record_and_no_overwrite(self):
        self.capture()
        record = json.loads(self.record.read_text())
        self.assertEqual(record["recorded_output"], "/workspace/research/result")
        self.assertEqual(record["build_receipt_sha256"], resume.digest(self.output / "RUN.json"))
        self.assertEqual(record["library_source_sha256"], {"proofs/Proofs/A.lean": "f" * 64})
        with self.assertRaises(FileExistsError):
            self.capture()

    def test_no_exit_refused(self):
        (self.directory / "exit").unlink()
        with self.assertRaisesRegex(ValueError, "no authoritative terminal"):
            self.capture()
        self.assertFalse(self.record.exists())

    def test_success_refused(self):
        (self.directory / "exit").write_text("0")
        with self.assertRaisesRegex(ValueError, "successful job"):
            self.capture()

    def test_live_process_refused(self):
        original_exists = Path.exists
        with patch.object(Path, "exists", lambda p: str(p) == "/proc/999999999" or original_exists(p)):
            with self.assertRaisesRegex(ValueError, "still present"):
                self.capture()

    def test_wrong_output_refused(self):
        wrong = self.root / "another-output"
        wrong.mkdir()
        with self.assertRaisesRegex(ValueError, "does not match"):
            resume.capture_terminal(self.job, wrong, self.record)


class LibraryChecks(unittest.TestCase):
    def test_container_hash_check_needs_no_git(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "proofs/Proofs").mkdir(parents=True)
            a, b = root / "proofs/Proofs/A.lean", root / "proofs/Proofs/B.lean"
            a.write_text("import Proofs.B\n")
            b.write_text("import Std\n")
            with patch.object(resume, "REPOSITORY", root), patch.object(
                    resume.subprocess, "check_output", side_effect=AssertionError("No Git in Docker")):
                terminal = {"library_source_sha256": resume.library_hashes(["Proofs.A"])}
                self.assertEqual(resume.verify_library_sources(terminal, ["Proofs.A"]), 6)
                b.write_text("import Std\n-- changed dependency\n")
                with self.assertRaisesRegex(ValueError, "source hashes differ"):
                    resume.verify_library_sources(terminal, ["Proofs.A"])

    def test_new_configuration_and_missing_inventory_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "proofs/Proofs").mkdir(parents=True)
            (root / "proofs/Proofs/A.lean").write_text("import Std\n")
            with patch.object(resume, "REPOSITORY", root):
                terminal = {"library_source_sha256": resume.library_hashes(["Proofs.A"])}
                with self.assertRaisesRegex(ValueError, "source hashes differ"):
                    resume.verify_library_sources({}, ["Proofs.A"])
                (root / "proofs/lakefile.toml").write_text('name = "different"\n')
                with self.assertRaisesRegex(ValueError, "source hashes differ"):
                    resume.verify_library_sources(terminal, ["Proofs.A"])

    def test_transitive_library_and_toml_changes_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "proofs/Proofs").mkdir(parents=True)
            (root / "proofs/Proofs/A.lean").write_text("import Proofs.B\n")
            (root / "proofs/Proofs/B.lean").write_text("import Std\n")
            with patch.object(resume, "REPOSITORY", root):
                for changed in ["proofs/Proofs/B.lean\n", "proofs/lakefile.toml\n"]:
                    with self.subTest(changed=changed), patch.object(
                            resume.subprocess, "check_output", return_value=changed):
                        with self.assertRaisesRegex(ValueError, "inputs changed"):
                            resume.library_unchanged("a" * 40, ["Proofs.A"])
                with patch.object(resume.subprocess, "check_output",
                                  return_value="proofs/Proofs/Unrelated.lean\n"):
                    self.assertEqual(resume.library_unchanged("a" * 40, ["Proofs.A"]), 6)


if __name__ == "__main__":
    unittest.main()
