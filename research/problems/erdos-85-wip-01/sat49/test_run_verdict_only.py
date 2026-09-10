"""Failure-path tests use fake executables, never real SAT solvers."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import signal
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location("verdict", Path(__file__).with_name("run_verdict_only.py"))
v = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(v)


class VerdictTests(unittest.TestCase):
    def setUp(self):
        v.ABORT.clear()
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.cnf = self.root / "tiny.cnf"
        self.cnf.write_text("p cnf 1 2\n1 0\n-1 0\n")

    def solver(self, name, body):
        path = self.root / name
        path.write_text(f"#!{sys.executable}\nimport sys,time,os\n" + body + "\n")
        path.chmod(0o755)
        return path

    def case(self):
        return {"id": "test-1", "sector": "H3", "cnf": "tiny.cnf",
                "resolved_cnf": str(self.cnf), "cnf_sha256": v.sha256(self.cnf),
                "generator_commit": "a" * 40, "crosscheck": True,
                "primary_cap_seconds": 2, "crosscheck_cap_seconds": 2}

    def test_verdict_requires_matching_exit_and_unique_status(self):
        for code, text, expected in [
            (20, b"s UNSATISFIABLE\n", "UNSAT"),
            (10, b"s SATISFIABLE\nv 1 0\n", "SAT_CANDIDATE"),
            (0, b"s UNKNOWN\n", "UNKNOWN"),
            (0, b"s UNSATISFIABLE\n", "ERROR"),
            (20, b"", "ERROR"),
            (20, b"s SATISFIABLE\ns UNSATISFIABLE\n", "ERROR"),
            (139, b"s UNSATISFIABLE\n", "ERROR"),
        ]:
            self.assertEqual(v.classify(code, text, None), expected)
        self.assertEqual(v.classify(20, b"s UNSATISFIABLE\n", "wall_time_limit"), "UNKNOWN")

    def test_crosscheck_receipt_and_no_proof_argument(self):
        body = "assert sys.argv[-1].endswith('.cnf') and len(sys.argv) in (3,4)\nprint('s UNSATISFIABLE')\nsys.exit(20)"
        primary, secondary = self.solver("primary", body), self.solver("secondary", body)
        result = v.run_case(self.case(), self.root, primary, secondary)
        self.assertEqual(result["status"], "UNSAT_CROSSCHECKED")
        self.assertFalse(result["primary"]["proof_requested"])
        self.assertEqual(result["primary"]["command"][1], "--time=2")
        self.assertEqual(result["crosscheck"]["command"][1:3], ["-t", "2"])
        self.assertTrue((self.root / "test-1" / "result.json").is_file())

    def test_crosscheck_unknown_does_not_become_unsat(self):
        primary = self.solver("primary", "print('s UNSATISFIABLE');sys.exit(20)")
        secondary = self.solver("secondary", "print('s UNKNOWN');sys.exit(0)")
        result = v.run_case(self.case(), self.root, primary, secondary)
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(result["primary"]["verdict"], "UNSAT")

    def test_solver_disagreement_is_preserved(self):
        primary = self.solver("primary", "print('s UNSATISFIABLE');sys.exit(20)")
        secondary = self.solver("secondary", "print('s SATISFIABLE');sys.exit(10)")
        self.assertEqual(v.run_case(self.case(), self.root, primary, secondary)["status"], "DISAGREEMENT")

    def test_hash_mismatch_prevents_process_start(self):
        case = self.case()
        case["cnf_sha256"] = "0" * 64
        with mock.patch.object(v, "run_solver") as run:
            result = v.run_case(case, self.root, self.cnf, self.cnf)
        run.assert_not_called()
        self.assertEqual(result["status"], "ERROR")

    def test_input_mutation_prevents_crosscheck_and_unsat(self):
        primary = self.solver("primary", "open(sys.argv[-1],'a').write('c changed\\n')\nprint('s UNSATISFIABLE');sys.exit(20)")
        secondary = self.solver("secondary", "raise AssertionError('must not run')")
        result = v.run_case(self.case(), self.root, primary, secondary)
        self.assertEqual(result["status"], "ERROR")
        self.assertNotIn("crosscheck", result)

    def test_timeout_even_after_unsat_line_is_unknown(self):
        solver = self.solver("slow", "print('s UNSATISFIABLE',flush=True);time.sleep(30)")
        result = v.run_solver(solver, self.cnf, 0.1, self.root / "slow.log")
        self.assertEqual(result["verdict"], "UNKNOWN")
        self.assertEqual(result["stop_reason"], "wall_time_limit")
        self.assertLess(result["elapsed_seconds"], 5)

    def test_sigterm_cancels_live_process_and_restores_handler(self):
        solver = self.solver("slow", "print('started',flush=True);time.sleep(30)")
        previous = signal.getsignal(signal.SIGTERM)
        timer = threading.Timer(0.1, lambda: __import__('os').kill(__import__('os').getpid(), signal.SIGTERM))
        with v.cancellation_handlers():
            timer.start()
            result = v.run_solver(solver, self.cnf, 10, self.root / "cancel.log")
            timer.join()
        self.assertEqual(signal.getsignal(signal.SIGTERM), previous)
        self.assertEqual(result["stop_reason"], "aborted")
        self.assertEqual(result["verdict"], "UNKNOWN")
        self.assertLess(result["elapsed_seconds"], 5)

    def test_log_limit_is_bounded_and_unknown(self):
        solver = self.solver("loud", "print('s UNSATISFIABLE');print('x'*10000);sys.exit(20)")
        with mock.patch.object(v, "LOG_LIMIT", 100):
            result = v.run_solver(solver, self.cnf, 2, self.root / "loud.log")
        self.assertEqual(result["verdict"], "UNKNOWN")
        self.assertEqual(result["log_bytes"], 100)

    def test_dry_run_never_invokes_solver_and_duplicates_fail(self):
        case = self.case()
        manifest = self.root / "inventory.json"
        data = {"schema": "erdos85-verdict-v1", "not_before": "2099-01-01T00:00:00Z", "cases": [case]}
        manifest.write_text(json.dumps(data))
        completed = subprocess.run([sys.executable, str(Path(v.__file__)), "--inventory", str(manifest),
                                    "--kissat", "/does/not/exist", "--cadical", "/does/not/exist"],
                                   capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(json.loads(completed.stdout)["mode"], "dry_run")
        data["cases"].append(case)
        manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            v.load_inventory(manifest)

    def test_committed_inventory_must_match(self):
        manifest = self.root / "inventory.json"
        manifest.write_text("original")
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "inventory.json"], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "-c", "core.hooksPath=/dev/null", "commit", "-qm", "inventory"], check=True)
        commit = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip()
        with self.assertRaises(subprocess.CalledProcessError):
            v.require_banked_inventory(manifest, commit)
        subprocess.run(["git", "-C", str(self.root), "update-ref",
                        "refs/remotes/origin/erdos85/integration", commit], check=True)
        v.require_banked_inventory(manifest, commit)
        manifest.write_text("changed")
        with self.assertRaisesRegex(ValueError, "differs"):
            v.require_banked_inventory(manifest, commit)

    def test_selected_pilot_cannot_claim_entire_inventory(self):
        first = self.case()
        second = dict(first, id="test-2")
        manifest = self.root / "inventory.json"
        manifest.write_text(json.dumps({"schema": "erdos85-verdict-v1",
                                       "not_before": "2000-01-01T00:00:00Z",
                                       "cases": [first, second]}))
        solver = self.solver("solver", "print('s UNSATISFIABLE');sys.exit(20)")
        output = self.root / "pilot"
        argv = ["runner", "--inventory", str(manifest), "--inventory-commit", "a" * 40,
                "--execute", "--case-id", "test-1", "--output-dir", str(output),
                "--kissat", str(solver), "--cadical", str(solver)]
        with mock.patch.object(sys, "argv", argv), \
                mock.patch.object(v, "require_banked_inventory"), \
                mock.patch.object(v, "solver_identity", return_value={"version": "fake"}), \
                mock.patch.object(v.shutil, "disk_usage", return_value=mock.Mock(free=20 * 1024**3)):
            self.assertEqual(v.main(), 0)
        result = json.loads((output / "results.json").read_text())
        self.assertTrue(result["selected_all_unsat"])
        self.assertFalse(result["inventory_all_unsat"])
        self.assertEqual(result["inventory_cases"], 2)
        self.assertFalse((output / "test-2").exists())

    def test_inventory_restored_after_parse_cannot_dispatch_unbanked_case(self):
        manifest = self.root / "inventory.json"
        row = self.case()
        data = {"schema": "erdos85-verdict-v1", "not_before": "2000-01-01T00:00:00Z", "cases": [row]}
        banked = json.dumps(data).encode()
        manifest.write_bytes(banked)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        subprocess.run(["git", "-C", str(self.root), "add", "inventory.json"], check=True)
        subprocess.run(["git", "-C", str(self.root), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "-c", "core.hooksPath=/dev/null", "commit", "-qm", "banked fixture"], check=True)
        commit = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip()
        subprocess.run(["git", "-C", str(self.root), "update-ref", "refs/remotes/origin/erdos85/integration", commit], check=True)
        row["id"] = "unbanked-case"
        manifest.write_text(json.dumps(data))
        check = v.require_banked_inventory

        def restore_then_check(path, revision, **kwargs):
            manifest.write_bytes(banked)
            check(path, revision, **kwargs)

        output = self.root / "race-output"
        argv = ["runner", "--inventory", str(manifest), "--inventory-commit", commit,
                "--execute", "--output-dir", str(output)]
        with mock.patch.object(sys, "argv", argv), \
                mock.patch.object(v, "require_banked_inventory", side_effect=restore_then_check), \
                mock.patch.object(v, "run_case") as run, \
                self.assertRaisesRegex(ValueError, "committed bytes"):
            v.main()
        run.assert_not_called()
        self.assertFalse(output.exists())

    def test_completed_error_stops_refill_even_after_completed_unsat(self):
        cases = [dict(self.case(), id=name) for name in ("1-good", "2-error", "3-not-started")]
        manifest = self.root / "inventory.json"
        manifest.write_text(json.dumps({"schema": "erdos85-verdict-v1",
                                       "not_before": "2000-01-01T00:00:00Z", "cases": cases}))
        started = []

        def fake_run(case, *_args):
            started.append(case["id"])
            return {"id": case["id"], "status": "ERROR" if case["id"] == "2-error" else "UNSAT_CROSSCHECKED"}

        original_wait = v.concurrent.futures.wait

        def wait_for_batch(fs, **_kwargs):
            done, pending = original_wait(fs, return_when=v.concurrent.futures.ALL_COMPLETED)
            return sorted(done, key=lambda f: f.result()["id"]), pending

        output = self.root / "batch-output"
        argv = ["runner", "--inventory", str(manifest), "--inventory-commit", "a" * 40,
                "--execute", "--workers", "2", "--output-dir", str(output)]
        with mock.patch.object(sys, "argv", argv), \
                mock.patch.object(v, "require_banked_inventory"), \
                mock.patch.object(v, "solver_identity", return_value={"version": "fake"}), \
                mock.patch.object(v, "run_case", side_effect=fake_run), \
                mock.patch.object(v.concurrent.futures, "wait", side_effect=wait_for_batch), \
                mock.patch.object(v.shutil, "disk_usage", return_value=mock.Mock(free=20 * 1024**3)):
            self.assertEqual(v.main(), 1)
        self.assertEqual(set(started), {"1-good", "2-error"})
        result = json.loads((output / "results.json").read_text())
        self.assertEqual(result["not_started"], ["3-not-started"])
        self.assertFalse(result["inventory_all_unsat"])


if __name__ == "__main__":
    unittest.main()
