"""Metadata-only reproductions against the pinned collector source; no solver calls."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

COMMIT = "1cab73ef2a2780161d98ac389068acbb54b9002b"
PREFIX = "research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/"
CAKE = "4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b"


def main():
    with tempfile.TemporaryDirectory(prefix="e85-h7-collector-review-") as tmp:
        root = Path(tmp)
        for name in ["collect_receipts.py", "h7_common.py"]:
            (root / name).write_bytes(subprocess.check_output(
                ["git", "show", COMMIT + ":" + PREFIX + name]))
        spec = importlib.util.spec_from_file_location("review_collector", root / "collect_receipts.py")
        collector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(collector)
        inputs, results = root / "inputs", root / "results"
        inputs.mkdir()
        results.mkdir()
        (inputs / "inputs.json").write_text("{}\n")
        argv = ["collect_receipts.py", "--inputs", str(inputs), "--results", str(results)]
        report = {"reviewed_commit": COMMIT}
        with patch.object(sys, "argv", argv + ["--cubes", "cube_TYPO"]), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            rc = collector.main()
        report["unknown_cube_selector"] = {"exit_code": rc, "summary": json.loads(output.getvalue())}
        assert rc == 0 and report["unknown_cube_selector"]["summary"]["all_complete"] is True
        (results / "fixture.jsonl.zst").write_bytes(b"fixture")

        class Cube:
            def __init__(self, *args):
                self.meta = {"cover_cnf_sha256": "a" * 64}
                self.n_leaves = 1

            def leaf_sha256(self, leaf):
                assert leaf == 0
                return "b" * 64

        for label, cake in [("approved_checker_control", CAKE), ("unapproved_checker_fixture", "0" * 64)]:
            rows = []
            for kind, leaf, sha in [("cover", None, "a" * 64), ("leaf", 0, "b" * 64)]:
                rows.append({"cube": "cube_fixture", "kind": kind, "leaf": leaf,
                    "status": "CERTIFIED", "cnf_sha256": sha,
                    "binaries": {"cadical": collector.CADICAL, "cake_lpr": cake},
                    "checker": {"verified_line": True, "cpu_seconds": 1},
                    "solver": {"returncode": 20, "cpu_seconds": 1},
                    "proof": {"checker_closed_early": False, "bytes": 1, "sha256": "c" * 64}})
            decoded = "".join(json.dumps(row) + "\n" for row in rows).encode()
            with patch.object(collector.hc, "CUBES", ["cube_fixture"]), \
                    patch.object(collector.hc, "Cube", Cube), \
                    patch.object(collector.subprocess, "run", return_value=
                                 subprocess.CompletedProcess([], 0, stdout=decoded)), \
                    patch.object(sys, "argv", argv), \
                    contextlib.redirect_stdout(io.StringIO()) as output:
                rc = collector.main()
            report[label] = {"exit_code": rc, "summary": json.loads(output.getvalue())}
            assert rc == 0 and report[label]["summary"]["all_complete"] is True
        report["scope"] = ("Metadata-only reproduction of old collector behavior. "
            "Checker fixtures stub only Cube and decompression; the selector case uses neither stub. "
            "No solver, Lean, real CNF, network operation, or cloud mutation.")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
