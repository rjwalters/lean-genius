"""Apply the proposed patch only in a temporary tree and test receipt acceptance."""

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
COMMIT = "1cab73ef2a2780161d98ac389068acbb54b9002b"
PREFIX = "research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/"
CAKE = "4d47ffdd19fc6a80e24025f8c5d27d89c4309c9931bdad6d389d87e35be5464b"


def main():
    results = {}
    with tempfile.TemporaryDirectory(prefix="e85-h7-collector-patch-") as tmp:
        root = Path(tmp)
        package = root / PREFIX
        package.mkdir(parents=True)
        for name in ["collect_receipts.py", "h7_common.py"]:
            (package / name).write_bytes(subprocess.check_output(
                ["git", "show", COMMIT + ":" + PREFIX + name]))
        proposed = HERE / "proposed-collector.patch"
        for flags in [["--check"], []]:
            subprocess.run(["git", "apply", *flags, str(proposed)], cwd=root, check=True)
        spec = importlib.util.spec_from_file_location("patched_collector", package / "collect_receipts.py")
        collector = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(collector)
        inputs, receipts = root / "inputs", root / "results"
        inputs.mkdir()
        receipts.mkdir()
        (inputs / "inputs.json").write_text("{}\n")
        (receipts / "fixture.jsonl.zst").write_bytes(b"fixture")
        argv = ["collect_receipts.py", "--inputs", str(inputs), "--results", str(receipts)]

        class Cube:
            def __init__(self, *args):
                self.meta = {"cover_cnf_sha256": "a" * 64}
                self.n_leaves = 1

            def leaf_sha256(self, leaf):
                assert leaf == 0
                return "b" * 64

        def run(cake, selectors=(), inventory=("cube_a", "cube_b")):
            rows = []
            for name in inventory:
                for kind, leaf, sha in [("cover", None, "a" * 64), ("leaf", 0, "b" * 64)]:
                    bins = {"cadical": collector.CADICAL}
                    if cake is not None:
                        bins["cake_lpr"] = cake
                    rows.append({"cube": name, "kind": kind, "leaf": leaf,
                        "status": "CERTIFIED", "cnf_sha256": sha, "binaries": bins,
                        "checker": {"verified_line": True, "cpu_seconds": 1},
                        "solver": {"returncode": 20, "cpu_seconds": 1},
                        "proof": {"checker_closed_early": False, "bytes": 1, "sha256": "c" * 64}})
            decoded = "".join(json.dumps(row) + "\n" for row in rows).encode()
            with patch.object(collector.hc, "CUBES", list(inventory)), \
                    patch.object(collector.hc, "Cube", Cube), \
                    patch.object(collector.subprocess, "run", return_value=
                                 subprocess.CompletedProcess([], 0, stdout=decoded)), \
                    patch.object(sys, "argv", argv + list(selectors)), \
                    contextlib.redirect_stdout(io.StringIO()) as out, \
                    contextlib.redirect_stderr(io.StringIO()) as err:
                try:
                    rc = collector.main()
                except SystemExit as exc:
                    rc = exc.code
            return {"exit_code": rc, "summary": json.loads(out.getvalue()) if out.getvalue() else None,
                    "argument_error": bool(err.getvalue())}

        results["approved_checker"] = r = run(CAKE)
        assert r["exit_code"] == 0 and r["summary"]["full_campaign_complete"] is True
        for label, cake in [("wrong_checker", "0" * 64), ("missing_checker", None)]:
            results[label] = r = run(cake)
            assert r["exit_code"] == 1 and r["summary"]["all_complete"] is False
            assert r["summary"]["totals"]["certified_leaves"] == 0
        for label, selectors, inventory in [
            ("unknown_selector", ["--cubes", "cube_TYPO"], ("cube_a", "cube_b")),
            ("mixed_selector", ["--cubes", "cube_a,cube_TYPO"], ("cube_a", "cube_b")),
            ("empty_selector_token", ["--cubes", ","], ("cube_a", "cube_b")),
            ("empty_inventory", [], ())]:
            results[label] = r = run(CAKE, selectors, inventory)
            assert r["exit_code"] == 2 and r["argument_error"] and r["summary"] is None
        results["known_subset"] = r = run(CAKE, ["--cubes", "cube_a"])
        assert r["exit_code"] == 0 and r["summary"]["all_complete"] is True
        assert r["summary"]["full_campaign_complete"] is False
        assert r["summary"]["selected_cubes"] == ["cube_a"]
        print(json.dumps({"status": "PASS", "base_commit": COMMIT,
            "patch_sha256": hashlib.sha256(proposed.read_bytes()).hexdigest(),
            "cases": len(results), "results": results,
            "scope": "Metadata-only acceptance tests in a temporary tree; no solver, Lean, or campaign mutation."},
            indent=2))


if __name__ == "__main__":
    main()
