"""Replay against immutable commit 336fabf2b61; produce a retention patch and review receipts."""
import difflib
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
COMMIT = "336fabf2b61"
BASE = "research/problems/erdos-85-wip-01/"
CAMPAIGN = BASE + "h7_hsb_campaign_20261008/"
INPUTS = Path("/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h7-hsb-campaign-20261008/inputs")


def run(script, campaign, *args):
    result = subprocess.run([sys.executable, "-B", str(script), *args], capture_output=True, text=True,
                            env=dict(os.environ, PYTHONPATH=str(campaign), PYTHONDONTWRITEBYTECODE="1"))
    return {"exit_code": result.returncode, "output": result.stdout + result.stderr}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    with tempfile.TemporaryDirectory(prefix="h7-split-review-") as tmp:
        root = Path(tmp)
        archive = subprocess.check_output(["git", "-C", str(REPO), "archive", COMMIT, CAMPAIGN,
                                           BASE + "h1_cert_full_20261001/cert_row.py",
                                           BASE + "phase_b_h1_verdict_cloud_20260921/controller.py"])
        with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
            for member in tf.getmembers():
                assert member.isfile() or member.isdir()
                assert not PurePosixPath(member.name).is_absolute() and ".." not in PurePosixPath(member.name).parts
            tf.extractall(root)
        campaign = root / CAMPAIGN
        baseline = run(HERE / "test_split_review.py", campaign)
        host_probe = run(HERE / "probe_host.py", campaign)
        changes = {}

        def replace(name, edits):
            path = campaign / name
            before = after = path.read_text()
            for old, new in edits:
                assert after.count(old) == 1, (name, old)
                after = after.replace(old, new)
            path.write_text(after)
            changes[CAMPAIGN + name] = (before, after)

        replace("cert_item.py", [
            ('def retained_stem(cube_name: str, kind: str, leaf: int | None = None) -> str:',
             'def retained_stem(cube_name: str, kind: str, leaf: int | None = None, split_sha256: str | None = None) -> str:'),
            ('    """File stem of a retained CNF/proof pair: <cube>.cover, or <cube>-s<leaf:05d>.subcover."""\n'
             '    return f"{cube_name}.cover" if kind == "cover" else f"{cube_name}-s{leaf:05d}.subcover"',
             '    """Keep every split\'s CNF/proof pair under its full split identity."""\n'
             '    if kind == "cover":\n        return f"{cube_name}.cover"\n'
             '    if not isinstance(split_sha256, str) or len(split_sha256) != 64 or any(x not in "0123456789abcdef" for x in split_sha256):\n'
             '        raise ValueError("a retained subcover needs its split sha256")\n'
             '    return f"{cube_name}-s{leaf:05d}-{split_sha256}.subcover"'),
            ('stem = retained_stem(cube.name, kind, leaf)',
             'stem = retained_stem(cube.name, kind, leaf, split["split_sha256"] if split else None)'),
        ])
        replace("cert_worker.py", [
            ('f"{row[\'cube\']}-s{row[\'leaf\']:05d}.subcover" if row["kind"] == "subcover" else None)',
             'f"{row[\'cube\']}-s{row[\'leaf\']:05d}-{row[\'split_sha256\']}.subcover" if row["kind"] == "subcover" else None)'),
        ])
        changes[CAMPAIGN + "test_split_review.py"] = ("", (HERE / "test_split_review.py").read_text())
        diff = "".join("".join(difflib.unified_diff(a.splitlines(True), b.splitlines(True),
                         fromfile="a/" + path if a else "/dev/null", tofile="b/" + path))
                       for path, (a, b) in changes.items())
        (HERE / "retain_split_identity.patch").write_text(diff)
        results = {"commit": COMMIT, "baseline": baseline, "host_probe": host_probe,
                   "patched": run(HERE / "test_split_review.py", campaign),
                   "campaign_suite": run(campaign / "test_campaign.py", campaign),
                   "stop_suite": run(campaign / "test_stop_enforcement.py", campaign),
                   "cloud_mutations": False, "fresh_lean_compile": False}
        if (INPUTS / "inputs.json").is_file():
            regenerated = root / "identity.json"
            result = run(campaign / "check_split_identity.py", campaign, "fixture", "--inputs", str(INPUTS),
                         "--specs", str(campaign / "receipts/split_specs_depth6_7leaves.jsonl"), "--out", str(regenerated))
            assert result["exit_code"] == 0, result
            receipt = json.loads((campaign / "receipts/split_identity_lean.json").read_text())
            expected = campaign / "receipts/split_identity_fixture.json"
            assert regenerated.read_bytes() == expected.read_bytes()
            assert sha(expected) == receipt["fixture_sha256"]
            assert sha(campaign / "EmitSplit.lean") == receipt["emitter_sha256"]
            results["identity_chain"] = {"fixture_regeneration": "byte-identical", "count": receipt["count"],
                                         "fixture_sha256": sha(expected), "emitter_sha256": sha(campaign / "EmitSplit.lean"),
                                         "lean_run": "Existing receipt hashes verified; Lean not rerun"}
        else:
            results["identity_chain"] = {"skipped": "Pinned inputs unavailable"}
        (HERE / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps({k: v.get("exit_code", v) for k, v in results.items() if isinstance(v, dict)}, indent=2))
        assert baseline["exit_code"] == 1 and "re-splitting overwrote" in baseline["output"], baseline
        for key in ("patched", "campaign_suite", "stop_suite", "host_probe"):
            assert results[key]["exit_code"] == 0, (key, results[key])


if __name__ == "__main__":
    main()
