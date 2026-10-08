"""Local metadata transport only; all estimate computation runs on the builder.

Run from a Git checkout containing the pinned commit. Mode: independent or exact.
Outputs go next to this script; no solver, Lean, fleet or branch advance.
"""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
COMMIT = '8afe018d8b0587ff2f21f31624161a227eeb99f8'
PKG = 'research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/'
PATHS = {'inputs.json': 'receipts/inputs.json', 'old-sample.jsonl': 'receipts/sample_results.jsonl',
         'new-sample.jsonl': 'receipts/sample_results_with_followup.jsonl',
         'followup.jsonl': 'receipts/capped_followup.jsonl',
         'old-estimate.json': 'receipts/estimate_capped_at_1h.json',
         'new-estimate.json': 'receipts/estimate.json', 'estimate.py': 'estimate.py'}
EXACT = '''
import json, pathlib, subprocess, sys, tempfile, hashlib
b = json.load(sys.stdin)
with tempfile.TemporaryDirectory(prefix="h7-estimate-review-") as d:
    p = pathlib.Path(d)
    for n, value in b["files"].items():
        assert hashlib.sha256(value.encode()).hexdigest() == b["sha256"][n]
        (p / n).write_text(value)
    result = subprocess.run([sys.executable, "-B", str(p / "estimate.py"),
        "--inputs-json", str(p / "inputs.json"), "--sample", str(p / "new-sample.jsonl"),
        "--boot", "5000", "--json", str(p / "result.json")], capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    out = json.loads((p / "result.json").read_text())
    published = json.loads(b["files"]["new-estimate.json"])
    differences = {k: {"published": published.get(k), "recomputed": v}
                   for k, v in out.items() if v != published.get(k)}
    print(json.dumps({"returncode": result.returncode, "python": sys.version,
          "bootstrap_replicates": 5000, "source_sha256": b["sha256"],
          "summary_differences": {k:v for k,v in differences.items() if k != "cubes"},
          "per_cube_differences": [{"cube": x["cube"],
              "differences": {k: {"published": y.get(k), "recomputed": v}
                              for k,v in x.items() if v != y.get(k)}}
              for x,y in zip(out["cubes"], published["cubes"]) if x != y],
          "recomputed": out}, indent=2))
'''


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'independent'
    assert mode in ('independent', 'exact')
    files = {k: subprocess.check_output(['git', 'show', COMMIT + ':' + PKG + v]).decode()
             for k, v in PATHS.items()}
    bundle = {'commit': COMMIT, 'paths': PATHS, 'files': files,
              'sha256': {k: hashlib.sha256(v.encode()).hexdigest() for k, v in files.items()}}
    (ROOT / 'SNAPSHOT.json').write_text(json.dumps({k:v for k,v in bundle.items() if k != 'files'}, indent=2) + '\n')
    script = (ROOT / 'audit_cloud.py').read_bytes() if mode == 'independent' else EXACT.encode()
    code = 'import base64; exec(compile(base64.b64decode(' + repr(base64.b64encode(script).decode()) + '), "audit.py", "exec"))'
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote', 'ssh',
                             'python3.12 -B -c ' + shlex.quote(code)],
                            input=json.dumps(bundle), capture_output=True, text=True)
    if result.returncode:
        sys.stderr.write(result.stderr)
        sys.stdout.write(result.stdout)
        raise SystemExit(result.returncode)
    data = json.loads(result.stdout)
    name = 'AUDIT.json' if mode == 'independent' else 'EXACT_ESTIMATOR.json'
    (ROOT / name).write_text(json.dumps(data, indent=2) + '\n')
    print(name, 'written')


if __name__ == '__main__':
    main()
