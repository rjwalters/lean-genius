"""Transport the read-only terminal auditor; run no Lean or search locally."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    prior = (ROOT.parent / 'h3_pair_split_review_20261008/AUDIT.json').read_bytes()
    script = (ROOT / 'audit_cloud.py').read_bytes()
    code = 'import base64;exec(compile(base64.b64decode(' + repr(base64.b64encode(script).decode()) + '),"audit_cloud.py","exec"))'
    result = subprocess.run(['/Users/rwalters/.local/bin/e85-remote', 'ssh', 'python3 -B -c ' + shlex.quote(code)],
                            input=prior, capture_output=True)
    if result.returncode:
        print(result.stderr.decode())
        raise SystemExit(result.returncode)
    bundle = json.loads(result.stdout)
    for name, value in bundle['files'].items():
        path = ROOT / 'evidence' / name
        path.parent.mkdir(parents=True, exist_ok=True)
        data = base64.b64decode(value)
        assert hashlib.sha256(data).hexdigest() == bundle['audit']['retained_sha256'][name]
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite different historical bytes: ' + name
        else:
            path.write_bytes(data)
    report = bundle['audit']
    report['auditor_sha256'] = hashlib.sha256(script).hexdigest()
    report['container_live_snapshot_sha256'] = hashlib.sha256((ROOT / 'container-live.json').read_bytes()).hexdigest()
    output = json.dumps(report, indent=2) + '\n'
    path = ROOT / 'AUDIT.json'
    if path.exists():
        assert path.read_text() == output, 'Refusing to overwrite different prior audit'
    else:
        path.write_text(output)
    print(report['status'])


if __name__ == '__main__':
    main()
