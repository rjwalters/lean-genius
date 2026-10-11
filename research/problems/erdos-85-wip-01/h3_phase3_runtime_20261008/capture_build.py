"""Run the read-only cloud audit and retain its exact evidence locally."""
import base64
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    script = (ROOT / 'audit_build.py').read_bytes()
    code = ('import base64;exec(compile(base64.b64decode('
            + repr(base64.b64encode(script).decode()) + '),"audit_build.py","exec"))')
    result = subprocess.run(
        ['/Users/rwalters/.local/bin/e85-remote', 'ssh', 'python3 -B -c ' + shlex.quote(code)],
        capture_output=True)
    if result.returncode:
        print(result.stderr.decode(), end='')
        raise SystemExit(result.returncode)
    bundle = json.loads(result.stdout)
    if bundle.get('status') == 'PENDING':
        print(json.dumps(bundle))
        return
    report = bundle['audit']
    report['auditor_sha256'] = hashlib.sha256(script).hexdigest()
    files = {name: base64.b64decode(data) for name, data in bundle['files_base64'].items()}
    for name, data in files.items():
        assert hashlib.sha256(data).hexdigest() == report['retained_files_sha256'][name]
    files['AUDIT.json'] = (json.dumps(report, indent=2) + '\n').encode()
    for name, data in files.items():
        path = ROOT / 'build-evidence' / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.exists():
            assert path.read_bytes() == data, 'Refusing to overwrite historical evidence: ' + name
        else:
            path.write_bytes(data)
    print(report['status'])
    print(json.dumps(report['results'], indent=2))


if __name__ == '__main__':
    main()
