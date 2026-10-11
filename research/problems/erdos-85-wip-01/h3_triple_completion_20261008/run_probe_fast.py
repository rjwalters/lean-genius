"""Run exactly one five-minute native diagnostic inside the cloud Lean image."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert Path('/.dockerenv').exists() and Path.cwd() == Path('/workspace/proofs')
    output = ROOT / 'probe384r0-fast'
    output.mkdir(exist_ok=False)
    source = ROOT / 'Probe384R0.lean'
    staged = Path('H3TripleCompletionProbe384R0Fast.lean')
    with staged.open('xb') as f:
        f.write(source.read_bytes())
    expected = json.loads((ROOT / 'fast-state-build/AUDIT.json').read_text())
    for item in expected['results']:
        module = item['module']
        assert sha(Path('Proofs') / (module + '.lean')) == item['source_sha256']
        assert sha(Path('.lake/build/lib/lean/Proofs') / (module + '.olean')) == item['olean_sha256']
    obj = output / 'Probe384R0.olean'
    cmd = ['lean', '-j1', str(staged), '-o', str(obj)]
    report = {'command': cmd, 'source_sha256': sha(source), 'timeout_seconds': 300,
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'prerequisites': expected['results'], 'status': 'RUNNING'}
    start = time.monotonic()
    timed_out = False
    try:
        with (output / 'probe.log').open('xb') as log:
            process = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                rc = process.wait(timeout=300)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                rc = process.wait()
        usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        report.update(returncode=rc, timed_out=timed_out, elapsed_seconds=time.monotonic()-start,
                      child_user_seconds=usage.ru_utime, child_system_seconds=usage.ru_stime,
                      child_maxrss_kib=usage.ru_maxrss, log_sha256=sha(output / 'probe.log'),
                      status='TIMEOUT' if timed_out else ('COMPILED' if rc == 0 else 'FAILED'))
        if obj.exists():
            report.update(olean_sha256=sha(obj), olean_bytes=obj.stat().st_size)
        (output / 'RUN.json').write_text(json.dumps(report, indent=2) + '\n')
        print((output / 'probe.log').read_text(), flush=True)
        print(json.dumps(report, indent=2), flush=True)
    finally:
        staged.unlink()
    raise SystemExit(124 if timed_out else rc)


if __name__ == '__main__':
    main()
