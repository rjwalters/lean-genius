"""Compile the audited production Runtime C and test only existing bucket 384/0."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert Path('/.dockerenv').exists() and Path.cwd() == Path('/workspace/proofs')
    audit = json.loads((ROOT / 'build-evidence/AUDIT.json').read_text())
    assert audit['status'] == 'RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS'
    for item in audit['results']:
        module = item['module']
        assert sha(Path('Proofs') / (module + '.lean')) == item['source_sha256']
        assert sha(Path('.lake/build/lib/lean/Proofs') / (module + '.olean')) == item['olean_sha256']
    cpath = Path('.lake/build/ir/Proofs/Erdos85H3TripleCompletionRuntime.c').resolve()
    assert sha(cpath) == audit['runtime_c']['sha256']
    initializers = re.findall(r'LEAN_EXPORT lean_object\* (initialize_\w+)\(uint8_t builtin\) \{',
                              cpath.read_text())
    assert len(initializers) == 1, initializers
    source = ROOT.parent / 'h3_triple_completion_20261008/Probe384R0.lean'
    assert sha(source) == 'badb03f821a2011a5dd36b0793d5ad608ef1139a12729cd97afd072e6b9d840d'
    output = ROOT / 'canary1'
    output.mkdir(exist_ok=False)
    stage = Path('H3TripleCompletionHelpersProbe.lean')
    with stage.open('xb') as f:
        f.write(source.read_bytes())
    report = {'status': 'RUNNING', 'steps': [], 'source_sha256': sha(source),
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'build_audit_sha256': sha(ROOT / 'build-evidence/AUDIT.json'),
              'runtime_c': audit['runtime_c'], 'initializer': initializers[0],
              'scope': 'Existing triplePart 384 0 only; no additional bucket or whole-cell credit.'}

    def save():
        (output / 'RUN.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(name, cmd, cap):
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic()
        timed_out = False
        with (output / (name + '.log')).open('xb') as log:
            process = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                rc = process.wait(timeout=cap)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                rc = process.wait()
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        entry = {'name': name, 'command': cmd, 'timeout_seconds': cap,
                 'returncode': rc, 'timed_out': timed_out,
                 'elapsed_seconds': time.monotonic() - start,
                 'child_user_seconds': after.ru_utime - before.ru_utime,
                 'child_system_seconds': after.ru_stime - before.ru_stime,
                 'child_maxrss_kib_cumulative': after.ru_maxrss,
                 'log_sha256': sha(output / (name + '.log'))}
        report['steps'].append(entry)
        save()
        print(json.dumps(entry), flush=True)
        print((output / (name + '.log')).read_text(), flush=True)
        return rc == 0

    try:
        library = output / 'libH3TripleRuntime.so'
        if not run('shared', ['leanc', '-O3', '-DLEAN_EXPORTING', '-shared', '-fPIC',
                              str(cpath), '-o', str(library)], 60):
            report['status'] = 'SHARED_COMPILE_FAILED'
            return
        symbols = subprocess.check_output(['nm', '-D', '--defined-only', str(library)], text=True)
        (output / 'symbols.log').write_text(symbols)
        assert ' ' + initializers[0] + '\n' in symbols
        passed = run('probe', ['lean', '-j1', '--plugin=' + str(library) + '=' + initializers[0],
                              str(stage), '-o', str(output / 'Probe384R0.olean')], 180)
        report['status'] = 'COMPILED' if passed else 'PROBE_FAILED'
        report['artifacts'] = {}
        for name in ('libH3TripleRuntime.so', 'Probe384R0.olean', 'symbols.log'):
            if (output / name).exists():
                report['artifacts'][name] = {'sha256': sha(output / name),
                                             'bytes': (output / name).stat().st_size}
        for item in audit['results']:
            assert sha(Path('.lake/build/lib/lean/Proofs') / (item['module'] + '.olean')) == item['olean_sha256']
    finally:
        save()
        stage.unlink()
        print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
    result = json.loads((ROOT / 'canary1/RUN.json').read_text())
    raise SystemExit(0 if result['status'] == 'COMPILED' else 1)
