"""Bounded standalone interpreter/plugin comparison, cloud container only.

No production sources or build objects are modified. Copied runtime definitions
do not establish a production exclusion or an equivalence theorem.
"""
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
    manifest = json.loads((ROOT / 'SOURCE.json').read_text())
    for path, digest in manifest['sources'].items():
        assert sha(Path('/workspace') / path) == digest, path
    assert sha(ROOT / 'H3NativeRuntime.lean') == manifest['runtime_sha256']
    output = ROOT / 'attempt1'
    output.mkdir(exist_ok=False)
    stage = Path('/workspace/proofs/H3NativeStandaloneProbe')
    stage.mkdir(exist_ok=False)
    for name in ('H3NativeRuntime.lean', 'H3NativeProbe.lean'):
        (stage / name).write_bytes((ROOT / name).read_bytes())
    env = dict(os.environ)
    env['LEAN_PATH'] = str(stage) + ':' + env.get('LEAN_PATH', '')
    report = {'status': 'RUNNING', 'scope': manifest['scope'], 'steps': [],
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'runtime_source_sha256': sha(ROOT / 'H3NativeRuntime.lean'),
              'probe_source_sha256': sha(ROOT / 'H3NativeProbe.lean')}

    def save():
        (output / 'RUN.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(name, cmd, cap):
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic()
        timed_out = False
        with (output / (name + '.log')).open('xb') as log:
            process = subprocess.Popen(cmd, cwd=stage, env=env, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
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
        if not run('runtime', ['lean', '-j1', 'H3NativeRuntime.lean', '-o',
                              'H3NativeRuntime.olean', '-c', 'H3NativeRuntime.c'], 60):
            report['status'] = 'RUNTIME_COMPILE_FAILED'
            return
        c = (stage / 'H3NativeRuntime.c').read_text()
        initializers = re.findall(r'LEAN_EXPORT lean_object\* (initialize_\w+)\(uint8_t builtin\) \{', c)
        assert len(initializers) == 1, initializers
        report['initializer'] = initializers[0]
        library = stage / 'libH3NativeRuntime.so'
        if not run('shared', ['leanc', '-O3', '-shared', '-fPIC', 'H3NativeRuntime.c',
                             '-o', str(library)], 60):
            report['status'] = 'SHARED_COMPILE_FAILED'
            return
        plain = run('plain', ['lean', '-j1', 'H3NativeProbe.lean', '-o',
                              str(output / 'Plain.olean')], 90)
        plugin = run('plugin', ['lean', '-j1', '--plugin=' + str(library) + ':' + initializers[0],
                                'H3NativeProbe.lean', '-o', str(output / 'Plugin.olean')], 90)
        report['status'] = 'BOTH_COMPILED' if plain and plugin else 'COMPARISON_INCOMPLETE'
        report['artifacts'] = {}
        for name in ('H3NativeRuntime.olean', 'H3NativeRuntime.c', 'libH3NativeRuntime.so'):
            data = (stage / name).read_bytes()
            (output / name).write_bytes(data)
            report['artifacts'][name] = {'sha256': sha(output / name), 'bytes': len(data)}
        for name in ('Plain.olean', 'Plugin.olean'):
            if (output / name).exists():
                report['artifacts'][name] = {'sha256': sha(output / name),
                                             'bytes': (output / name).stat().st_size}
    finally:
        save()
        # Preserve this attempt's intermediate files for failed-stage diagnosis.
        # Unique staging and attempt names prevent overwriting historical evidence.
        print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
    result = json.loads((ROOT / 'attempt1/RUN.json').read_text())
    raise SystemExit(0 if result['status'] == 'BOTH_COMPILED' else 1)
