"""Retry only plugin compilation/evaluation after the retained CLI failure."""
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
    prior = json.loads((ROOT / 'evidence1/RUN.json').read_text())
    assert prior == json.loads((ROOT / 'attempt1/RUN.json').read_text())
    assert prior['status'] == 'COMPARISON_INCOMPLETE'
    assert prior['steps'][2]['name'] == 'plain' and prior['steps'][2]['returncode'] == 0
    stage = Path('/workspace/proofs/H3NativeStandaloneProbe')
    for name in ('H3NativeRuntime.c', 'H3NativeRuntime.olean'):
        assert sha(stage / name) == prior['artifacts'][name]['sha256']
    assert sha(stage / 'H3NativeRuntime.lean') == prior['runtime_source_sha256']
    assert sha(stage / 'H3NativeProbe.lean') == prior['probe_source_sha256']
    output = ROOT / 'attempt2'
    output.mkdir(exist_ok=False)
    env = dict(os.environ)
    env['LEAN_PATH'] = str(stage) + ':' + env.get('LEAN_PATH', '')
    report = {'status': 'RUNNING', 'steps': [], 'scope': prior['scope'],
              'prior_receipt_sha256': sha(ROOT / 'attempt1/RUN.json'),
              'started_utc': datetime.now(timezone.utc).isoformat()}

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
        (output / 'RUN.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(entry), flush=True)
        print((output / (name + '.log')).read_text(), flush=True)
        return rc == 0

    library = output / 'libH3NativeRuntimeExport.so'
    if run('shared', ['leanc', '-O3', '-DLEAN_EXPORTING', '-shared', '-fPIC',
                      'H3NativeRuntime.c', '-o', str(library)], 60):
        symbols = subprocess.check_output(['nm', '-D', '--defined-only', str(library)], text=True)
        (output / 'symbols.log').write_text(symbols)
        assert ' initialize_H3NativeRuntime\n' in symbols
        passed = run('plugin', ['lean', '-j1', '--plugin=' + str(library) + '=initialize_H3NativeRuntime',
                               'H3NativeProbe.lean', '-o', str(output / 'Plugin.olean')], 90)
        report['status'] = 'PLUGIN_COMPILED' if passed else 'PLUGIN_FAILED'
    else:
        report['status'] = 'SHARED_COMPILE_FAILED'
    report['artifacts'] = {}
    for name in ('libH3NativeRuntimeExport.so', 'Plugin.olean', 'symbols.log'):
        if (output / name).exists():
            report['artifacts'][name] = {'sha256': sha(output / name),
                                         'bytes': (output / name).stat().st_size}
    (output / 'RUN.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2), flush=True)
    raise SystemExit(0 if report['status'] == 'PLUGIN_COMPILED' else 1)


if __name__ == '__main__':
    main()
