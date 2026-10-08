"""Run only the frozen five-part sizing sample on the existing cloud builder."""
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

from prepare import part_source

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert Path('/.dockerenv').exists() and Path.cwd() == Path('/workspace/proofs')
    memory = Path('/sys/fs/cgroup/memory.max').read_text().strip()
    cpu = Path('/sys/fs/cgroup/cpu.max').read_text().strip()
    assert int(memory) == 16 * 1024**3, memory
    quota, period = map(int, cpu.split())
    assert quota == 2 * period, cpu
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['status'] == 'PREPARED_NOT_LAUNCHED'
    assert manifest['sizing_sample']['residues_in_order'] == [0, 3, 5, 4, 162]
    assert sha(ROOT / 'prepare.py') == manifest['source_generator_sha256']
    audit_path = Path('/workspace') / manifest['prerequisite_audit']['path']
    assert sha(audit_path) == manifest['prerequisite_audit']['sha256']
    audit = json.loads(audit_path.read_text())
    assert audit['status'] == 'RUNTIME_HELPERS_CHAIN_BUILD_AUDIT_PASS'
    assert audit['execution_commit'] == manifest['math_commit']
    cache = Path('.lake/build/lib/lean/Proofs').resolve()

    def prerequisites():
        for item in audit['results']:
            assert sha(Path('Proofs') / (item['module'] + '.lean')) == item['source_sha256']
            assert sha(cache / (item['module'] + '.olean')) == item['olean_sha256']

    prerequisites()
    cpath = Path('.lake/build/ir/Proofs/Erdos85H3TripleCompletionRuntime.c').resolve()
    assert sha(cpath) == audit['runtime_c']['sha256']
    initializers = re.findall(r'LEAN_EXPORT lean_object\* (initialize_\w+)\(uint8_t builtin\) \{', cpath.read_text())
    assert len(initializers) == 1
    rows = [manifest['parts'][r] for r in manifest['sizing_sample']['residues_in_order']]
    for row in rows:
        assert not Path(row['source_path']).exists(), 'Refusing existing source'
        assert not (cache / (row['module'].split('.')[-1] + '.olean')).exists(), 'Refusing existing object'
    output = ROOT / 'sample1'
    output.mkdir(exist_ok=False)
    (output / 'sources/Proofs').mkdir(parents=True)
    (output / 'objects').mkdir()
    deadline = time.monotonic() + 540
    report = {'status': 'RUNNING', 'steps': [], 'parts': [],
              'cgroup_memory_bytes': int(memory), 'cgroup_cpu_max': cpu,
              'started_utc': datetime.now(timezone.utc).isoformat(),
              'manifest_sha256': sha(ROOT / 'MANIFEST.json'),
              'prerequisite_audit_sha256': sha(audit_path), 'initializer': initializers[0],
              'scope': 'Frozen five-part sample only; no full campaign or aggregate verdict.'}

    def save():
        temp = output / 'RUN.json.tmp'
        temp.write_text(json.dumps(report, indent=2) + '\n')
        temp.replace(output / 'RUN.json')

    def stopped():
        return (ROOT / 'STOP').exists() or time.monotonic() >= deadline

    def run(name, command, cap):
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic()
        effective = min(cap, max(0, deadline - start))
        assert effective > 0
        timed_out = False
        with (output / (name + '.log')).open('xb') as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                rc = process.wait(timeout=effective)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                rc = process.wait()
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        entry = {'name': name, 'command': command, 'timeout_seconds': cap,
                 'effective_timeout_seconds': effective, 'returncode': rc, 'timed_out': timed_out,
                 'elapsed_seconds': time.monotonic() - start,
                 'child_user_seconds': after.ru_utime - before.ru_utime,
                 'child_system_seconds': after.ru_stime - before.ru_stime,
                 'child_maxrss_kib_cumulative': after.ru_maxrss,
                 'log_sha256': sha(output / (name + '.log'))}
        report['steps'].append(entry)
        save()
        print(json.dumps(entry), flush=True)
        print((output / (name + '.log')).read_text(), flush=True)
        return entry

    try:
        if stopped():
            report['status'] = 'STOPPED'
            return
        library = output / 'libH3TripleRuntime.so'
        shared = run('shared', ['leanc', '-O3', '-DLEAN_EXPORTING', '-shared', '-fPIC',
                                str(cpath), '-o', str(library)], 60)
        if shared['returncode'] != 0:
            report['status'] = 'COMPILE_TIMEOUT' if shared['timed_out'] else 'ALARM'
            return
        report['library'] = {'sha256': sha(library), 'bytes': library.stat().st_size}
        for row in rows:
            if stopped():
                report['status'] = 'STOPPED'
                return
            prerequisites()
            source = part_source(row['residue']).encode()
            assert hashlib.sha256(source).hexdigest() == row['source_sha256']
            staged = Path(row['source_path'])
            retained = output / 'sources' / row['source_path']
            retained.write_bytes(source)
            obj = cache / (row['module'].split('.')[-1] + '.olean')
            with staged.open('xb') as f:
                f.write(source)
            try:
                step = run(f'part{row["residue"]:03d}',
                           ['lean', '-j1', '--plugin=' + str(library) + '=' + initializers[0],
                            str(staged), '-o', str(obj)], 90)
            finally:
                staged.unlink()
            item = {'residue': row['residue'], 'module': row['module'],
                    'source_sha256': row['source_sha256'], 'status': 'UNVERIFIED'}
            report['parts'].append(item)
            if step['returncode'] != 0:
                item['status'] = 'TIMEOUT' if step['timed_out'] else 'ALARM'
                report['status'] = item['status']
                return
            raw = (output / (step['name'] + '.log')).read_text()
            reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", raw)
            assert not re.search(r'\b(sorry|error)\b', raw, re.I)
            assert len(reports) == 1 and reports[0][0] == row['theorem']
            axioms = [a.strip() for a in reports[0][1].split(',') if a.strip()]
            assert len(axioms) == 3 and set(axioms) == {'propext', 'Quot.sound', row['native_axiom']}
            data = obj.read_bytes()
            assert data
            (output / 'objects' / obj.name).write_bytes(data)
            item.update(status='COMPILED_PENDING_AUDIT', axioms=axioms,
                        object_sha256=sha(obj), object_bytes=len(data), object_mtime=obj.stat().st_mtime)
            prerequisites()
            save()
        report['status'] = 'SAMPLE_COMPILED_PENDING_AUDIT'
    except Exception as exc:
        report['status'] = 'ALARM'
        report['exception'] = repr(exc)
        raise
    finally:
        save()
        print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
    report = json.loads((ROOT / 'sample1/RUN.json').read_text())
    raise SystemExit(0 if report['status'] == 'SAMPLE_COMPILED_PENDING_AUDIT' else 1)
