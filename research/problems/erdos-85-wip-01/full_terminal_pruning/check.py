"""Compile the terminal pruning reduction against retained verified builds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

parser = argparse.ArgumentParser()
for name in ('full-u-build', 'pruning-build', 'pair-coverage-build',
             'pair-rejections-build', 'pair-exclusion-build'):
    parser.add_argument('--' + name, type=Path, required=True)
parser.add_argument('--representatives-build', type=Path)
parser.add_argument('--build-dir', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent
build = (args.build_dir or Path(tempfile.mkdtemp(prefix='erdos85-terminal-pruning-'))).resolve()
if build.exists() and any(build.iterdir()):
    parser.error('build directory must be empty')
paths = [args.full_u_build, args.pruning_build, args.pair_coverage_build,
         args.pair_rejections_build, args.pair_exclusion_build]
required = ['Assembly', 'Pruning', 'CoverageAssembly', 'OrderedLeaves', 'FixedPairExclusion']
for path, module in zip(paths, required):
    if not (path / (module + '.olean')).is_file():
        parser.error(f'{path} must contain verified {module}.olean')
if args.representatives_build:
    paths.append(args.representatives_build)
receipt = json.loads((root / 'RECEIPT.json').read_text())
base = root.parent / 'full_block_pruning' / 'Reduction.lean'
source = root / 'TerminalReduction.lean'
assert hashlib.sha256(base.read_bytes()).hexdigest() == receipt['base_source_sha256']
assert hashlib.sha256(source.read_bytes()).hexdigest() == receipt['sha256']['TerminalReduction.lean']
build.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join([str(build), *(str(p.resolve()) for p in paths),
                                   env.get('LEAN_PATH', '')])
results = []
for name, original, expected in [('FullBlockReduction', base, 5),
                                  ('TerminalReduction', source, 6)]:
    target = build / (name + '.lean')
    target.write_bytes(original.read_bytes())
    start = time.monotonic()
    with (build / (name + '.log')).open('w') as log:
        result = subprocess.run(['lean', '--root=' + str(build), '-o',
                                 str(build / (name + '.olean')), str(target)],
                                env=env, stdout=log, stderr=subprocess.STDOUT)
    output = (build / (name + '.log')).read_text()
    exports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    axioms_ok = all({a.strip() for a in xs.split(',') if a.strip()} <= allowed for xs in exports)
    ok = (result.returncode == 0 and len(exports) == expected and axioms_ok
          and target.read_bytes() == original.read_bytes())
    results.append({'module': name, 'exit_code': result.returncode, 'verified': ok,
                    'seconds': time.monotonic() - start, 'exports': len(exports),
                    'source_sha256': hashlib.sha256(target.read_bytes()).hexdigest()})
    (build / 'RESULT.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results[-1]), flush=True)
    if not ok:
        raise SystemExit(1)
print('PASS: 275 remaining full pairs; their rejection is still an explicit premise.')
