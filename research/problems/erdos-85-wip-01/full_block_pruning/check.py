from contextlib import nullcontext
from pathlib import Path
import argparse
import os
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--coverage-build', type=Path, required=True)
parser.add_argument('--build-dir', type=Path, help='Optional empty directory retaining dependency oleans')
args = parser.parse_args()
coverage = args.coverage_build.resolve()
if not (coverage / 'Assembly.olean').is_file() or not (coverage / 'Full_3_3.olean').is_file():
    parser.error('coverage build must contain verified Assembly.olean and Full_3_3.olean')
root = Path(__file__).resolve().parent
context = nullcontext(str(args.build_dir.resolve())) if args.build_dir else tempfile.TemporaryDirectory(prefix='erdos85-full-block-pruning-')
with context as temporary:
    build = Path(temporary)
    build.mkdir(parents=True, exist_ok=True)
    if any(build.iterdir()):
        parser.error('build directory must be empty; inspect any existing run before reusing it')
    env = os.environ.copy()
    env['LEAN_PATH'] = env.get('LEAN_PATH', '') + os.pathsep + str(coverage) + os.pathsep + str(build)
    for directory, name in [('full_orbit_transport', 'Transport'), ('full_orbit_pruning', 'Pruning'), ('full_block_orbits', 'Certificate')]:
        source = root.parent / directory / (name + '.lean')
        result = subprocess.run(['lean', '-R', str(source.parent), '-o', str(build / (name + '.olean')), str(source)], env=env)
        if result.returncode:
            raise SystemExit(result.returncode)
    raise SystemExit(subprocess.run(['lean', str(root / 'Reduction.lean')], env=env).returncode)
