from pathlib import Path
import argparse
import os
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--coverage-build', type=Path, required=True)
args = parser.parse_args()
coverage = args.coverage_build.resolve()
if not (coverage / 'Assembly.olean').is_file():
    parser.error('coverage build must contain Assembly.olean')
root = Path(__file__).resolve().parent
transport = root.parent / 'full_orbit_transport' / 'Transport.lean'
with tempfile.TemporaryDirectory(prefix='erdos85-full-pruning-') as temporary:
    env = os.environ.copy()
    env['LEAN_PATH'] = env.get('LEAN_PATH', '') + os.pathsep + str(coverage) + os.pathsep + temporary
    result = subprocess.run(['lean', '-R', str(transport.parent), '-o', str(Path(temporary) / 'Transport.olean'), str(transport)], env=env)
    if result.returncode:
        raise SystemExit(result.returncode)
    raise SystemExit(subprocess.run(['lean', str(root / 'Pruning.lean')], env=env).returncode)
