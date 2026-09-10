from pathlib import Path
import argparse
import os
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--coverage-build', type=Path, required=True)
args = parser.parse_args()
build = args.coverage_build.resolve()
if not (build / 'Assembly.olean').is_file():
    parser.error('coverage build must contain Assembly.olean')
env = os.environ.copy()
env['LEAN_PATH'] = env.get('LEAN_PATH', '') + os.pathsep + str(build)
source = Path(__file__).resolve().with_name('Transport.lean')
raise SystemExit(subprocess.run(['lean', str(source)], env=env).returncode)
