from pathlib import Path
import argparse
import os
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--coverage-build', type=Path, required=True)
args = parser.parse_args()
coverage = args.coverage_build.resolve()
if not (coverage / 'Deficient_3_3_0.olean').is_file():
    parser.error('coverage build must contain verified Deficient_3_3_0.olean')
env = os.environ.copy()
env['LEAN_PATH'] = env.get('LEAN_PATH', '') + os.pathsep + str(coverage)
raise SystemExit(subprocess.run(['lean', str(Path(__file__).with_name('Pruning.lean'))], env=env).returncode)
