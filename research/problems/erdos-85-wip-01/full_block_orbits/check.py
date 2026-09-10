import argparse,os,subprocess
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--coverage-build',type=Path,required=True)
a=parser.parse_args()
assert (a.coverage_build/'Full_3_3.olean').is_file()
e=os.environ.copy();e['LEAN_PATH']=e.get('LEAN_PATH','')+':'+str(a.coverage_build.resolve())
raise SystemExit(subprocess.call(['lean',str(Path(__file__).with_name('Certificate.lean'))],env=e))
