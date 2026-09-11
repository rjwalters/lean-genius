from pathlib import Path
import json,hashlib,tempfile,shutil,subprocess
p=Path(__file__).parent
for f,h in json.loads((p/'bank-pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
for f,h in json.loads((p/'original/pins.json').read_text()).items():assert hashlib.sha256((p/'original'/f).read_bytes()).hexdigest()==h,f
with tempfile.TemporaryDirectory(prefix='erdos85-singleton-positive-') as t:
 q=Path(t)
 for f in ['check.py','profile-source.json','reviews.json','endpoints.json']:shutil.copy2(p/'original'/f,q/f)
 subprocess.run(['python3',str(q/'check.py')],check=True,stdout=subprocess.DEVNULL)
 assert json.loads((q/'results.json').read_text())==json.loads((p/'original/results.json').read_text())
print('PASS all bank hashes and exact six-profile/count replay')
