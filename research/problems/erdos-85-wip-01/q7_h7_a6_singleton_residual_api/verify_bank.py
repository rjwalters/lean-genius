from pathlib import Path
import hashlib,json
p=Path(__file__).parent
for f,h in json.loads((p/'bank-pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
for side in ['original','review']:
 for f,h in json.loads((p/side/'pins.json').read_text()).items():assert hashlib.sha256((p/side/f).read_bytes()).hexdigest()==h,f
print('PASS archived bank/source/review hashes')
