from pathlib import Path
import json,hashlib
p=Path(__file__).parent
for f,h in json.loads((p/'bank-pins.json').read_text()).items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
for f,h in json.loads((p/'original/pins.json').read_text()).items():assert hashlib.sha256((p/'original'/f).read_bytes()).hexdigest()==h,f
print('PASS every bank payload and original manifest hash')
