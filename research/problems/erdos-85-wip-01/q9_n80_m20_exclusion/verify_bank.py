from pathlib import Path
import json,hashlib
p=Path(__file__).parent
a=json.loads((p/"bank-pins.json").read_text())
for f,h in a.items():assert hashlib.sha256((p/f).read_bytes()).hexdigest()==h,f
print("PASS",len(a),"payload hashes")
