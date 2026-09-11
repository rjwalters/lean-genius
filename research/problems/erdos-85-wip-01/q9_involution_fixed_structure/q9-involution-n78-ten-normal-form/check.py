from pathlib import Path
import json
p=Path(__file__).resolve().parent
profiles=[{'m':m,'D':d,'R_edges':12-2*m+d} for m in range(4) for d in range(0,37,2) if 12-2*m+d<=8]
assert profiles==[{'m':2,'D':0,'R_edges':8},{'m':3,'D':0,'R_edges':6},{'m':3,'D':2,'R_edges':8}]
(p/'arithmetic.json').write_text(json.dumps({'status':'PASS','profiles':profiles},indent=2)+'\n')
