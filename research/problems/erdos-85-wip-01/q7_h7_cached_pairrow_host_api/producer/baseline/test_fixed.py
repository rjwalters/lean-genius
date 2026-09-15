"""Complete traversal controls on saved fixed host assignments only."""
import ctypes
import gzip
import json
from pathlib import Path
import api
import check_receipt
P=Path(__file__).parent
inputs=json.loads((P/'fixture-launch.json').read_text())['inputs']
inputs=[r for r in inputs if r['F_index']==5]
keys={(r['case_index'],r['pairing_index']):r for r in inputs}
source=Path('/Users/rwalters/lean-genius-h7-f5-sol2-20260915/hosts/receipts-000.jsonl.gz')
for line in gzip.open(source,'rt'):
    r=json.loads(line);key=r['case_index'],r['pairing_index']
    if key in keys:keys[key]['fixed']=r['receipt']['solutions'][0]
    if all('fixed' in r for r in inputs):break
U=ctypes.c_uint64
api.lib.check_fixed_hosts.argtypes=[ctypes.POINTER(U),ctypes.POINTER(U),ctypes.c_int,ctypes.c_double]
api.lib.check_fixed_hosts.restype=ctypes.c_char_p
results=[]
for fixture in inputs:
    base=fixture['adjacency'];fixed=fixture['fixed']
    receipt=json.loads(api.lib.check_fixed_hosts((U*49)(*[sum(1<<v for v in ns) for ns in base]),(U*7)(*fixed),100000,1))
    checked=check_receipt.check(base,receipt,seconds=1,fixed=fixed)
    assert receipt['status']=='COMPLETE' and checked['coverage_proved']
    results.append({'input':fixture,'receipt':receipt,'checked':checked})
with (P/'fixed-results.json').open('x') as f:json.dump(results,f)
print(json.dumps({'status':'PASS_FIXED_CONTROLS','count':len(results),'nodes':[r['receipt']['nodes'] for r in results],
                  'scope':'Only four specified host assignments; not a whole high input or root exclusion.'}))
