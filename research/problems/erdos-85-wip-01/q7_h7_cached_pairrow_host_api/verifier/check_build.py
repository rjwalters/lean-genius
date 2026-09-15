"""Fresh compiled integration on four fixed controls, not whole inputs."""
import ctypes,hashlib,json
from pathlib import Path
import verifier
P=Path(__file__).parent
S=Path('/Users/rwalters/lean-genius-h7-host-pairrow-sol2-20260915')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((S/'pins.json').read_text())
for n,h in pins.items():assert sha(S/n)==h,n
lib=ctypes.CDLL(str(P/'rebuilt-hosts.dylib'));U=ctypes.c_uint64
lib.check_fixed_hosts.argtypes=[ctypes.POINTER(U),ctypes.POINTER(U),ctypes.c_int,ctypes.c_double]
lib.check_fixed_hosts.restype=ctypes.c_char_p
lib.enumerate_hosts.argtypes=[ctypes.POINTER(U),ctypes.c_int,ctypes.c_double]
lib.enumerate_hosts.restype=ctypes.c_char_p
results=[]
for r in json.loads((S/'cached/fixed-results.json').read_text()):
    base=r['input']['adjacency'];fixed=r['input']['fixed']
    a=(U*49)(*[sum(1<<v for v in ns) for ns in base]);f=(U*7)(*fixed)
    receipt=json.loads(lib.check_fixed_hosts(a,f,100000,1))
    assert receipt==r['receipt']
    checked=verifier.check(base,receipt,fixed=fixed,seconds=1)
    assert checked['coverage_proved'] and checked['endpoint_status']=='PASS'
    results.append(checked)
    for cap,seconds in [(0,1),(100000,-1)]:
        cut=json.loads(lib.check_fixed_hosts(a,f,cap,seconds))
        assert cut['status']=='UNKNOWN' and not cut['solutions'] and not cut['prunes']
    bad=(U*49)(*a);bad[21]|=1<<21
    assert json.loads(lib.enumerate_hosts(bad,100000,1))['status']=='INVALID_INPUT'
out={'status':'PASS_REBUILT_FIXED_CONTROLS','controls':len(results),'results':results,
     'source_sha256':sha(S/'cached/hosts.cpp'),'rebuilt_sha256':sha(P/'rebuilt-hosts.dylib'),
     'scope':'Four fixed assignments and limit/input controls only; no whole capped input restarted.'}
(P/'build-results.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(results))
