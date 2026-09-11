from pathlib import Path
import json,hashlib
s=Path('/tmp/erdos85-sol1-q9-elementary-nine-square-obstruction');p=Path(__file__).resolve().parent
for f,h in json.loads((s/'pins.json').read_text()).items():assert hashlib.sha256((s/f).read_bytes()).hexdigest()==h
r=json.loads((p.parent/'review-2215/results.json').read_text());F,S,T=(r[k] for k in ('F','S','T'))
def factors(n):
 out={};d=2
 while d*d<=n:
  while n%d==0:out[d]=out.get(d,0)+1;n//=d
  d+=1
 if n>1:out[n]=out.get(n,0)+1
 return out
def odd(n):return frozenset(q for q,e in factors(n).items() if e%2)
unique={1911:13,2751:131,4221:67,5700:19,6060:101,8700:29}
for t,q in unique.items():assert factors(t)[q]%2 and all(f%q and s%q for f in F for s in S)
assert {odd(f) for f in F}.isdisjoint({odd(s*t) for s in S for t in (2940,3960)})
assert all(odd(f*s*t) for f in F for s in S for t in T)
out={'status':'PASS','factorizations':{str(n):factors(n) for n in F+S+T},'all128_products_have_odd_prime_exponent':True,'unique_prime_checks':unique};(p/'results.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS128 products and all unique-prime/squarefree arguments')
