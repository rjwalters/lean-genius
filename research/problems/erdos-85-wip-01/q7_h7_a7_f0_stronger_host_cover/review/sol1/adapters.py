import ast,hashlib,itertools,json,time
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-f0-pairrow-sol2-20260915')
O=Path(__file__).parent
start=time.monotonic()
ns={}
exec(compile((P/'inputs.py').read_text(),str(P/'inputs.py'),'exec'),ns)
cover,cases,high=ns['load']()
a=ast.parse((P/'verify.py').read_text())
f=next(n for n in a.body if isinstance(n,ast.FunctionDef) and n.name=='graph')
vns={'cover':cover,'cases':cases,'high':high}
exec(compile(ast.Module(body=[f],type_ignores=[]),str(P/'verify.py'),'exec'),vns)
checked=0
for ci,row in enumerate(high):
    rep=cover['representatives'][row['source_index']]
    si,sj,edges=cases[ci]
    assert (si,sj)==(row['source_index'],row['singleton_index'])
    for pi,perm in enumerate(row['pairings']):
        pairs=set()
        def edge(u,v):pairs.add(tuple(sorted((u,v))))
        ren=lambda v:v+42 if v<7 else v
        for u,v in rep['F_edges']+edges:edge(ren(u),ren(v))
        for s,ee in enumerate(rep['singleton_hosts'],7):
            for e in ee:edge(s,e+42)
        for p,hh in enumerate(itertools.combinations(range(7),2),21):
            for h in hh:edge(p,h)
        for h,s in enumerate(perm):edge(h,14+h);edge(h,7+s)
        expected=[{v if u==i else u for u,v in pairs if i in (u,v)} for i in range(49)]
        assert expected==ns['graph'](cover,cases,high,ci,pi)==vns['graph'](ci,pi)
        checked+=1
assert checked==18408
out={'status':'PASS_ALL_INPUT_ADAPTERS','inputs':checked,'seconds':time.monotonic()-start,'pins':{str(P/n):hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ('inputs.py','verify.py')}}
(O/'adapters-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
