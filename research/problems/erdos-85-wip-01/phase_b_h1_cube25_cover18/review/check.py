from pathlib import Path
import hashlib, json, time
P=Path(__file__).parent
A=Path('/Users/rwalters/lean-genius-h1-cube25-cover18-sol2-20260916')
R=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01')
sha=lambda b:hashlib.sha256(b).hexdigest()
start=time.monotonic()
for name,pin in json.loads((A/'pins.json').read_text()).items():
    raw=(A/name).read_bytes()
    assert len(raw)==pin['bytes'] and sha(raw)==pin['sha256']
launch=json.loads((A/'launch.json').read_text())
t=(R/'phase_b_h1_cube25_cnf_cover/author/clause-certificate.json').read_bytes()
b=(R/'phase_b_h1_cube25_cover/binding-results.json').read_bytes()
assert sha(t)==launch['template_sha256'] and sha(b)==launch['bindings_sha256']
req={}
for c in json.loads(t)['certificates']:
    for offset,clause in enumerate(c['counter_clauses']):
        i=c['counter_start_clause']+offset
        assert i not in req
        req[i]=tuple(clause)
    for item in c['block_clauses']:
        assert item['index'] not in req
        req[item['index']]=tuple(item['clause'])
assert len(req)==660
rows=json.loads(b)['results']; reported=json.loads((A/'results.json').read_text())
bytag={r['tag']:r for r in reported['results']}
assert len(rows)==len(bytag)==18 and {r['tag'] for r in rows}==set(bytag)
checked=[]
for row in rows:
    assert time.monotonic()-start<60
    path=Path(row['cube_path']); raw=path.read_bytes()
    assert sha(raw)==row['cube_sha256']
    header,body=raw.split(b'\n',1); _,_,nv,nc=header.split();nv=int(nv);nc=int(nc)
    assert header.startswith(b'p cnf ') and body.endswith(b'301 0\n456 0\n')
    basebody=body[:-len(b'301 0\n456 0\n')]
    basehash=sha(f'p cnf {nv} {nc-2}\n'.encode()+basebody)
    assert basehash==row['frozen_base_sha256']
    count=0; found=0
    for count,line in enumerate(basebody.splitlines(),1):
        if count in req:
            tokens=tuple(map(int,line.split()))
            assert tokens[-1]==0 and tokens[:-1]==req[count]
            assert all(0<abs(v)<=nv for v in tokens[:-1])
            found+=1
    assert count==nc-2 and found==660
    result=bytag[row['tag']]
    assert result['cube_path']==str(path) and result['cube_sha256']==sha(raw)
    assert result['base_sha256']==basehash and result['base_variables']==nv
    assert result['base_clauses']==count and result['required_clauses_checked']==found
    checked.append(row['tag'])
assert reported['count']==18 and reported['required_occurrences']==11880
out={'status':'PASS','tags':checked,'occurrences':11880,'seconds':time.monotonic()-start,
     'limit_seconds':60,'author_pins':4,'scope':'Exact 18 c0/base identities and clause containment. Semantics inherited from 2723; other cube joins inherited from 2019. No proof verification or new exclusion.'}
(P/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
