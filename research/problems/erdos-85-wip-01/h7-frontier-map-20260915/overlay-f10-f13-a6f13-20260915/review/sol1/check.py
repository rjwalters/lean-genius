import hashlib,json,sqlite3,subprocess
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-frontier-overlay-f10-f13-a6f13-sol2-20260915');O=Path(__file__).parent
repo=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in read(P/'pins.json').items():assert sha(P/n)==h
for n,r in read(P/'provenance.json')['inputs'].items():
    assert sha(P/n)==r['sha256']
    if 'revision' in r:
        assert subprocess.check_output(['git','show',r['revision']+':'+r['path']],cwd=repo)==(P/n).read_bytes()
    elif r.get('path','').startswith('/'):
        assert (P/n).read_bytes()==Path(r['path']).read_bytes()
c=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True);c.row_factory=sqlite3.Row
for rid in (2695,2697,2696):
    live=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone())
    live['refs']=json.loads(live['refs'])
    saved=read(P/f'review-{rid}.json')
    if isinstance(saved['refs'],str):saved['refs']=json.loads(saved['refs'])
    assert saved==live
subprocess.run(['python3',str(P/'check.py')],check=True)
a=read(P/'previous-map.json');b=read(P/'results.json')
old={r['id']:r for r in a['rows']};new={r['id']:r for r in b['rows']}
assert set(old)==set(new) and len(new)==28
changes={k for k in old if old[k]!=new[k]};assert changes=={'cube_F7_t10','cube_F7_t13','cube_F6_t8'}
for k in old:
    assert old[k]['cnf_sha256']==new[k]['cnf_sha256'] and old[k]['mask']==new[k]['mask']
    if k in changes:
        assert new[k]['review_id']=={'cube_F7_t10':2695,'cube_F7_t13':2697,'cube_F6_t8':2696}[k]
        assert new[k]['parent_to_reviewed_shape']==([3,0,1,2,6,5,4] if k=='cube_F6_t8' else list(range(7)))
assert set(b['covered'])==set(a['covered'])|changes
assert set(b['residual'])==set(a['residual'])-changes
assert b['counts']=={'total':28,'covered':24,'residual':4}
out={'status':'PASS_REVIEW2700','delta':sorted(changes),'counts':b['counts'],'remaining':b['residual'],'source_manifest_sha256':sha(P/'pins.json'),'checks':'All pins, committed previous map, exact live review snapshots and source mappings, three-row delta and unchanged root/CNF identities; producer checker reproduced.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
