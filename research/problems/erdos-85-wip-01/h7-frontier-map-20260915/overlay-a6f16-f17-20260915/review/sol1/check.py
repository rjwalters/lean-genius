import hashlib,json,sqlite3,subprocess
from pathlib import Path
P=Path('/Users/rwalters/lean-genius-h7-frontier-overlay-a6f16-f17-sol2-20260915');O=Path(__file__).parent
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
for rid in (2704,2709):
    live=dict(c.execute('select * from review_requests where id=?',(rid,)).fetchone())
    live['refs']=json.loads(live['refs'])
    saved=read(P/f'review-{rid}.json')
    if isinstance(saved['refs'],str):saved['refs']=json.loads(saved['refs'])
    assert saved==live
subprocess.run(['python3',str(P/'check.py')],check=True)
a=read(P/'previous-map.json');b=read(P/'results.json')
old={r['id']:r for r in a['rows']};new={r['id']:r for r in b['rows']}
assert set(old)==set(new) and len(new)==28
changes={k for k in old if old[k]!=new[k]};assert changes=={'cube_F6_t15','cube_F6_t5'}
for k in old:
    assert old[k]['cnf_sha256']==new[k]['cnf_sha256'] and old[k]['mask']==new[k]['mask']
    if k in changes:
        assert new[k]['review_id']=={'cube_F6_t15':2704,'cube_F6_t5':2709}[k]
        assert new[k]['parent_to_reviewed_shape']==([2,3,4,0,1,6,5] if k=='cube_F6_t15' else [2,3,4,0,6,1,5])
assert set(b['covered'])==set(a['covered'])|changes
assert set(b['residual'])==set(a['residual'])-changes
assert b['counts']=={'total':28,'covered':26,'residual':2}
src=read(repo/'research/problems/erdos-85-wip-01/q7_h7_a6_high_pairing_cover/original/source-cover-results.json')
for fi in [16,17]:
    m=read(P/f'f{fi}-map.json');assert m['source_edges']==next(x for x in src['cases'] if x['F_index']==fi)['F_edges']
out={'status':'PASS_REVIEW2710','delta':sorted(changes),'counts':b['counts'],'remaining':b['residual'],'source_manifest_sha256':sha(P/'pins.json'),'checks':'All pins, committed previous map, exact live review snapshots and source mappings, two-row delta and unchanged root/CNF identities; producer checker reproduced.'}
(O/'REVIEW.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
