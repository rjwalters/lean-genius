"""Independently check the single final H7 coverage-map change."""
import argparse,hashlib,itertools,json,sqlite3,subprocess
from pathlib import Path
W=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration')
BASE='research/problems/erdos-85-wip-01/'
PREVIOUS=BASE+'h7-frontier-map-20260915/overlay-a6f12-20260915/author/results.json'
SOURCE=BASE+'q7_h7_a6_high_pairing_cover/original/source-cover-results.json'
def main():
 parser=argparse.ArgumentParser();parser.add_argument('packet',type=Path);args=parser.parse_args();p=args.packet
 pins=json.loads((p/'pins.json').read_text())
 for n,h in pins.items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h,n
 previous=subprocess.check_output(['git','show','97ec983fce:'+PREVIOUS],cwd=W);old=json.loads(previous)
 new=json.loads((p/'results.json').read_text());a={r['id']:r for r in old['rows']};b={r['id']:r for r in new['rows']}
 assert len(a)==len(b)==28 and set(a)==set(b)
 changed=[]
 for rid,x in a.items():
  y=b[rid]
  for field in ['id','edge_count','mask','cnf_sha256']:assert x[field]==y[field],(rid,field)
  if x!=y:changed.append(rid)
 assert changed==['cube_F6_t18'],changed
 row=b[changed[0]];assert row['review_id']==2718 and row['scope']=='F14'
 perm=row['parent_to_reviewed_shape'];assert sorted(perm)==list(range(7))
 source=json.loads((W/SOURCE).read_text());F=next(x for x in source['cases'] if x['F_index']==14)
 edges=list(itertools.combinations(range(7),2));image={tuple(sorted((perm[u],perm[v]))) for i,(u,v) in enumerate(edges) if row['mask']>>i&1}
 assert image==set(map(tuple,F['F_edges']))
 assert all(r['review_id'] is not None for r in b.values())
 db=sqlite3.connect('file:/Users/rwalters/GitHub/lean-genius/.squad/squad.db?mode=ro',uri=True)
 for rid in {r['review_id'] for r in b.values()}:
  st,res=db.execute('select status,resolution from review_requests where id=?',(rid,)).fetchone();assert st=='resolved' and res.startswith('PASS'),rid
 result={'status':'PASS_EXACT_FINAL_OVERLAY','rows':28,'changed':changed,'review':2718,'parent_to_source':perm,'previous_sha256':hashlib.sha256(previous).hexdigest(),'packet_pins_sha256':hashlib.sha256((p/'pins.json').read_bytes()).hexdigest(),'scope':'Exact selected structural scope join; no new certificate replay, arbitrary CNF UNSAT, Lean or global proof.'}
 (Path(__file__).parent/'REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
