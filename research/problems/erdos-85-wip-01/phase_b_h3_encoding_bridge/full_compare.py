import hashlib,itertools,json,time
from pathlib import Path
root=Path('/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49')
lex={e:i+1 for i,e in enumerate(itertools.combinations(range(49),2))}
old=list(itertools.combinations(range(3),2))+[(h,l) for l in range(3,49) for h in range(3)]+list(itertools.combinations(range(3,49),2))
assert len(set(old))==1176
mapping={i+1:lex[e] for i,e in enumerate(old)}
def lit(x):return (1 if x>0 else -1)*mapping.get(abs(x),abs(x)) if x else 0
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for x in iter(lambda:f.read(1048576),b''):h.update(x)
 return h.hexdigest()
results=[]
for profile,scout,pins in [(0,'h3_b1',84),(1,'h3_dist2',108)]:
 a=root/f'small-high-canonical-audit/h3_t{profile}.base.cnf';b=root/f'campaign-20260825.noindex/small-high-base-freight-38b15d484b/{scout}.cnf'
 start=time.monotonic();count=0;differences=[];geometry=[]
 with a.open() as aa,b.open() as bb:
  headers=[aa.readline().strip(),bb.readline().strip()]
  for i,line in enumerate(aa):
   if i==141:geometry=[next(bb).strip() for _ in range(pins)]
   x=[lit(int(t)) for t in line.split()];y=[int(t) for t in next(bb).split()]
   if x!=y:
    if len(differences)<4:differences.append({'clause_index':i,'python_after_edge_permutation':x,'lean':y})
   else:count+=1
  trailing=bb.read()
 out={'profile':profile,'python_cnf':str(a),'python_sha256':sha(a),'lean_scout_cnf':str(b),'lean_scout_sha256':sha(b),'headers':headers,'matching_clauses':count,'total_clauses':i+1,'geometry_clauses_removed':pins,'geometry_sha256':hashlib.sha256(('\n'.join(geometry)+'\n').encode()).hexdigest(),'first_differences':differences,'trailing_scout_data':bool(trailing),'seconds':time.monotonic()-start,'scope':'Full DIMACS clause comparison after a bijective edge-ID permutation and removal of explicitly located scout geometry clauses. Auxiliary IDs unchanged. This is empirical input equivalence, not a Lean kernel theorem or solver verdict.'};results.append(out);print(json.dumps(out),flush=True)
Path(__file__).with_name('full-results.json').write_text(json.dumps({'edge_permutation':mapping,'results':results,'solver_launched':False},indent=2)+'\n')
