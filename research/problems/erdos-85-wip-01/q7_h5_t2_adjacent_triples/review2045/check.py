from pathlib import Path
import itertools,json,hashlib
src=Path('/Users/rwalters/lean-genius-erdos85-goal48-sol3/t2-adjacent-triples-exclusion');pins=json.loads((src/'PINS.json').read_text())
for n,h in pins.items():assert hashlib.sha256((src/n).read_bytes()).hexdigest()==h
S=[{0,1,2},{0,3,4},{1,3},{1,4},{2,3},{2,4}]
for triple in [0,1]:
 assert not any(not(S[triple]&S[i]) for i in range(6) if i!=triple)
 other=1-triple;assert [i for i in range(6) if i!=triple and not(S[i]&S[other])]==[]
# Distinct direct enumeration using the forced empty rows rather than B-special rows.
W=set(range(10));EA=set(range(4));patterns=0;partitions=0;passing=0
for eb in itertools.combinations(W,4):
 EB=set(eb)
 if len(EA&EB)>1:continue
 patterns+=1;UB=W-EB;assert len(EA&UB)>=3
 for l in itertools.combinations(UB,3):
  L=set(l);R=UB-L;partitions+=1
  assert len(EA&L)+len(EA&R)==len(EA&UB)
  if len(EA&L)<=1 and len(EA&R)<=1:passing+=1
assert passing==0
base=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration/research/problems/erdos-85-wip-01/q7_h5_heavy_core/core-t2.json');raw=base.read_bytes();c=json.loads(raw);assert c['masks']==[sum(1<<i for i in s) for s in S]
for core in [1537,6145,9217,9729]:
 assert core in c['canonical_cores'];edges=[e for i,e in enumerate(itertools.combinations(range(6),2)) if core>>i&1];assert (0,1) in edges
 assert sum(0 in e for e in edges)==sum(1 in e for e in edges)==1
r={'status':'PASS','source_pins':pins,'canonical_core_sha256':hashlib.sha256(raw).hexdigest(),'empty_row_pairs_checked':patterns,'special_partitions_checked':partitions,'survivors':passing,'argument':'Forced rows EA and EB each have size4 and intersect in at most1, so EA meets W\\EB=UB in at least3. But UB is the disjoint union of the two B-special neighbourhoods, each meeting EA in at most1; hence at most2. Contradiction.','premise_audit':'Adjacent triples force one-heavy neighbours; each triple has two special singletons and one empty. Specials have exactly one heavy, two singletons, three empties. Own-side empty-special edges repeat a high colour and opposite-side edges close a length3path; special empty sets lie in W and are disjoint within each side. Triple empty rows have degree4 and are forced complements.','scope':'All adjacent-triple T2 graphs excluded under reviewed support/BC/degree premises, covering four remaining core IDs. Core44 remains open. No kernel theorem, queue change or cap retry.'}
Path(__file__).with_name('REVIEW2045.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
