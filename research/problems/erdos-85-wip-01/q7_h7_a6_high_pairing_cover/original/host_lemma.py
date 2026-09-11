"""Finite algebra check of the empty-host star criterion and monotonicity."""
import itertools,json,pathlib,time
P=pathlib.Path(__file__).parent;start=time.monotonic();cases=extensions=0
for count in [2,3]:
 for forbidden in range(128):
  B={e for e in range(7) if forbidden>>e&1}
  for hs in itertools.product(range(8),repeat=count):
   cases+=1;assert cases<=100000 and time.monotonic()-start<60
   sets=[set() if h==0 else {h-1} for h in hs]
   direct=all(not ns&B for ns in sets) and all(not a&b for a,b in itertools.combinations(sets,2))
   used=0;fast=True
   for h in hs:
    mask=0 if not h else 1<<(h-1)
    if mask&(forbidden|used):fast=False;break
    used|=mask
   assert direct==fast
   if not fast:
    # Removing an assigned host is the reverse of the allowed refinement.
    # Check every one-host refinement cannot turn a false row into true.
    for i,h in enumerate(hs):
     if h:continue
     for e in range(7):
      nxt=list(sets);nxt[i]={e};extensions+=1
      assert not (all(not ns&B for ns in nxt) and all(not a&b for a,b in itertools.combinations(nxt,2)))
result=dict(status='PASS',cases=cases,one_host_refinements=extensions,seconds=time.monotonic()-start)
(P/'host-lemma-results.json').write_text(json.dumps(result,indent=2)+'\n');print(result)
