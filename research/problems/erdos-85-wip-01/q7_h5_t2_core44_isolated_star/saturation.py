"""Audit forced internal F-star edge in the no-C/F-sharing case."""
from pathlib import Path
import itertools,json
possible=[(0,1),(0,3),(1,3)];survivors=[]
for bits in range(8):
 edges=[e for i,e in enumerate(possible) if bits>>i&1];degree=[sum(v in e for e in edges) for v in range(5)]
 if max(degree)>1 or degree[1]!=1 or degree[3]!=1:continue
 survivors.append(edges)
assert survivors==[[(1,3)]]
r={'scope':'No-C/F-sharing branch only. All F-singletons require colours0/1/3; colour1/3 singleton classes have exactly5 vertices and demands saturate injectively. C4 makes the induced F-neighbour graph a matching.','possible_internal_edges':possible,'forced_internal_edges':survivors[0],'colour0_targets':'Exactly the five colour0 singletons other than f0.','status':'NECESSARY_CONDITIONAL_LEMMA','not_claimed':'No exclusion of core44; shared f1/f2 branches and remaining edges unresolved.'};Path(__file__).with_name('saturation-results.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
