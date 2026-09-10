import collections,itertools,json,hashlib
from pathlib import Path
p=Path(__file__).parent;d=json.loads((p/'full-results.json').read_text());edges=list(itertools.combinations(range(49),2));lex={e:i+1 for i,e in enumerate(edges)};old=list(itertools.combinations(range(3),2))+[(h,l) for l in range(3,49) for h in range(3)]+list(itertools.combinations(range(3,49),2));idmap={i+1:lex[e] for i,e in enumerate(old)}
def boundary(path,pins,renumber):
 fixed=[];tail=collections.deque(maxlen=138);middle=hashlib.sha256()
 with Path(path).open() as f:
  next(f)
  for i,line in enumerate(f):
   x=[int(t) for t in line.split()][:-1]
   if renumber:x=[(1 if t>0 else -1)*idmap.get(abs(t),abs(t)) for t in x]
   if i<141:fixed.append(x)
   elif i<141+pins:continue
   elif i<141+pins+1327904:middle.update((json.dumps(x)+'\n').encode())
   else:tail.append(x)
 return fixed,list(tail),middle.hexdigest()
results=[]
for r in d['results']:
 a,at,am=boundary(r['python_cnf'],0,True);b,bt,bm=boundary(r['lean_scout_cnf'],r['geometry_clauses_removed'],False);assert am==bm
 def supports(fixed):
  out={v:[] for v in range(3,49)}
  for clause in fixed:
   assert len(clause)==1
   if clause[0]>0:
    h,l=edges[clause[0]-1];assert h<3<=l;out[l].append(h)
  return out
 sa,sb=supports(a),supports(b);ga=collections.defaultdict(list);gb=collections.defaultdict(list)
 for v,s in sa.items():ga[tuple(s)].append(v)
 for v,s in sb.items():gb[tuple(s)].append(v)
 assert {s:len(v) for s,v in ga.items()}=={s:len(v) for s,v in gb.items()}
 perm={i:i for i in range(3)}
 for support,vs in ga.items():perm.update(zip(vs,gb[support],strict=True))
 assert set(perm)==set(perm.values())==set(range(49))
 def transform(clause):
  return tuple(sorted((1 if t>0 else -1)*lex[tuple(sorted((perm[edges[abs(t)-1][0]],perm[edges[abs(t)-1][1]])))] for t in clause))
 assert collections.Counter(map(transform,a))==collections.Counter(tuple(sorted(x)) for x in b)
 assert collections.Counter(map(transform,at))==collections.Counter(tuple(sorted(x)) for x in bt)
 out={'profile':r['profile'],'vertex_permutation':perm,'support_counts':{str(k):len(v) for k,v in ga.items()},'fixed_clause_multisets_match_under_vertex_permutation':True,'partition_clause_multisets_match_under_vertex_permutation':True,'c4_degree_block_identical_before_vertex_permutation':am,'scope':'Fixed/partition clauses match via a low-vertex relabeling. C4 and exact-degree predicates are invariant under that relabeling; auxiliary-counter clauses were compared before vertex relabeling, not claimed byte-identical afterward.'};results.append(out);print(json.dumps(out))
(p/'support-results.json').write_text(json.dumps({'results':results,'solver_launched':False},indent=2)+'\n')
