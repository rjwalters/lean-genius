"""Exact fixed-colouring singleton incidences under the reviewed2097 criterion."""
import itertools
K=list(itertools.combinations(range(7),2));pair_index={p:i for i,p in enumerate(K)}
def enumerate_incidences(phi,F):
 fg=[set() for _ in range(7)]
 for x,y in F:fg[x].add(y);fg[y].add(x)
 unused=[sorted(set(range(7))-{x for edge,x in phi.items() if i in edge}) for i in range(7)]
 assert len(phi)==14 and all(len(U)==3 for U in unused)
 pairs=[list(itertools.combinations(U,2)) for U in unused]
 options=[[(j,1<<pair_index[pair]) for j,pair in enumerate(row) if not fg[pair[0]]&fg[pair[1]]] for row in pairs]
 order=sorted(range(7),key=lambda i:(len(options[i]),i));answers=[];nodes=0
 def visit(k,used,code):
  nonlocal nodes
  nodes+=1
  if k==7:answers.append(code);return
  i=order[k]
  for j,bit in options[i]:
   if not used&bit:visit(k+1,used|bit,code|(j<<(2*i)))
 visit(0,0,0)
 return {'unused':unused,'pairs':pairs,'solutions':sorted(answers),'nodes':nodes}
