from pathlib import Path
import itertools as I,json,time
p=Path(__file__).parent;start=time.monotonic();cap=30
els=list(I.product(range(2),range(4),range(2)));perms=[tuple([z,1^z]+[2+(r+(-1 if s else 1)*v)%4 for v in range(4)]) for z,r,s in els];ix={x:i for i,x in enumerate(perms)}
M=[[ix[tuple(a[b[i]] for i in range(6))] for b in perms] for a in perms]
def closure(gens):
 group={0};todo=[0]
 while todo:
  x=todo.pop()
  for g in gens:
   y=M[x][g]
   if y not in group:group.add(y);todo.append(y)
 return frozenset(group)
subgroups={frozenset({0})};todo=list(subgroups)
while todo:
 if time.monotonic()-start>cap:raise TimeoutError('Original30s group-image cap')
 H=todo.pop()
 for g in set(range(16))-H:
  K=closure(list(H)+[g])
  if K not in subgroups:subgroups.add(K);todo.append(K)
models=[];excluded=[]
for H in sorted(subgroups,key=lambda h:(len(h),sorted(h))):
 if len(H) not in (4,8):continue
 if {perms[g][0] for g in H}!={0,1} or {perms[g][2] for g in H}!={2,3,4,5}:continue
 invswap=[g for g in H if g and M[g][g]==0 and perms[g][0]==1]
 r={'elements':sorted(H),'order':len(H),'involutions_swapping_two':invswap,'projection_four':sorted({(els[g][1],els[g][2]) for g in H})}
 if invswap:models.append(r)
 else:excluded.append(r)
r={'status':'COMPLETE','original_cap_seconds':cap,'seconds':time.monotonic()-start,'ambient_elements':els,'ambient_action':perms,'multiplication':M,'all_subgroups':[sorted(h) for h in sorted(subgroups,key=lambda h:(len(h),sorted(h)))],'models':models,'excluded_no_involution':excluded};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'seconds':r['seconds'],'subgroups':len(subgroups),'models':models,'excluded':excluded}))
