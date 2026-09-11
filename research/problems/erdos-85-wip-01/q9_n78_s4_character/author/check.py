from pathlib import Path
import json,time,hashlib
p=Path(__file__).parent
source=Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json')
g=next(g for g in json.loads(source.read_text()) if g['name']=='S4')
m=g['multiplication'];n=24;cap=30.;start=time.monotonic()
def tick():
    if time.monotonic()-start>=cap:raise TimeoutError
inv=[next(y for y in range(n) if m[x][y]==0) for x in range(n)]
orders=[]
for x in range(n):
    y=x;k=1
    while y:y=m[y][x];k+=1
    orders.append(k)
classes=[];unseen=set(range(n))
while unseen:
    x=min(unseen);C=sorted({m[m[a][x]][inv[a]] for a in range(n)})
    classes.append(C);unseen-=set(C)
reps=[C[0] for C in classes]
subgroups={frozenset([0])};queue=list(subgroups);solutions=[];chars={};nodes=0
try:
    for H in queue:
        for x in range(n):
            tick()
            if x in H:continue
            gens=list(H)+[x];K={0};todo=[0]
            for a in todo:
                for b in gens:
                    c=m[a][b]
                    if c not in K:K.add(c);todo.append(c)
                if len(K)>8:break
            if len(K)>8:continue
            assert len(K) in (1,2,3,4,6,8)
            K=frozenset(K)
            if K not in subgroups:subgroups.add(K);queue.append(K)
    bounds=[78 if x==0 else 3 if orders[x]==3 else 6 for x in reps]
    for H in subgroups:
        counts=[sum(m[m[inv[a]][x]][a] in H for a in range(n)) for x in reps]
        assert all(c%len(H)==0 for c in counts)
        ch=tuple(c//len(H) for c in counts)
        if all(a<=b for a,b in zip(ch,bounds)):chars.setdefault(ch,[]).append(sorted(H))
    vectors=sorted(chars)
    def dfs(idx,left,total,chosen):
        global nodes
        tick();nodes+=1
        if left==0:
            if total[0]!=78:return
            for i,x in enumerate(reps):
                if orders[x]==3 and total[i] not in (0,3):return
                if orders[x] in (2,4) and total[i] not in (0,2,4,6):return
            solutions.append({'indices':chosen,'fixed_counts':total,'sizes':[vectors[j][0] for j in chosen]})
            return
        for j in range(idx,len(vectors)):
            ch=vectors[j]
            if total[0]+left*ch[0]>78 or total[0]+left*vectors[-1][0]<78:continue
            nxt=tuple(a+b for a,b in zip(ch,total))
            if all(a<=b for a,b in zip(nxt,bounds)):dfs(j,left-1,nxt,chosen+[j])
    completed=[]
    for orbit_count in (7,8):
        dfs(0,orbit_count,(0,)*len(classes),[]);completed.append(orbit_count)
    status='COMPLETE'
except TimeoutError:
    status='UNKNOWN'
out={'status':status,'cap_seconds':cap,'elapsed_seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'classes':classes,'class_orders':[orders[x] for x in reps],'subgroups':len(subgroups),'characters':[{'values':v,'subgroups':chars[v]} for v in sorted(chars)],'nodes':nodes,'solutions':solutions}
(p/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':status,'elapsed':out['elapsed_seconds'],'subgroups':len(subgroups),'characters':len(chars),'nodes':nodes,'solutions':len(solutions),'patterns':sorted(set(tuple(s['sizes']) for s in solutions))}))
