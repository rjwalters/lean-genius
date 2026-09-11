import json, time, pathlib, hashlib
P=pathlib.Path(__file__).parent
SOURCE=pathlib.Path('/tmp/erdos85-sol1-q9-n78-four-orbit-order24-parameters/groups.json')
CAP=30.0
start=time.monotonic()
def tick():
    if time.monotonic()-start>CAP: raise TimeoutError
groups=json.loads(SOURCE.read_text())[:22]
results=[]
try:
    for group in groups:
        tick()
        m=group['multiplication']; n=len(m)
        assert n==24 and m[0]==list(range(n))
        inv=[next(y for y in range(n) if m[x][y]==0) for x in range(n)]
        orders=[]
        for x in range(n):
            y=x;k=1
            while y: y=m[y][x];k+=1
            orders.append(k)
        # Every subgroup of 2-power order at most eight, by adjoining one element.
        subgroups={frozenset([0])}; queue=list(subgroups)
        for H in queue:
            for x in range(n):
                tick()
                if x in H or orders[x]%3==0: continue
                gens=list(H)+[x]; K={0}; todo=[0]
                for a in todo:
                    for b in gens:
                        c=m[a][b]
                        if c not in K: K.add(c);todo.append(c)
                    if len(K)>8: break
                if len(K)>8 or len(K) not in (1,2,4,8): continue
                K=frozenset(K)
                if K not in subgroups: subgroups.add(K);queue.append(K)
        target=tuple(78 if x==0 else 0 if orders[x]%3==0 else 6 for x in range(n))
        # Formula for fixed left cosets: |{a:a^-1*x*a in H}| / |H|.
        chars={}
        for H in subgroups:
            counts=[sum(m[m[inv[a]][x]][a] in H for a in range(n)) for x in range(n)]
            assert all(c%len(H)==0 for c in counts)
            ch=tuple(c//len(H) for c in counts)
            if all(a<=b for a,b in zip(ch,target)): chars.setdefault(ch,[]).append(sorted(H))
        vectors=sorted(chars); solutions=[]; nodes=[0]
        def dfs(idx,left,remaining,chosen):
            tick();nodes[0]+=1
            if left==0:
                if not any(remaining):solutions.append(list(chosen))
                return
            for j in range(idx,len(vectors)):
                ch=vectors[j]
                if ch[0]*left>remaining[0] or vectors[-1][0]*left<remaining[0]: continue
                if all(a<=b for a,b in zip(ch,remaining)):
                    dfs(j,left-1,tuple(b-a for a,b in zip(ch,remaining)),chosen+[j])
        dfs(0,7,target,[])
        results.append({'name':group['name'],'subgroups':len(subgroups),'characters':[{'values':list(ch),'subgroups':chars[ch]} for ch in vectors], 'solutions':solutions,'nodes':nodes[0],'status':'COMPLETE'})
    status='COMPLETE'
except TimeoutError:
    status='UNKNOWN'
out={'status':status,'cap_seconds':CAP,'elapsed_seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'groups':results,'completed_groups':len(results),'uncompleted_groups':22-len(results)}
(P/'results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':status,'elapsed':out['elapsed_seconds'],'groups':[(g['name'],g['subgroups'],len(g['characters']),len(g['solutions'])) for g in results]}))
