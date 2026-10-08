"""Python mirror of the Lean H3 pair-cell engine (Erdos85H3PairEngine.lean).

Vertices: 0,1,2 high; 3,4,5 pair supports (masks 3,5,6); 6..23 singleton
supports (six per colour); 24..48 empty supports.  This is a prototype used to
size the Lean native_decide search; it is NOT a proof.
"""
import sys, time
from itertools import product,combinations
sys.setrecursionlimit(10000)
MASK=[0,0,0,3,5,6]+[1]*6+[2]*6+[4]*6+[0]*25
CAP=[8]*3+[7]*46
FIB=[[v for v in range(49) if MASK[v]>>w&1] for w in range(3)]
def col(v,w): return MASK[v]>>w&1
class S:
    __slots__=('rows','nbr')
    def __init__(s,rows,nbr): s.rows=rows; s.nbr=nbr
def init():
    rows=[0]*49; nbr=[[] for _ in range(49)]
    for v in range(3,49):
        for w in range(3):
            if col(v,w):
                rows[v]|=1<<w; rows[w]|=1<<v; nbr[v].append(w); nbr[w].append(v)
    return S(rows,nbr)
def allowed(s,u,x):
    if len(s.nbr[u])>=CAP[u] or len(s.nbr[x])>=CAP[x]: return False
    rx=s.rows[x]
    for y in s.nbr[u]:
        if s.rows[y]&rx: return False
    return True
def add(s,u,x):
    rows=s.rows[:]; nbr=s.nbr[:]
    rows[u]|=1<<x; rows[x]|=1<<u; nbr[u]=[x]+nbr[u]; nbr[x]=[u]+nbr[x]
    return S(rows,nbr)
def try_add(s,u,x):
    if u==x: return None
    if s.rows[u]>>x&1: return s
    if not allowed(s,u,x): return None
    return add(s,u,x)
stats={'n1':0,'leaf1':0,'n2':0,'leaf2':0,'n3':0,'found':0}
def find_clause(s):
    for u in range(3,24):
        for w in range(3):
            if all(not(s.rows[u]>>x&1) for x in FIB[w]): return (u,w)
    return None
def twin_skip(s,u,w,x):
    return any(y<x and y!=u and s.rows[y]==s.rows[x] and MASK[y]==MASK[x] for y in FIB[w])
ALL_TRIPLES=list(product(FIB[0],FIB[1],FIB[2]))
def dfs1(s):
    stats['n1']+=1
    c=find_clause(s)
    if c is None:
        stats['leaf1']+=1
        b=dict(stats); t1=time.time()
        r=dfs2(s,ALL_TRIPLES)
        print('core',stats['leaf1'],'n1',stats['n1'],'n2',stats['n2']-b['n2'],'leaf2',stats['leaf2']-b['leaf2'],'n3',stats['n3']-b['n3'],'secs',round(time.time()-t1,1),flush=True)
        return r
    u,w=c
    for x in FIB[w]:
        if x==u or twin_skip(s,u,w,x): continue
        t=try_add(s,u,x)
        if t is None: continue
        if not dfs1(t): return False
    return True
def insertable(s,t):
    a,b,c=t
    if len(s.nbr[a])>=7 or len(s.nbr[b])>=7 or len(s.nbr[c])>=7: return False
    if a!=b and s.rows[a]&s.rows[b]: return False
    if a!=c and s.rows[a]&s.rows[c]: return False
    if b!=c and s.rows[b]&s.rows[c]: return False
    return True
def contains(v,t):
    return all(t[w]==v for w in range(3) if col(v,w))
HEUR='count'
from math import comb
def dfs2(s,avail):
    stats['n2']+=1
    avail=[t for t in avail if insertable(s,t)]
    best=None
    for v in range(3,24):
        d=7-len(s.nbr[v])
        if d<=0: continue
        cnt=sum(1 for t in avail if contains(v,t))
        key=comb(cnt,d) if HEUR=='comb' else cnt
        if best is None or key<best[0]: best=(key,v)
    if best is None:
        stats['leaf2']+=1
        return dfs3(s)
    v=best[1]
    n=next((e for e in range(24,49) if s.rows[e]==0),None)
    if n is None: return True
    pre=[t for t in avail if not contains(v,t)]
    cs=[t for t in avail if contains(v,t)]
    for i,c in enumerate(cs):
        t=s
        for x in c:
            t=try_add(t,n,x)
            if t is None: break
        if t is None: continue
        if not dfs2(t,pre+cs[i:]): return False
    return True
def add_many(s,u,xs):
    for x in xs:
        s=try_add(s,u,x)
        if s is None: return None
    return s
def dfs3(s):
    stats['n3']+=1
    best=None
    for u in range(24,49):
        if len(s.nbr[u])>=7: continue
        cands=[x for x in range(49) if x!=u and not(s.rows[u]>>x&1) and allowed(s,u,x)]
        if len(s.nbr[u])+len(cands)<7: return True
        if best is None or len(cands)<len(best[1]): best=(u,cands)
    if best is None:
        stats['found']+=1
        return False
    u,cands=best
    for sub in combinations(cands,7-len(s.nbr[u])):
        t=add_many(s,u,sub)
        if t is None: continue
        if not dfs3(t): return False
    return True
if __name__=='__main__':
    if len(sys.argv)>1: HEUR=sys.argv[1]
    t0=time.time()
    T0=t0
    r=dfs1(init())
    print('rejected',r,stats,'secs',round(time.time()-t0,1),'heur',HEUR,flush=True)
