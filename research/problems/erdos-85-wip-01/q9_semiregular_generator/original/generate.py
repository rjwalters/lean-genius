"""Exact CNF for C4-free graphs invariant under a free cyclic action."""
import argparse, collections, hashlib, json
from pathlib import Path

class CNF:
    def __init__(self):
        self.nvars=1; self.clauses=[(1,)]; self.gates=[]; self.cache={}
    def var(self):
        self.nvars+=1; return self.nvars
    def add(self,*lits):
        self.clauses.append(tuple(lits))
    def AND(self,a,b):
        if a==1: return b
        if b==1: return a
        if a==-1 or b==-1 or a==-b: return -1
        if a==b: return a
        key=tuple(sorted((a,b)))
        if key in self.cache: return self.cache[key]
        z=self.var(); self.cache[key]=z; self.gates.append((z,a,b))
        self.add(-z,a); self.add(-z,b); self.add(z,-a,-b)
        return z
    def OR(self,a,b): return -self.AND(-a,-b)
    def amo(self,lits):
        # Distinct common neighbours can give the same Boolean conjunction.
        # Such a repeated conjunction MUST be false, not deduplicated away.
        counts=collections.Counter(lits)
        for x,n in counts.items():
            if n>1: self.add(-x)
        unique=[x for x,n in counts.items() if n==1]
        seen=-1
        for x in unique:
            self.add(-seen,-x)
            seen=self.OR(seen,x)
    def at_least(self,lits,d):
        # Repetition intentionally implements weights, including antipodal orbits.
        prev=[1]+[-1]*d
        for x in lits:
            prev=[1]+[self.OR(prev[j],self.AND(x,prev[j-1])) for j in range(1,d+1)]
        self.add(prev[d])
    def extension(self,edges):
        values={1:True,**edges}
        def val(x): return values[abs(x)] == (x>0)
        for z,a,b in self.gates: values[z]=val(a) and val(b)
        return values

def build(n,m,d):
    if n<1 or m<1 or n%m or not 0<=d<n: raise ValueError('need m|n, m>=1, 0<=d<n')
    k=n//m; c=CNF(); orbits=[]; edge={}; degree=[[] for _ in range(k)]
    for a in range(k):
        for b in range(a,k):
            shifts=range(1,m//2+1) if a==b else range(m)
            for shift in shifts:
                v=c.var()
                pairs=sorted({tuple(sorted((a*m+t,b*m+(t+shift)%m))) for t in range(m)})
                assert all(u!=w for u,w in pairs)
                for pair in pairs:
                    assert pair not in edge
                    edge[pair]=v
                orbits.append({'var':v,'blocks':[a,b],'shift':shift,'edges':pairs})
                if a!=b: degree[a].append(v);degree[b].append(v)
                else: degree[a].extend([v]*(1 if 2*shift==m else 2))
    assert len(edge)==n*(n-1)//2
    for o in orbits:
        u,v=o['edges'][0]
        common=[c.AND(edge[tuple(sorted((u,w)))],edge[tuple(sorted((v,w)))]) for w in range(n) if w!=u and w!=v]
        c.amo(common)
    for row in degree: c.at_least(row,d)
    return c,{'schema':1,'n':n,'m':m,'minimum_degree':d,'vertex_label':'block*m+residue','orbits':orbits,'variables':c.nvars,'clauses':len(c.clauses)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,required=True);ap.add_argument('--m',type=int,required=True);ap.add_argument('--d',type=int,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=False)
    c,meta=build(a.n,a.m,a.d)
    p=a.out/'graph.cnf'
    with p.open('w') as f:
        f.write(f'p cnf {c.nvars} {len(c.clauses)}\n')
        for clause in c.clauses: f.write(' '.join(map(str,clause))+' 0\n')
    meta['cnf_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
    meta['generator_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (a.out/'map.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({k:v for k,v in meta.items() if k!='orbits'}))
if __name__=='__main__': main()
