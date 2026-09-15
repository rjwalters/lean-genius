#!/usr/bin/env python3
import json, hashlib
from pathlib import Path

class CNF:
    def __init__(self,n):
        self.n=n; self.clauses=[]; self.gates=[]
    def add(self,*lits):
        if any(x is True for x in lits): return
        lits=list(dict.fromkeys(x for x in lits if x is not False))
        if any(-x in lits for x in lits): return
        self.clauses.append(lits)
    def new(self):
        self.n+=1; return self.n
    @staticmethod
    def neg(x): return not x if isinstance(x,bool) else -x
    def conjunction(self,a,b):
        if a==b:return a
        y=self.new();self.add(-y,a);self.add(-y,b);self.add(y,-a,-b)
        self.gates.append([y,'and',a,b]);return y
    def threshold(self,a,b,x):
        y=self.new();neg=self.neg
        self.add(neg(a),y);self.add(neg(b),-x,y)
        self.add(-y,a,b);self.add(-y,a,x)
        self.gates.append([y,'threshold',a,b,x]);return y
    def amo(self,items):
        if not items:return
        prev=items[0]
        for x in items[1:]:
            self.add(-prev,-x)
            y=self.new();self.add(-prev,y);self.add(-x,y);self.add(-y,prev,x)
            self.gates.append([y,'or',prev,x]);prev=y

def encode(data,q):
    n=data['order']; t=data['table'];inv=data['inverse'];c=CNF(n-1)
    assert data['identity']==0 and len(t)==n and all(len(r)==n for r in t)
    assert t[0]==list(range(n)) and [r[0] for r in t]==list(range(n))
    assert all(t[a][inv[a]]==t[inv[a]][a]==0 for a in range(n))
    for a in range(1,n):
        c.add(-a,inv[a]);c.add(a,-inv[a])
    prev=[True]+[False]*(q+1)
    for a in range(1,n):
        prev=[True]+[c.threshold(prev[k],prev[k-1],a) for k in range(1,q+2)]
    c.add(prev[q]);c.add(-prev[q+1])
    for h in range(1,n):
        pairs=[]
        for a in range(1,n):
            b=t[inv[a]][h]
            if b: pairs.append(c.conjunction(a,b))
        c.amo(pairs)
    return c

def main():
    root=Path(__file__).resolve().parent
    manifest={'image':'gapsystem/gap-docker@sha256:d66dca500c3d8b8ca88824d3c3c7315183335af029f6b74ce592ed0d148edaee','groups':[]}
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    for n,q,count in [(48,7,52),(80,9,52),(120,11,47),(168,13,57)]:
        for i in range(1,count+1):
            src=root/'groups'/f'{n}-{i}.json';data=json.loads(src.read_text())
            assert data['small_group_id']==[n,i]
            c=encode(data,q);out=root/'instances'/f'{n}-{i}';out.mkdir(parents=True,exist_ok=True)
            cnf=out/'input.cnf'
            with cnf.open('w') as f:
                f.write(f'p cnf {c.n} {len(c.clauses)}\n')
                for row in c.clauses:f.write(' '.join(map(str,row))+' 0\n')
            m=out/'map.json';m.write_text(json.dumps({'small_group_id':[n,i],'q':q,'identity':0,'selection_variables':{str(a):a for a in range(1,n)},'group_sha256':sha(src),'variables':c.n,'clauses':len(c.clauses),'gates':c.gates},separators=(',',':'))+'\n')
            manifest['groups'].append({'small_group_id':[n,i],'q':q,'structure':data['structure'],'group':str(src.relative_to(root)),'group_sha256':sha(src),'cnf':str(cnf.relative_to(root)),'cnf_sha256':sha(cnf),'map':str(m.relative_to(root)),'map_sha256':sha(m),'variables':c.n,'clauses':len(c.clauses)})
    manifest['encoder_sha256']=sha(Path(__file__))
    manifest['exporter_sha256']=sha(root/'export.g')
    (root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('Encoded',len(manifest['groups']),'groups')

if __name__=='__main__':main()
