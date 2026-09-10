from pathlib import Path
import json,hashlib
p=Path(__file__).parent;ns={'__file__':str(p/'survey.py')};exec((p/'survey.py').read_text().split('results=[]')[0],ns)
rows=json.loads((p/'witnesses.json').read_text())['pairs'];audited=[]
for row in rows:
 r,q=row['pair'];a,b,c=[x[r] for x in ns['arrays']];assert row['compact']==[a,b,c]
 U=ns['u'].adjacency(ns['u'].MASKS[a],ns['u'].MASKS[b],ns['perms'][c],None);m,a,b,far=ns['codes'][q];assert row['r_code']==[m,a,b,far]
 R=[0]*8;edges=[(2*i,2*i+1) for i in range(m+1)]+([(6,a-1)] if a else [])+([(7,b-1)] if b else [])+([(6,7)] if far else [])
 for x,y in edges:R[x]|=1<<y;R[y]|=1<<x
 fixed=U+[x<<15 for x in R]+[0]
 for j in range(6):fixed[23]|=1<<(15+j);fixed[15+j]|=1<<23
 D=[[S for S in ns['candidates'] if len(S)==4-R[j].bit_count()-(j<6) and not ns['c4'](ns['add'](fixed,j,S))] for j in range(8)]
 assert list(map(len,D))==row['domain_sizes']
 w=row['witness'];S={i for i in range(15) if w['mask']>>i&1}
 # Direct set-intersection maxima, independent of subset-zeta implementation.
 caps=[max(len(S.intersection(T)) for T in ds) for ds in D]
 demand=sum(4-U[i].bit_count() for i in S)
 assert caps==w['caps'] and demand==w['demand'] and demand>sum(caps)
 audited.append({'pair':[r,q],'subset':sorted(S),'demand':demand,'caps':caps,'deficit':demand-sum(caps)})
(p/'DIRECT_AUDIT.json').write_text(json.dumps({'scope':'Direct numerical witness audit; Lean certificate still required','witnesses_sha256':hashlib.sha256((p/'witnesses.json').read_bytes()).hexdigest(),'count':len(audited),'results':audited},indent=2)+'\n');print('Direct maxima audit PASS',len(audited))
