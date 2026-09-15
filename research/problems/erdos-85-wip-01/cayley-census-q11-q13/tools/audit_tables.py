#!/usr/bin/env python3
import json,hashlib,time
from pathlib import Path
import numpy as np
p=Path(__file__).resolve().parent
start=time.monotonic();manifest=json.loads((p/'manifest.json').read_text());rows=[]
for r in manifest['groups']:
 f=p/r['group'];assert hashlib.sha256(f.read_bytes()).hexdigest()==r['group_sha256']
 g=json.loads(f.read_text());n=g['order'];t=np.array(g['table'],dtype=np.int64); inv=np.array(g['inverse'],dtype=np.int64); e=np.arange(n)
 assert t.shape==(n,n) and np.all((t>=0)&(t<n))
 assert np.array_equal(t[0],e) and np.array_equal(t[:,0],e)
 assert np.all(np.sort(t,axis=1)==e) and np.all(np.sort(t,axis=0)==e[:,None])
 assert inv.shape==(n,) and np.all((inv>=0)&(inv<n))
 assert np.all(t[e,inv]==0) and np.all(t[inv,e]==0)
 for a in range(n):assert np.array_equal(t[t[a],:],t[a,t]),(r['small_group_id'],a)
 rows.append({'small_group_id':g['small_group_id'],'associativity_triples':n**3,'abelian':bool(np.array_equal(t,t.T)),'sha256':r['group_sha256']})
result={'status':'PASS','scope':'All multiplication tables: full associativity, Latin rows/columns, identity and inverses; group catalog identity supplied by pinned GAP export','groups':rows,'total_associativity_triples':sum(r['associativity_triples'] for r in rows),'wall_seconds':time.monotonic()-start,'numpy':np.__version__}
(p/'table-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='groups'})
print('abelian counts',{n:sum(r['abelian'] for r in rows if r['small_group_id'][0]==n) for n in [48,80,120,168]})
