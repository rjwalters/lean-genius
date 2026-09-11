from pathlib import Path
import itertools as I,json,time
p=Path(__file__).parent;start=time.monotonic();records=[];bases=[];status='INCOMPLETE'
def guard():
 if time.monotonic()-start>30:raise TimeoutError
try:
 for kind in ['C8','D8']:
  if kind=='C8':J=[[(a+b)%8 for b in range(8)] for a in range(8)]
  else:
   # Labels 2*r+s, r mod4, s mod2.
   J=[[2*((a//2+(-1 if a%2 else 1)*(b//2))%4)+(a%2)^(b%2) for b in range(8)] for a in range(8)]
  inv=[next(b for b in range(8) if J[a][b]==J[b][a]==0) for a in range(8)]
  autos=[]
  for perm in I.permutations(range(1,8)):
   guard();theta=(0,)+perm
   if all(theta[J[a][b]]==J[theta[a]][theta[b]] for a,b in I.product(range(8),repeat=2)):autos.append(theta)
  bases.append({'kind':kind,'multiplication':J,'inverse':inv,'automorphisms':autos})
  for ai,theta in enumerate(autos):
   for c in range(8):
    guard();rec={'base':kind,'automorphism':ai,'square':c};records.append(rec)
    if theta[c]!=c or any(theta[theta[h]]!=J[J[c][h]][inv[c]] for h in range(8)):
     rec['status']='INCOMPATIBLE_EXTENSION';continue
    M=[]
    for a in range(16):
     row=[];h,e=divmod(a,2)
     for b in range(16):
      k,f=divmod(b,2);v=J[h][theta[k] if e else k]
      if e and f:v=J[v][c]
      row.append(2*v+(e^f))
     M.append(row)
    assert all(M[M[a][b]][d]==M[a][M[b][d]] for a,b,d in I.product(range(16),repeat=3))
    orders=[]
    for a in range(16):
     v=0
     for n in range(1,17):
      v=M[v][a]
      if v==0:orders.append(n);break
     else:raise AssertionError('no inverse')
    noninv=[a for a,o in enumerate(orders) if o>2];noncentral=[a for a,o in enumerate(orders) if o==2 and any(M[a][b]!=M[b][a] for b in range(16))]
    rec.update(multiplication=M,orders=orders,noninvolutions=noninv,noncentral_involutions=noncentral)
    if len(noninv)<10:rec['status']='INSUFFICIENT_FREE_PAIRS'
    elif not noncentral:rec['status']='NO_NONCENTRAL_INVOLUTION'
    else:rec['status']='RETAINED'
 status='COMPLETE'
except TimeoutError:pass
r={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'bases':bases,'records':records}
(p/'results.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'status':status,'seconds':r['seconds'],'automorphisms':[(b['kind'],len(b['automorphisms'])) for b in bases],'counts':{s:sum(x['status']==s for x in records) for s in set(x['status'] for x in records)},'retained':[{k:v for k,v in x.items() if k not in ['multiplication','orders']} for x in records if x['status']=='RETAINED']}))
