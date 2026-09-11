from pathlib import Path
import json,time
p=Path(__file__).parent;start=time.monotonic();data=json.loads((p/'results.json').read_text());out=[];status='INCOMPLETE'
try:
 for mi,rec in enumerate(data['records']):
  if rec['status']!='RETAINED':continue
  M=rec['multiplication'];orders=rec['orders'];found=None
  for r in range(16):
   if time.monotonic()-start>30:raise TimeoutError
   if orders[r]!=8:continue
   powers=[0]
   for i in range(1,8):powers.append(M[powers[-1]][r])
   for t in range(16):
    if orders[t]!=2 or t in powers:continue
    for k in (3,5):
     if M[M[t][r]][t]!=powers[k]:continue
     mapping=[M[powers[i]][t] if e else powers[i] for i in range(8) for e in range(2)]
     assert len(set(mapping))==16
     for a in range(16):
      for b in range(16):
       i,e=divmod(a,2);j,f=divmod(b,2);product=2*((i+(k if e else 1)*j)%8)+(e^f)
       assert M[mapping[a]][mapping[b]]==mapping[product]
     found={'model_record':mi,'r':r,'t':t,'exponent':k,'isomorphism':mapping};break
    if found:break
   if found:break
  assert found is not None
  out.append(found)
 assert len(out)==10
 status='COMPLETE'
except TimeoutError:pass
result={'status':status,'original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'identifications.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':status,'seconds':result['seconds'],'models':len(out),'types':{str(k):sum(x['exponent']==k for x in out) for k in (3,5)}}))
