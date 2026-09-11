from pathlib import Path
import json,itertools,math,time
p=Path(__file__).parent;start=time.monotonic();out=[]
for order in [24,48]:
 divisors=[n for n in range(1,order+1) if order%n==0]
 for sizes in itertools.combinations_with_replacement(divisors,4):
  if sum(sizes)!=78:continue
  pairs=list(itertools.combinations(range(4),2));choices=[]
  for i,j in pairs:
   d=math.gcd(sizes[i],sizes[j]);a=sizes[j]//d;b=sizes[i]//d
   choices.append([(a*k,b*k) for k in range(min(9//a,9//b)+1)])
  tested=degree_pass=0;survivors=[]
  for vals in itertools.product(*choices):
   assert time.monotonic()-start<30,'UNKNOWN original30s'
   tested+=1;Q=[[0]*4 for _ in range(4)]
   for (i,j),(a,b) in zip(pairs,vals):Q[i][j]=a;Q[j][i]=b
   for i in range(4):Q[i][i]=9-sum(Q[i])
   if any(Q[i][i]<0 or Q[i][i]>=sizes[i] for i in range(4)):continue
   degree_pass+=1
   if any(sum(sizes[j]*Q[j][i]*(Q[j][i]-1)//2 for j in range(4))>sizes[i]*(sizes[i]-1)//2 for i in range(4)):continue
   if any(sum(sizes[j]*Q[j][i]*Q[j][k] for j in range(4))>sizes[i]*sizes[k] for i,k in pairs):continue
   survivors.append(Q)
  out.append({'automorphism_order':order,'sizes':sizes,'tested':tested,'degree_pass':degree_pass,'quotients':survivors})
result={'status':'COMPLETE','original_seconds':30,'seconds':time.monotonic()-start,'partitions':out};(p/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps([{k:v for k,v in r.items() if k!='quotients'}|{'survivors':len(r['quotients']),'first':r['quotients'][:1]} for r in out]))
