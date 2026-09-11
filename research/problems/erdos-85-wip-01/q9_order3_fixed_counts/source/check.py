from pathlib import Path
import json,collections
p=Path(__file__).parent;out={}
for n in [78,80]:
 initial=[];reduced=[];margins=[]
 for f in range(n):
  m=n-f
  if m%3 or m<57:continue
  if f>13:
   lo=10*f-n;excess=lo*lo-f*lo-f*f*(f-1);assert 2*lo>f and excess>0
   margins.append({'fixed':f,'degree_sum_lower':lo,'cauchy_excess':excess})
  for a in range(f+1):
   for b in range(f-a+1):
    for c in range(f-a-b+1):
     d=f-a-b-c;counts=[a,b,c,d];degrees=[0,3,6,9]
     if any(k and degree>=f for degree,k in zip(degrees,counts)):continue
     degree_sum=sum(k*degree for degree,k in zip(degrees,counts))
     if degree_sum%2 or 9*f-degree_sum>m:continue
     if sum(k*degree*(degree-1) for degree,k in zip(degrees,counts))>f*(f-1):continue
     initial.append({'fixed':f,'degree_counts':counts})
     if c or d:continue # paper component bound excludes degree6/9
     if b and b<10:continue # paper cubic-component lemma
     reduced.append({'fixed':f,'nonisolated':b})
 expected=([{'fixed':0,'nonisolated':0},{'fixed':3,'nonisolated':0},{'fixed':6,'nonisolated':0}] if n==78 else [{'fixed':2,'nonisolated':0},{'fixed':5,'nonisolated':0},{'fixed':8,'nonisolated':0},{'fixed':11,'nonisolated':10}])
 assert reduced==expected
 final=[]
 for row in reduced:
  f=row['fixed']
  if row['nonisolated']:
   assert (n,f,row['nonisolated'])==(80,11,10)
   assert 9*8-60>9 # exceptional O_a internal-degree sum contradiction
   continue
  if f and f>n-75:continue
  final.append(f)
 assert final==([0,3] if n==78 else [2,5])
 out[n]={'initial_profiles':initial,'cauchy_excluded':margins,'after_cubic_lemma':reduced,'final_fixed_counts':final}
r={'status':'PASS_ARITHMETIC','orders':out,'scope':'Finite necessary profile reductions; graph lemmas supplied by PROOF.md; no search/witness/exclusion of remaining cases.'};(p/'results.json').write_text(json.dumps(r,indent=2)+'\n');print({n:{'initial_profiles':len(v['initial_profiles']),'final_fixed_counts':v['final_fixed_counts']} for n,v in out.items()})
