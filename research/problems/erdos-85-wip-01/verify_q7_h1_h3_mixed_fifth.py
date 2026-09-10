"""Exact local C4 extremal tables and finite triangle-allocation bounds, not graphs."""
import itertools,json
from pathlib import Path

def extremal(n):
 edges=list(itertools.combinations(range(n),2));best=0
 for mask in range(1<<len(edges)):
  if mask.bit_count()<=best:continue
  neighbors=[set() for _ in range(n)]
  for k,(i,j) in enumerate(edges):
   if mask>>k&1:neighbors[i].add(j);neighbors[j].add(i)
  if all(len(neighbors[i]&neighbors[j])<=1 for i,j in edges):best=mask.bit_count()
 return best
ex=[extremal(n) for n in range(6)]
assert ex==[0,0,1,3,4,6]

def bounds(census,h1=False):
 # State: total local triangle incidences, singleton incidences.
 dp={(0,0):0}
 for t,count in enumerate(census):
  choices=[(tau,2*ex[t+2*tau-1]) for tau in range(1 if t==0 else 0,4-t)]
  for _ in range(count):
   nxt={}
   for (total,single),value in dp.items():
    for tau,cap in choices:
     key=(total+tau,single+(tau if t==1 else 0))
     nxt[key]=max(nxt.get(key,-1),value+cap)
   dp=nxt
 out={}
 for (total,single),cap in dp.items():
  if total%3 or (h1 and not 12<=single<=16):continue
  T=total//3;out[T]=max(out.get(T,-1),cap)
 return [{'T':T,'R_upper':out[T]} for T in sorted(out)]
profiles={
 'H1':{'h':1,'census':[40,8,0,0],'bounds':bounds([40,8,0,0],True)},
 'H3_pair':{'h':3,'census':[25,18,3,0],'bounds':bounds([25,18,3,0])},
 'H3_triple':{'h':3,'census':[24,21,0,1],'bounds':bounds([24,21,0,1])}}
assert [v['T'] for v in profiles['H1']['bounds']]==list(range(18,46))
for row in profiles['H1']['bounds']:
 assert row['R_upper']==(18*row['T']-264 if row['T']<=44 else 538)
for profile in profiles.values():
 h=profile['h']
 for row in profile['bounds']:
  row['p5_lower']=72*row['T']-4116+269*h
  row['p5_upper']=row['p5_lower']+row['R_upper']
  row['R_residue_mod5']=(3*row['T']+h+4)%5
  allowed=[R for R in range(0,row['R_upper']+1,2) if R%5==row['R_residue_mod5']]
  row['allowed_even_R_count']=len(allowed)
  row['allowed_even_R_min']=min(allowed,default=None)
assert [(name,row['T']) for name,p in profiles.items() for row in p['bounds'] if not row['allowed_even_R_count']]==[('H3_triple',8)]
# Consume sol1's explicit degree<=2 spectral relaxation, without asserting a graph.
factors=[([1,3],1),([1,1],1),([1,-2,-4],2),([1,0,-8],3),
         ([1,0,-7],3),([1,0,-6],6),([1,0,-5],2),([1,1,-7],1),
         ([1,1,-5],4),([1,2,-1],1)]
powers=[0]*6
for coeff,multiplicity in factors:
 if len(coeff)==2:
  local=[1]+[(-coeff[1])**k for k in range(1,6)]
 else:
  local=[2,-coeff[1]]
  for k in range(2,6):local.append(-coeff[1]*local[-1]-coeff[2]*local[-2])
 for k in range(6):powers[k]+=multiplicity*local[k]
assert powers==[46,-7,281,-64,1961,-507]
R=powers[5]+3847-72*43
upper=next(row['R_upper'] for row in profiles['H1']['bounds'] if row['T']==43)
assert R==244 and upper==510 and 0<=R<=upper
candidate={'scope':'Sol1 explicit spectral relaxation; no integer matrix/graph assertion',
           'monic_factors_descending_and_multiplicities':factors,'power_sums_0_through_5':powers,
           'T':43,'R':R,'R_upper':upper,'passes_mixed_bound':True}
result={'scope':'Necessary local allocation envelope only; maximizing allocations need not be graph realizable','ex_C4_orders_0_through_5':ex,'profiles':profiles,'h1_spectral_relaxation_check':candidate}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:{'T_min':v['bounds'][0]['T'],'T_max':v['bounds'][-1]['T'],'R_upper_min':v['bounds'][0]['R_upper'],'R_upper_max':v['bounds'][-1]['R_upper']} for k,v in profiles.items()},indent=2))
