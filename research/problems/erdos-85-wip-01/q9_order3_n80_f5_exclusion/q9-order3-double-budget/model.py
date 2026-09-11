from pathlib import Path
import importlib.util
p=Path(__file__).resolve().parent.parent/'q9-order3-fractional-residual/model.py';spec=importlib.util.spec_from_file_location('base_residual',p);base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def model(code):
 m=base.model(code);n=len(m['words']);original=m['variables'];incident=[[] for _ in range(n)]
 for k,(i,j) in enumerate(m['edges']):
  incident[i].append(n+k)
  if j!=i:incident[j].append(n+k)
 def add(row,label):m['A'].append(row);m['rhs'].append(0);m['labels'].append(label)
 for i in range(n):
  ts=[]
  for y in incident[i]:
   t=m['variables'];m['variables']+=1;ts.append(t)
   add({y:1,t:-1,i:-1},['excess_lower',i,y,t])
   add({t:1,i:-1},['excess_upper',i,t])
  add({i:-1,**{t:1 for t in ts}},['double_budget',i])
 for i in range(n):
  for j in range(i+1,n):
   if sum(a==b for a,b in zip(m['words'][i],m['words'][j]))>3:m['A'].append({i:1,j:1});m['rhs'].append(1);m['labels'].append(['word_incompatible',i,j])
 m['base_variables']=original;return m
