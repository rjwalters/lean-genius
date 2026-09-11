from pathlib import Path
import json,itertools as it,time
p=Path(__file__).resolve().parent;b=p.parent;start=time.monotonic();old=json.loads((b/'residual-ten-D5-five-311-low-edge-allocation/models.json').read_text())['records'];results={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-allocation/results.json').read_text())['records']};prop={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-propagation/results.json').read_text())['records']};edgecases={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-low-edge-capacity/results.json').read_text())['records']};joint={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-nonempty-joint/results.json').read_text())['records']};graphs={r['root']:r for r in json.loads((b/'residual-ten-D5-five-311-high-matchings/results.json').read_text())['records']};pack=json.loads((b/'residual-ten-D5-five-311-packing/results.json').read_text())['records'];dom=json.loads((b/'residual-ten-D5-supports/results.json').read_text())['records'];out=[]
for model in old:
 if results[model['root']]['status']=='EXACT_FARKAS_CONTRADICTION':continue
 assert time.monotonic()-start<30
 src=model['source_root'];ai=model['assignment'];source=joint[src];ci=source['class'];root=pack[ci]['survivors'][source['source_root']];c=dom[ci];ss=[c['high3'][j] for j in root['high3']];S=[set(t) for s in ss for t in (s,[e^1 for e in s])];Hg=graphs[source['packing_root']]['survivors'][source['graph']]['edges'];lows=next(a['lows'] for a in edgecases[src]['survivors'] if a['assignment']==ai);a=next(a for a in prop[src]['survivors'] if a['assignment']==ai);N=[set() for _ in range(70)];V=[{} for _ in range(70)]
 def edge(v,w):N[v].add(w);N[w].add(v)
 for v,w in c['edges']:edge(v,w)
 for v,s in enumerate(S):
  for r in s:edge(10+v,r)
 for v,w in Hg:edge(10+v,10+w)
 for i,(v,r) in enumerate(lows):
  edge(20+i,r)
  if v>=0:edge(20+i,10+v)
 for i,j in a['forced_edges']:edge(20+i,20+j)
 for k,var in enumerate(model['variables']):
  i,j=var['edge'];V[20+i][20+j]=k;V[20+j][20+i]=k
 full=[N[i]|set(V[i]) for i in range(70)];witness=results[model['root']].get('assignment');has_witness=results[model['root']]['status']=='EXACT_RATIONAL_WITNESS';x=[float(__import__('fractions').Fraction(v)) for v in witness] if has_witness else None;cuts=[]
 for i,j in it.combinations(range(70),2):
  base=len(N[i]&N[j]);assert base<=1;linear=[];selected=[]
  for z in sorted(full[i]&full[j]):
   vi=V[i].get(z);vj=V[j].get(z)
   if vi is None and vj is None:continue
   if vi is None or vj is None:linear.append(vj if vi is None else vi)
   elif x is not None and x[vi]+x[vj]>1.000000001:selected.append((z,vi,vj))
  if not linear and not selected:continue
  coefficients={}
  for k in linear:coefficients[k]=coefficients.get(k,0)+1
  for z,v,w in selected:
   coefficients[v]=coefficients.get(v,0)+1;coefficients[w]=coefficients.get(w,0)+1
  label='common-neighbor cut '+str((i,j));upper=1-base+len(selected);cut={'label':label,'coefficients':sorted(coefficients.items()),'lower':0,'upper':upper};model['constraints'].append(cut);cuts.append({'pair':[i,j],'fixed_common':base,'linear_paths':linear,'selected_paths':selected,'upper':upper})
 model['new_cuts']=cuts;out.append(model)
r={'status':'COMPLETE','original_cap_seconds':30,'seconds':time.monotonic()-start,'records':out};(p/'models.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'seconds':r['seconds'],'models':len(out),'cuts':sum(len(r['new_cuts']) for r in out)}))
