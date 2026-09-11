from pathlib import Path
import json,itertools,hashlib,sys
p=Path(__file__).parent
ORBIT=Path('/tmp/erdos85-sol1-q9-order3-f2-symmetry/orbits.json')
STATE=Path('/tmp/erdos85-sol1-q9-order3-f2-contingency/receipts.json')
def build(index):
 o=json.loads(ORBIT.read_text())[index];r=json.loads(STATE.read_text())[o['state']];T=r['tables'][o['table']]
 words=[(a,b) for a in range(3) for b in range(3) for _ in range(T[a][b])]
 if r['cross_orbits']==3:
  if r['missing_labels'] is None:words.append((3,3))
  else:a,b=r['missing_labels'];words.extend([(a,3),(3,b)])
 assert len(words)==20
 pairs=list(itertools.combinations_with_replacement(range(20),2));ei={e:k for k,e in enumerate(pairs)};rows=[];nextvar=420
 def b(i,j):return ei[tuple(sorted((i,j)))]
 def d(i,j):return 210+b(i,j)
 def add(name,terms,lo=None,hi=None):
  coef={}
  for j,c in terms:coef[j]=coef.get(j,0)+c
  rows.append({'name':name,'terms':[[j,c] for j,c in sorted(coef.items()) if c],'lower':lo,'upper':hi})
 for i,j in pairs:add(['double_implies_present',i,j],[(d(i,j),1),(b(i,j),-1)],hi=0)
 for i in range(20):
  add(['diagonal',i],[(b(i,i),1),(d(i,i),-1)],0,0)
  add(['one_double',i],[(d(i,j),1) for j in range(20)],hi=1)
  a,c=words[i];degree=9-int(a<3)-int(c<3)
  add(['degree',i],[(v,1) for j in range(20) for v in (b(i,j),d(i,j))],degree,degree)
  for label in range(3):
   ca=3-int(0<a<3 and label==3-a)-int(c<3 and r['mapping'][label]==c)
   cb=3-int(0<c<3 and label==3-c)-int(a<3 and r['mapping'][a]==label)
   for side,cap in [(0,ca),(1,cb)]:add(['attached_margin',i,side,label],[(v,1) for j in range(20) if words[j][side]==label for v in (b(i,j),d(i,j))],hi=cap)
 for i,j in itertools.combinations(range(20),2):
  products=[]
  for k in range(20):
   for term,(u,v) in enumerate([(b(i,k),b(j,k)),(d(i,k),b(j,k)),(b(i,k),d(j,k))]):
    z=nextvar;nextvar+=1;products.append(z)
    add(['product_lower',i,j,k,term],[(u,1),(v,1),(z,-1)],hi=1)
  h=sum(words[i][s]<3 and words[i][s]==words[j][s] for s in range(2))
  add(['two_step',i,j],[(z,1) for z in products],hi=3-h)
 assert nextvar==11820 and len(rows)==11980
 assert sum(row['lower'] is not None and row['lower']==row['upper'] for row in rows)==40
 assert all(0<=v<nextvar and c in (-1,1) for row in rows for v,c in row['terms'])
 return {'schema':'erdos85-f2-integral-quotient-v1','representative':index,'source_state':o['state'],'source_table':o['table'],'orbit_size':o['size'],'words':words,'cross_mapping':r['mapping'],'matrix_pair_order':pairs,'variables':{'count':nextvar,'binary_range':[0,420],'nonnegative_continuous_range':[420,nextvar]},'constraints':rows,'objective':None}
def data(m):return json.dumps(m,separators=(',',':'),sort_keys=True).encode()+b'\n'
if __name__=='__main__':
 if sys.argv[1]=='all-hashes':
  out=[]
  for i in range(117):
   m=build(i);raw=data(m);out.append({'representative':i,'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'variables':m['variables']['count'],'constraints':len(m['constraints'])})
  (p/'model-manifest.json').write_text(json.dumps(out,indent=2)+'\n');(p/'model-0.json').write_bytes(data(build(0)))
  (p/'input-pins.json').write_text(json.dumps({str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in (ORBIT,STATE)},indent=2)+'\n');print('Built and structurally checked all117 models;420 binary+11400 continuous,11980 constraints each; no optimizer invoked')
 else:Path(sys.argv[2]).write_bytes(data(build(int(sys.argv[1]))))
