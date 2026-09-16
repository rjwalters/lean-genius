import hashlib,json,itertools,sys,time
from pathlib import Path
P=Path(__file__).parent;W=Path('/Users/rwalters/GitHub/lean-genius/.codex/worktrees/erdos85-sol2-integration');R=W/'research/problems/erdos-85-wip-01'
sys.path.insert(0,str(R/'sat49'));import verify_h1_sat_graph as decoder
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
def counter(inputs,top):
 ids={};clauses=[]
 def s(k,j):
  nonlocal top
  if (k,j) not in ids:top+=1;ids[k,j]=top
  return ids[k,j]
 n=len(inputs);t=24
 for j in range(n-t):
  clauses.append([inputs[j],s(0,j)])
  for k in range(t-1):
   a=s(k,j)
   if j<n-t-1:clauses.append([-a,s(k,j+1)])
   clauses.append([inputs[j+k+1],-a,s(k+1,j)])
  a=s(t-1,j)
  if j<n-t-1:clauses.append([-a,s(t-1,j+1)])
  clauses.append([inputs[j+t],-a])
 return clauses,[[ids[k,j] for j in range(n-t)] for k in range(t)]
def main():
 start=time.monotonic();deadline=start+60
 row=next(r for r in read(R/'phase_b_h1_cube25_cover/binding-results.json')['results'] if r['tag']=='0bbee37fe45d9447');path=Path(row['cube_path']);raw=path.read_bytes();assert sha(raw)==row['cube_sha256']
 ids,digest,prefixcount=decoder.verify_prefix(path,row['profile']);assert digest==sha(raw)
 lines=raw.splitlines(keepends=True);header=lines[0].split();assert header[:2]==[b'p',b'cnf']
 nc=int(header[3]);assert len(lines)==nc+1
 units=[list(map(int,x.split())) for x in lines[-2:]];assert units==[[301,0],[456,0]],units
 base=f'p cnf {int(header[2])} {nc-2}\n'.encode()+b''.join(lines[1:-2]);assert sha(base)==row['frozen_base_sha256']
 clauses=[tuple(map(int,l.split()[:-1])) for l in lines[1:-2]];assert all(l.split()[-1]==b'0' for l in lines[1:-2]);index={c:i+1 for i,c in enumerate(clauses)}
 certificates=[]
 for y,block in [(4,2),(9,3)]:
  far=[x for x in range(40) if x//5 not in [y//5,y//5^1]];inputs=[ids[tuple(sorted((y,x)))] for x in far];assert len(inputs)==30
  found=[]
  for i,c in enumerate(clauses):
   assert time.monotonic()<deadline
   if len(c)!=2 or c[0]!=inputs[0] or c[1]<=780:continue
   expected,grid=counter(inputs,c[1]-1)
   if clauses[i:i+len(expected)]==list(map(tuple,expected)):found.append((i,expected,grid))
  assert len(found)==1,(y,len(found))
  i,expected,grid=found[0];assert len(expected)==270
  blockclauses=[]
  for b in range(8):
   if b in [y//5,y//5^1]:continue
   for u,v in itertools.combinations(range(5*b,5*b+5),2):
    c=(-ids[tuple(sorted((y,u)))],-ids[tuple(sorted((y,v)))]);assert c in index,c
    blockclauses.append({'clause':list(c),'index':index[c]})
  assert len(blockclauses)==60
  certificates.append({'vertex':y,'target_block':block,'far_vertices':far,'edge_ids':inputs,'auxiliary_grid':grid,'counter_start_clause':i+1,'counter_clauses':expected,'block_clauses':blockclauses,'target_literals':[ids[tuple(sorted((y,v)))] for v in range(5*block,5*block+5)]})
 out={'status':'PASS_EXACT_BASE_CLAUSE_CONTAINMENT','tag':row['tag'],'cube_path':str(path),'cube_sha256':sha(raw),'base_sha256':sha(base),'base_clause_count':len(clauses),'base_variables':int(header[2]),'removed_units':units,'edge_prefix_checked':prefixcount,'decoder_sha256':sha(Path(decoder.__file__).read_bytes()),'certificates':certificates,'required_occurrences':660,'seconds':time.monotonic()-start,'scope':'Clause containment only; semantic CNF-cover argument separate, no UNSAT/proof verification.'}
 (P/'clause-certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='certificates'}))
if __name__=='__main__':main()
