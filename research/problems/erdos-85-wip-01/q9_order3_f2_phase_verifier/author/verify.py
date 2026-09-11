"""Exact candidate verifier; never searches or modifies a candidate."""
import json,sys,hashlib
from pathlib import Path

def bits(mask):return [(mask>>t)&1 for t in range(3)]
def reverse(mask):return (mask&1)|((mask&2)<<1)|((mask&4)>>1)
def conv(x,y):
 a,b=bits(x),bits(y)
 return [sum(a[s]*b[(t-s)%3] for s in range(3)) for t in range(3)]
def blocks(record):
 assert len(record)==59
 adj=record[1:19];coords=record[19:]
 U=[[sum(((adj[3*a]>>(3*b+t))&1)<<t for t in range(3)) for b in range(6)] for a in range(6)]
 C=[[0]*20 for _ in range(6)]
 for i in range(20):
  for side in range(2):
   v=coords[2*i+side]
   if v>=0:
    label,phase=divmod(v,3);C[3*side+label][i]=1<<((-phase)%3)
 return U,C

def counts(record,D):
 assert len(D)==20 and all(len(row)==20 for row in D)
 assert all(type(x)==int and 0<=x<8 for row in D for x in row)
 assert all(D[j][i]==reverse(D[i][j]) for i in range(20) for j in range(20))
 assert all(not(D[i][i]&1) for i in range(20))
 U,C=blocks(record)
 AR=[[[sum(conv(U[a][b],C[b][i])[t] for b in range(6))+sum(conv(C[a][j],D[j][i])[t] for j in range(20)) for t in range(3)] for i in range(20)] for a in range(6)]
 RR=[[[sum(conv(reverse(C[a][i]),C[a][j])[t] for a in range(6))+sum(conv(D[i][k],D[k][j])[t] for k in range(20)) for t in range(3)] for j in range(20)] for i in range(20)]
 degrees=[sum(x.bit_count() for x in D[i])+sum(C[a][i].bit_count() for a in range(6)) for i in range(20)]
 return AR,RR,degrees

def verify(record,D):
 AR,RR,degrees=counts(record,D)
 return {'valid':all(d==9 for d in degrees) and all(x<=1 for row in AR for cell in row for x in cell) and all(RR[i][j][t]<=1 for i in range(20) for j in range(20) for t in range(3) if i!=j or t!=0),'residual_degrees':degrees,'max_attached_residual_codegree':max(x for row in AR for cell in row for x in cell),'max_distinct_residual_codegree':max(RR[i][j][t] for i in range(20) for j in range(20) for t in range(3) if i!=j or t!=0)}

if __name__=='__main__':
 data=json.loads(Path(sys.argv[1]).read_text())
 source=Path(sys.argv[2])
 raw=source.read_bytes()
 assert hashlib.sha256(raw).hexdigest()=='ba3f8cbb932d278020ff6510a877099ec63ea5833a298c9f59a1025841cf54e6'
 index=data['phase_index'];assert type(index)==int and 0<=index<56916
 record=list(map(int,raw.splitlines()[index].split()));assert record[0]==index
 result=verify(record,data['D'])
 print(json.dumps(result,indent=2));sys.exit(0 if result['valid'] else 1)
