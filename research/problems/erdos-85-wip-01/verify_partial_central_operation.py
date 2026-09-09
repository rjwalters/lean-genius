"""Exact common-neighbor calibration and central-law instability controls."""
from pathlib import Path
from itertools import combinations
from collections import Counter
from fractions import Fraction
import argparse,ast,hashlib,json,tempfile
import numpy as np
ROOT=Path(__file__).parent
SOURCE=Path(__file__).with_name('binary_q4_fixed_free_disconnected_control.py')

def partial_table(A):
 n=len(A);square=A@A
 assert np.all(np.diag(A)==0) and np.array_equal(A,A.T)
 assert np.all(square[~np.eye(n,dtype=bool)]<=1)
 P=np.full((n,n),-1,dtype=np.int32)
 for x,y in combinations(range(n),2):
  common=np.flatnonzero(A[x]*A[y])
  if len(common):P[x,y]=P[y,x]=int(common[0])
 return P

def partial_check(A,P,q):
 n=len(A);assert np.all(A.sum(axis=1)==q)
 assert np.array_equal(P,P.T)
 for y in range(n):
  fibers=Counter(int(v) for v in P[y] if v>=0)
  assert fibers=={int(v):q-1 for v in np.flatnonzero(A[y])}
 count=0
 for y in range(n):
  left=P[:,y,None];right=P[y,None,:]
  mask=(left>=0)&(right>=0)&(left!=right)
  out=P[np.maximum(left,0),np.maximum(right,0)]
  assert np.all(out[mask]==y)
  count+=int(mask.sum())
 assert count==n*q*(q-1)**3
 return {'n':n,'q':q,'defined_ordered_pairs':int((P>=0).sum()),'row_fiber_size':q-1,'conditional_central_triples':count,'PASS':True}

def field(k,mod):
 q=1<<k
 def mul(a,b):
  out=0
  while b:
   if b&1:out^=a
   b>>=1;a<<=1
   if a&q:a^=mod
  return out
 M=np.array([[mul(a,b) for b in range(q)] for a in range(q)],dtype=np.int32)
 assert np.array_equal(M,M.T)
 inv=[0]+[next(b for b in range(1,q) if M[a,b]==1) for a in range(1,q)]
 for a in range(q):
  for b in range(q):
   for c in range(q):
    assert M[M[a,b],c]==M[a,M[b,c]]
    assert M[a,b^c]==(M[a,b]^M[a,c])
 return q,M,inv

def core_check(k,mod):
 q,M,inv=field(k,mod);n=q*q
 coords=[divmod(i,q) for i in range(n)]
 det=np.array([[M[a,d]^M[b,c] for c,d in coords] for a,b in coords],dtype=np.int32)
 A=(det==1).astype(np.int32)
 assert np.all(A[0]==0) and np.all(A[1:].sum(axis=1)==q)
 P=partial_table(A[1:,1:]);core=partial_check(A[1:,1:],P,q)
 T=np.zeros((n,n),dtype=np.int32)
 for x,(a,b) in enumerate(coords):
  for y,(c,d) in enumerate(coords):
   if det[x,y]:
    t=inv[det[x,y]];T[x,y]=int(M[a^c,t])*q+int(M[b^d,t])
 assert np.array_equal(T,T.T)
 assert np.array_equal(T[1:,1:],np.where(P>=0,P+1,0))
 # Exhaustively count all n^3 law instances; undefined products go to0.
 successes=0
 for y in range(n):
  out=T[T[:,y,None],T[y,None,:]]
  successes+=int((out==y).sum())
 expected=(n-1)*q*(q-1)**3+n*n
 assert successes==expected
 # An exact target exists at this square cardinality.
 B=np.array([[b*q+c for c,d in coords] for a,b in coords],dtype=np.int32)
 for y in range(n):assert np.all(B[B[:,y,None],B[y,None,:]]==y)
 assert np.all((B!=B.T)|np.eye(n,dtype=bool))
 disagreement=int((T!=B).sum());bound=n*(n-1)//2
 assert disagreement>=bound
 out={'q':q,'modulus_bits':mod,'core':core,'padded_order':n,'dummy_degree':0,'central_successes':successes,'central_trials':n**3,'success_fraction':str(Fraction(successes,n**3)),'failure_fraction':str(Fraction(n**3-successes,n**3)),'distance_lower_bound_to_every_exact_model':str(Fraction(bound,n*n)),'disagreements_with_natural_model':disagreement,'table_sha256':hashlib.sha256(T.astype('<i4').tobytes()).hexdigest(),'PASS':True}
 np.save(ROOT/f'core-q{q}-padded-table.npy',T)
 print(q,'PASS',successes,'/',n**3,'exact-law triples; universal edit bound',bound,'/',n*n,flush=True)
 return out

def main():
 global ROOT
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output-dir',type=Path,help='Directory for verification JSON and exact tables; defaults to a new temporary directory.')
 args=parser.parse_args()
 ROOT=args.output_dir.resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix='erdos85-central-operation-'))
 ROOT.mkdir(parents=True,exist_ok=True)
 tree=ast.parse(SOURCE.read_text());edges=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='A_EDGES' for t in n.targets))
 A=np.zeros((16,16),dtype=np.int32)
 for u,v in edges:A[u,v]=A[v,u]=1
 control=partial_check(A,partial_table(A),4)
 out={'genuine_q4_square_control':control,'q4_source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'field_core_controls':[core_check(2,0b111),core_check(4,0b10011)],'scope':'Common-neighbor partial law and total-table instability; padded graphs are not regular endpoint witnesses.'}
 (ROOT/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
 print('Evidence directory:',ROOT)
if __name__=='__main__':main()
