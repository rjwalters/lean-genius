#!/usr/bin/env python3
"""Construct odd-prime cross-completion controls for the fixed q16 interval.

Requires NumPy. Exact modular arithmetic throughout; no solver or graph search.
Only primes 3,5,7,11 are asserted. No integral, binary or exterior-Gram
completion is supplied; the actual example fails its modulo-two test.
"""

import numpy as np
from itertools import combinations


def rref(a,p):
 a=a.copy()%p; nr,nc=a.shape; piv=[]; r=0
 for c in range(nc):
  nz=np.flatnonzero(a[r:,c])
  if not len(nz):continue
  k=r+int(nz[0]);a[[r,k]]=a[[k,r]]
  a[r]=a[r]*pow(int(a[r,c]),-1,p)%p
  for i in range(nr):
   if i!=r and a[i,c]:a[i]=(a[i]-a[i,c]*a[r])%p
  piv.append(c);r+=1
  if r==nr:break
 return a,piv


def construct():
 q=16;m=48
 h=np.zeros((m,m),dtype=np.int64)
 for x in range(m):
  for s in (1,3,7):h[x,(s-x)%m]=1
 blocks=[{x,(x+a)%m,(x+c)%m} for a,c in ((7,15),(5,14),(3,13),(1,12)) for x in range(m)]
 blocks += [{x,x+16,x+32} for x in range(16)]
 b=np.array([[int(x in block) for block in blocks] for x in range(m)],dtype=np.int64)
 d=np.array([[int(16<(y-x)%48<32) for y in range(m)] for x in range(m)],dtype=np.int64)
 assert np.all(b.sum(axis=1)==13) and np.all(b.sum(axis=0)==3)
 assert np.array_equal(h@h+b@b.T,15*np.eye(m,dtype=np.int64)+np.ones((m,m),dtype=np.int64)-d)
 c=np.ones_like(b)-h@b
 return h,b,c


def solve(p):
 assert p in (3,5,7,11)
 h,b,c=construct(); n=b.shape[1]
 # Include degree13 as an explicit equation, even in characteristic3.
 a=np.vstack([b,np.ones((1,n),dtype=np.int64)])%p
 c=np.vstack([c,13*np.ones((1,n),dtype=np.int64)])%p
 _,indrows=rref(a.T,p)
 s=a[indrows]; v=c[indrows]; r=len(indrows)
 sr,piv=rref(s,p)
 free=[i for i in range(n) if i not in piv];d=len(free)
 # Inverse of the independent pivot-column minor supplies right inverse.
 aug=np.hstack([s[:,piv],np.eye(r,dtype=np.int64)])
 ar,pp=rref(aug,p);assert pp[:r]==list(range(r))
 R=np.zeros((n,r),dtype=np.int64);R[piv]=ar[:,r:]
 assert np.array_equal(s@R%p,np.eye(r,dtype=np.int64))
 M=v@s.T%p;assert np.array_equal(M,M.T)
 t=(R@v+v.T@R.T-R@M@R.T)%p
 assert np.array_equal(a@t%p,c)
 K=np.zeros((n,d),dtype=np.int64)
 K[free]=np.eye(d,dtype=np.int64);K[piv]=-sr[:r,free]%p
 assert not np.any(a@K%p)
 # First fix all free-coordinate diagonal entries with diagonal kernel forms.
 diag=-np.diag(t)[free]%p
 t=(t+(K*diag)@K.T)%p
 assert not np.any(np.diag(t)[free])
 # Offdiagonal kernel forms leave those entries fixed. Pick a basis of
 # their diagonal effects on the pivot coordinates, stopping at full rank.
 basis={}; effects=[]; pairs=[]
 for f,g in combinations(range(d),2):
  eff=2*K[piv,f]*K[piv,g]%p
  reduced=eff.copy()
  for j,w in basis.items():
   if reduced[j]:reduced=(reduced-reduced[j]*w)%p
  nz=np.flatnonzero(reduced)
  if not len(nz):continue
  j=int(nz[0]);reduced=reduced*pow(int(reduced[j]),-1,p)%p
  basis[j]=reduced;effects.append(eff);pairs.append((f,g))
  if len(basis)==r:break
 assert len(basis)==r, 'Offdiagonal kernel effects do not span all pivot diagonals'
 E=np.array(effects,dtype=np.int64).T
 rr,pp=rref(np.column_stack([E,-np.diag(t)[piv]%p]),p)
 assert pp==list(range(r))
 coeff=rr[:,-1]
 for alpha,(f,g) in zip(coeff,pairs):
  t=(t+alpha*(np.outer(K[:,f],K[:,g])+np.outer(K[:,g],K[:,f])))%p
 assert np.array_equal(t,t.T) and not np.any(np.diag(t))
 assert np.array_equal(a@t%p,c)
 print('PASS p',p,'rankAug',r,'kernel',d,'pivot diagonal effects',len(basis),'BT=C, T1=13, symmetric, diag0')
 return t

if __name__=='__main__':
 for p in (3,5,7,11):solve(p)
