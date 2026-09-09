# Independent check of the 2ADIC_TERMINAL audit's mod-2 proposition on D16:
# M mod 2 should be nilpotent with nullity exactly 2 (=> no alternating, i.e. symmetric
# zero-diagonal, square root over F_2).
import numpy as np
q=16; n=q*q
S=sorted({n//2,*[(s%n) for a in [1,*range(2,q-2,2)] for s in (a,n-a)]})
M=np.ones((n,n),dtype=np.int64)
for i in range(n):
    M[i,i]+=q-1
    for s in S: M[i,(i+s)%n]-=1
M2=M%2
def rank_gf2(A):
    A=A.copy()%2; r=0; rows,cols=A.shape
    for c in range(cols):
        piv=[i for i in range(r,rows) if A[i,c]]
        if not piv: continue
        A[[r,piv[0]]]=A[[piv[0],r]]
        for i in range(rows):
            if i!=r and A[i,c]: A[i]^=A[r]
        r+=1
    return r
rk=rank_gf2(M2)
P=M2.copy(); k=1
while P.any():
    P=(P@M2)%2; k+=1
    if k>n: break
print("odd representatives in R:", [a for a in [1,*range(2,q-2,2)] if a%2], "S =",S)
print("rank(M mod 2) =", rk, " nullity =", n-rk, " nilpotency index (M^k=0) k =", k if k<=n else None)
