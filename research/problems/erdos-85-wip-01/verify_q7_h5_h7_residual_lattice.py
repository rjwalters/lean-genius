#!/usr/bin/env python3
"""Incidence/lattice checks only. Unknown graph C and residual R are not built."""
import json

import sympy as sp

from q7_h5_h7_setup_checks import incidence


def rank_mod(A, p):
    rows = [[int(x) % p for x in A.row(i)] for i in range(A.rows)]
    rank = 0
    for col in range(A.cols):
        pivot = next((i for i in range(rank,A.rows) if rows[i][col]),None)
        if pivot is None:
            continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        inv=pow(rows[rank][col],-1,p)
        rows[rank]=[(x*inv)%p for x in rows[rank]]
        for i in range(A.rows):
            if i != rank:
                m=rows[i][col]
                rows[i]=[(x-m*y)%p for x,y in zip(rows[i],rows[rank])]
        rank+=1
        if rank==A.rows:
            break
    return rank


def zero_mod(A,p):
    return all(int(x)%p==0 for x in A)


def main():
    profiles=[(5,[]),(5,[(0,1,2)]),(5,[(0,1,2),(0,3,4)]),(7,[])]
    rows=[]
    for h,triples in profiles:
        B,masks=incidence(h,triples)
        pivots=[masks.index((i,)) for i in range(h)]+[masks.index(())]
        free=[i for i in range(len(masks)) if i not in pivots]
        order=pivots+free
        B=B[:,order]
        M=B.col_join(sp.ones(1,B.cols))
        P,F=M[:,:h+1],M[:,h+1:]
        assert P.det()==1
        N=(-P.inv()*F).col_join(sp.eye(len(free)))
        assert all(x.is_Integer for x in N)
        assert M*N==sp.zeros(h+1,len(free))
        assert N[h+1:,:]==sp.eye(len(free))
        det_lattice=int((N.T*N).det())
        Delta=343-22*h-h*h
        assert det_lattice==int((M*M.T).det())==7**(h-1)*Delta
        t=B.T*sp.ones(h,1)
        w=(h+7)*sp.ones(B.cols,1)-8*t
        assert B*w==sp.zeros(h,1)
        assert sum(w)==Delta
        p=13 if h==5 else 5
        lam=((h+7)*pow(8,-1,p))%p
        assert zero_mod(M*w,p) and not zero_mod(w,p)
        assert zero_mod(N*w[h+1:,:]-w,p)
        assert ((lam*lam-7*lam+h)%p)==0
        # On actual C, Cw=(49-h)1-(h+7)t by the checked block identities.
        formal_Cw=(49-h)*sp.ones(B.cols,1)-(h+7)*t
        assert zero_mod(formal_Cw-lam*w,p)
        X=sp.zeros(h,h-1)
        for j in range(h-1):
            X[j,j]=1
            X[h-1,j]=-1
        W=B.T*X
        assert B*W==7*X
        assert zero_mod(M*W,7)
        assert rank_mod(W,7)==h-1
        assert rank_mod(W[h+1:,:],7)==h-1
        assert zero_mod(N*W[h+1:,:]-W,7)
        rows.append({'h':h,'triples':triples,'pivot_determinant':1,
          'kernel_rank':len(free),'exact_lattice_determinant':det_lattice,
          'overlap_prime':p,'overlap_eigenvalue':lam,'mod7_kernel_lower_bound':h-1,
          'residual_constant_divisor':7**(h-1),
          'adjacency_determinant_divisor':(49-h)*7**(2*h-2)})
    print(json.dumps({'scope':'Exact incidence/lattice data; no C/R construction or spectrum exclusion',
                      'profiles':rows},indent=2))


if __name__=='__main__':
    main()
