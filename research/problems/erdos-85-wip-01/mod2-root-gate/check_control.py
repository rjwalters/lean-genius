#!/usr/bin/env python3
"""Deterministic construction checks, no search and no third-party packages."""
import json
from pathlib import Path

def bits(x):
    while x:
        low=x & -x
        yield low.bit_length()-1
        x ^= low

def check(q):
    assert q>=8 and q & (q-1)==0
    s=q*q//4; t=q//4-1; m=2*s; n=2*m
    T=[sum(1<<((i+j)%s) for j in list(range(1,t+1))+list(range(-t,0))) for i in range(s)]
    H=[]
    for a in range(2):
        for i in range(s):
            H.append((T[i]<<(a*s)) | (1<<((1-a)*s+i)))
    # Construct D directly as lexicographic product, grouped by inner coordinate.
    D=[]
    for a in range(2):
        for i in range(m):
            D.append(H[i] | (H[i]<<m) | (1<<((1-a)*m+i)))
    all_s=(1<<s)-1
    F0=[all_s ^ (1<<i) ^ T[i] for i in range(s)]
    U=[F0[i] & ~((1<<(i+1))-1) for i in range(s)]
    UT=[sum(1<<j for j in range(s) if (U[j]>>i)&1) for i in range(s)]
    B=[u<<s for u in U]+[UT[i] | ((all_s^(1<<i))<<s) for i in range(s)]
    X=[(1<<i) | (1<<((i+s)%m)) for i in range(m)]
    A=[B[i] | ((B[i]^X[i])<<m) for i in range(m)]
    A += [(B[i]^X[i]) | (B[i]<<m) for i in range(m)]
    assert all(row.bit_count()==q-1 and not ((row>>i)&1) for i,row in enumerate(D))
    for rows in (D,A):
        assert all(((rows[j]>>i)&1)==1 for i,row in enumerate(rows) for j in bits(row))
    assert all(not ((row>>i)&1) and row.bit_count()%2==0 for i,row in enumerate(A))
    all_n=(1<<n)-1
    for i,row in enumerate(A):
        square_row=0
        for j in bits(row): square_row ^= A[j]
        assert square_row == (all_n ^ (1<<i) ^ D[i])
    seen={0}; todo=[0]
    for i in todo:
        for j in bits(D[i]):
            if j not in seen: seen.add(j); todo.append(j)
    assert len(seen)==n
    # Exhibit a triangle from an H edge and the doubled vertex.
    j=next(bits(H[0])); triangle=[0,m,j]
    assert all((D[u]>>v)&1 for u in triangle for v in triangle if u!=v)
    return {'q':q,'n':n,'defect_degree':q-1,'components':1,'triangle':triangle,
            'root_integer_degree_min':min(x.bit_count() for x in A),
            'root_integer_degree_max':max(x.bit_count() for x in A),
            'symmetric_alternating_root_mod2':True}

if __name__=='__main__':
    out={'kind':'deterministic construction regression; uniform proof in CONTROL.md',
         'results':[check(q) for q in (16,32)]}
    Path(__file__).with_name('control-verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
