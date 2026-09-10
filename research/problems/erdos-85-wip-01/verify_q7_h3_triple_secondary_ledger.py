"""Exact scalar consequences of the H3 triple secondary partition."""
from itertools import product
assert 24==1+3*5+8 and 8==6+2
assert 6*3>3*5+2  # m=0 would require18 distinct endpoints in17 vertices.
assert 3*(5//2)+3*5==21
cases=[]
for m,epsilon,k1,k2 in product(range(1,4),range(2),range(2),range(2)):
    if k1+epsilon<1 or k2+epsilon<1:continue
    r=m+epsilon+k1+k2;q=26-2*r;p=17+r
    if p>21:continue
    assert 32==6+2*r+q and 60==2*p+q
    assert 2<=r<=4 and q<=24
    assert 6+r+q+p==49
    if epsilon==0:assert r>=3 and k1==k2==1
    if r==2:assert (m,epsilon,k1,k2)==(1,1,0,0) and 2-k1-k2==2
    cases.append((m,epsilon,k1,k2,r,2-k1-k2))
assert {a[4] for a in cases}=={2,3,4}
print('PASS: secondary degree ledger,2<=e(R)<=4, and e(R)=2 forces at least2 D-triangles through z')
print('Scalar cases:',cases)
print('Necessary conditions only; graph partition is proved in accompanying note; no profile exclusion.')
