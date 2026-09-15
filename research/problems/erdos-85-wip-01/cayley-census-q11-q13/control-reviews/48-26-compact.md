# Explicit order48 control

The verified SmallGroup(48,26) witness can be written on pairs (i,j) in Z24 x Z2 with multiplication

(i,j)(a,b) = (i + 19^j a mod24, j+b mod2).

Thus the group has presentation r^24=s^2=e, srs=r^19. In the exported GAP table r has index17 and s index2. Every one of the2304 products was checked against the table under (i,j) -> r^i s^j.

Use the inverse-closed connection set

S = {(0,1),(1,1),(5,1),(9,0),(14,1),(15,0),(22,1)}.

The following standalone Python code reconstructs the graph and checks it without GAP, the encoding, or a solver:

```python
from itertools import product, combinations
V = list(product(range(24), range(2)))
S = [(0,1),(1,1),(5,1),(9,0),(14,1),(15,0),(22,1)]
def mul(x, y):
    i,j = x
    a,b = y
    return ((i + 19**j*a) % 24, (j+b) % 2)
A = {x: {mul(x,s) for s in S} for x in V}
assert len(A) == 48
assert all(len(A[x]) == 7 and x not in A[x] for x in V)
assert all(x in A[y] for x in V for y in A[x])
assert all(len(A[x] & A[y]) <= 1 for x,y in combinations(V,2))
assert sum(map(len,A.values())) // 2 == 168
```

This is a coordinate description of the existing positive control, not an additional target witness. The full graph and SAT-model checks are in48-26.json; the coordinate receipt is48-26-compact.json.
