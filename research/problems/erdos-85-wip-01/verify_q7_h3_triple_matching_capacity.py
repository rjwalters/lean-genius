"""Exact scalar capacity check for the universal H3 triple refinement."""
from itertools import product
solutions=[]
for a1,a2,a3 in product(range(3),repeat=3):
    for b12,b13,b23 in product(range(6),repeat=3):
        degrees=[2*a1+b12+b13,2*a2+b12+b23,2*a3+b13+b23]
        outgoing=[20-d for d in degrees]
        if not all(0<=v<=7 for v in outgoing):continue
        assert (a1,a2,a3)==(2,2,2)
        assert sorted([b12,b13,b23]) in [[4,5,5],[5,5,5]]
        p=a1+a2+a3+b12+b13+b23;r=p-17
        assert r in [3,4] and sum(outgoing)==26-2*r
        solutions.append((a1,a2,a3,b12,b13,b23,r))
assert set(solutions)=={(2,2,2,4,5,5,3),(2,2,2,5,4,5,3),(2,2,2,5,5,4,3),(2,2,2,5,5,5,4)}
assert 12*3+3*2==2*21
assert 3*(4*1+1*2)==26-2*4
print('PASS universal scalar capacities:',solutions)
print('Every internal block is a2-edge matching; cross counts4/5/5 or5/5/5; r=3 or4. No graph/profile exclusion.')
