#!/usr/bin/env python3
"""
Independent verification of the *simplicity-collapse* argument formalized in
`proofs/Proofs/InverseGaloisA5OQ02.lean` (theorem `simple168_subgroup_card_collapse`).

The Lean theorem says: in a finite simple group G of order 168, any subgroup H with
84 | |H| equals the whole group. This script checks the purely arithmetic and
group-structural facts the proof relies on, plus the GL(3,2)=PSL(2,7) data behind the
cycle-type certificate. No floats; exact integer / finite-field arithmetic only.
"""

from itertools import product

ok = True
def check(name, cond):
    global ok
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")
    ok = ok and cond

print("== Collapse arithmetic ==")
divs = [d for d in range(1, 169) if 168 % d == 0]
mult84 = [d for d in divs if d % 84 == 0]
check("divisors of 168 that are multiples of 84 are exactly {84,168}", mult84 == [84, 168])
# index of an order-84 subgroup in a group of order 168 is 2 (the normal/simple crux)
check("[168 : 84] = 2", 168 // 84 == 2)
# index of an order-168 subgroup is 1 (=> whole group)
check("[168 : 168] = 1", 168 // 168 == 1)
# 84 = lcm(7,4,3) (the cycle-type input)
import math
check("lcm(7,4,3) = 84", math.lcm(7, 4, 3) == 84)

print("== Order 168 factorization ==")
check("168 = 2^3 * 3 * 7", 168 == 2**3 * 3 * 7)
check("disc = 3^8 * 7^8 = 194481^2", 3**8 * 7**8 == 194481**2 == 37822859361)

print("== GL(3,2) = PSL(2,7): order and cycle-type classes on 7 Fano points ==")
# Build GL(3,2): invertible 3x3 matrices over F2, acting on the 7 nonzero vectors.
F = [0, 1]
vecs = [v for v in product(F, repeat=3) if any(v)]   # 7 nonzero vectors of F2^3
assert len(vecs) == 7
vindex = {v: i for i, v in enumerate(vecs)}

def matvec(M, v):
    return tuple(sum(M[r][c] * v[c] for c in range(3)) % 2 for r in range(3))

def is_invertible(M):
    # 3x3 over F2 invertible iff det == 1 (mod 2)
    det = (
        M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
        - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
        + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])
    )
    return det % 2 == 1

def cycle_type(perm):
    n = len(perm); seen = [False]*n; t = []
    for i in range(n):
        if not seen[i]:
            ln = 0; j = i
            while not seen[j]:
                seen[j] = True; j = perm[j]; ln += 1
            t.append(ln)
    return tuple(sorted(t))

mats = []
for entries in product(F, repeat=9):
    M = [list(entries[0:3]), list(entries[3:6]), list(entries[6:9])]
    if is_invertible(M):
        mats.append(M)

check("|GL(3,2)| = 168", len(mats) == 168)

from collections import Counter
type_counts = Counter()
for M in mats:
    perm = [vindex[matvec(M, v)] for v in vecs]
    type_counts[cycle_type(perm)] += 1

# Expected class sizes on the 7 points: identity 1^7:1, 2^2 1^3:21, 4.2.1:42, 3^2.1:56, 7:48
expected = {(1,1,1,1,1,1,1):1, (1,1,1,2,2):21, (1,2,4):42, (1,3,3):56, (7,):48}
check("cycle-type class sizes match PSL(2,7) on Fano points", dict(type_counts) == expected)
check("class sizes sum to 168", sum(type_counts.values()) == 168)
# Element orders present are exactly {1,2,3,4,7} (no 5- or 6-cycle => not A7)
orders_present = set()
for t in type_counts:
    orders_present.add(math.lcm(*t) if len(t) > 1 else t[0])
check("element orders are exactly {1,2,3,4,7}", orders_present == {1,2,3,4,7})

print()
print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
exit(0 if ok else 1)
