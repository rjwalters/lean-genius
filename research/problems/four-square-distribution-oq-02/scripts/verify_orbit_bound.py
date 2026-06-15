#!/usr/bin/env python3
"""
ORIENT verification for four-square-distribution-oq-02.

B4 = (Z/2)^4 semidirect S4, |B4| = 2^4 * 4! = 384, acts on integer vectors
(x1,x2,x3,x4) by coordinate permutation (S4) and independent sign flips ((Z/2)^4).

We verify, by brute force for small n, three claims that form the ORIENT plan:

  (A) Jacobi:        r4(n) = 8 * sigma*(n),  sigma*(n) = sum_{d|n, 4 not| d} d.
  (B) Orbit-size:    for a solution v with z zero-coords and nonzero |values|
                     occurring with multiplicities m_1,...,m_k,
                        |Stab(v)| = 2^z * z! * prod_j m_j!,
                        |orbit(v)| = 384 / |Stab(v)|.
  (C) Type bound:    numTypes(n) := #(B4-orbits) satisfies, for n > 0,
                        numTypes(n) <= r4(n)/8 = sigma*(n),
                     because every orbit of a nonzero vector has size >= 8
                     (max stabilizer for n>0 is 48, at the (a,0,0,0) type).
"""
from itertools import product, permutations
from math import isqrt, factorial
from collections import Counter

def r4_bruteforce(n):
    """Ordered signed reps; count solutions and return the solution set."""
    b = isqrt(n)
    sols = []
    for x in product(range(-b, b+1), repeat=4):
        if x[0]*x[0]+x[1]*x[1]+x[2]*x[2]+x[3]*x[3] == n:
            sols.append(x)
    return sols

def sigma_star(n):
    return sum(d for d in range(1, n+1) if n % d == 0 and d % 4 != 0)

def b4_group():
    """All 384 elements as (signs, perm) with action w_i = signs[i]*v[perm[i]]."""
    elems = []
    for signs in product((1,-1), repeat=4):
        for perm in permutations(range(4)):
            elems.append((signs, perm))
    return elems

B4 = b4_group()
assert len(B4) == 384

def act(g, v):
    signs, perm = g
    return tuple(signs[i]*v[perm[i]] for i in range(4))

def orbit(v):
    return {act(g, v) for g in B4}

def stab_size_formula(v):
    z = sum(1 for c in v if c == 0)
    nz = [abs(c) for c in v if c != 0]
    mult = Counter(nz)
    prod = 1
    for m in mult.values():
        prod *= factorial(m)
    return (2**z) * factorial(z) * prod

ok = True
print(f"{'n':>3} {'r4':>5} {'8sig*':>6} {'numTypes':>8} {'sig*':>5} {'bound ok':>8} {'minorb':>6}")
for n in range(1, 51):
    sols = r4_bruteforce(n)
    r4 = len(sols)
    jac = 8*sigma_star(n)
    if r4 != jac:
        print(f"  JACOBI MISMATCH n={n}: r4={r4} 8sig*={jac}"); ok=False
    # orbits
    seen = set()
    orbits = []
    for v in sols:
        if v in seen: continue
        o = orbit(v)
        seen |= o
        orbits.append(o)
    numTypes = len(orbits)
    # verify orbit-stabilizer + sum = r4, and formula matches brute-force orbit size
    total = 0
    minorb = 384
    for o in orbits:
        rep = next(iter(o))
        formula = 384 // stab_size_formula(rep)
        if formula != len(o):
            print(f"  ORBIT-SIZE MISMATCH n={n} rep={rep}: formula={formula} actual={len(o)}"); ok=False
        total += len(o)
        minorb = min(minorb, len(o))
    if total != r4:
        print(f"  ORBIT-SUM MISMATCH n={n}: sum={total} r4={r4}"); ok=False
    bound_ok = numTypes <= sigma_star(n)
    if not bound_ok:
        print(f"  BOUND VIOLATION n={n}: numTypes={numTypes} sig*={sigma_star(n)}"); ok=False
    if minorb < 8:
        print(f"  MIN-ORBIT < 8 at n={n}: minorb={minorb}"); ok=False
    if n <= 20 or not bound_ok:
        print(f"{n:>3} {r4:>5} {jac:>6} {numTypes:>8} {sigma_star(n):>5} {str(bound_ok):>8} {minorb:>6}")

print()
print("ALL CHECKS PASSED" if ok else "FAILURES ABOVE")
# Spot demonstration of the four largest-stabilizer (smallest-orbit) types for n>0:
print("\nStabilizer/orbit by degeneracy type (illustrative):")
for label, v in [("(a,b,c,d) distinct nonzero", (1,2,3,4)),
                 ("(a,a,a,a)", (1,1,1,1)),
                 ("(a,a,0,0)", (1,1,0,0)),
                 ("(a,0,0,0)", (1,0,0,0))]:
    s = stab_size_formula(v)
    print(f"  {label:28} |Stab|={s:3}  |orbit|={384//s:3}")
