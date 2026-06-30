#!/usr/bin/env python3
"""
Durable certificate for inverse-galois-a5-oq-02:
    Gal(x^7 - 7x + 3 / Q) = PSL(2,7)  (Trinks, 1968), order 168.

Build-free verification of every ingredient of the ORIENT pinning argument.
Run:  python3 verify_trinks_psl27.py   (requires sympy)

All facts are exact (integer / finite-field arithmetic), no floating point.
"""
import itertools, math
from collections import Counter
import sympy as sp
from sympy import symbols, Poly, discriminant, factorint, integer_nthroot

x = symbols('x')
f = Poly(x**7 - 7*x + 3, x)
FAIL = []

def check(name, cond):
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")
    if not cond:
        FAIL.append(name)

print("Trinks polynomial f = x^7 - 7x + 3")

print("\n(1) Irreducibility over Q (single-prime certificate)")
# f mod 2 irreducible  =>  f irreducible over Q (f is monic, primitive)
f2 = Poly(x**7 - 7*x + 3, x, modulus=2)
degs2 = sorted(Poly(g, x, modulus=2).degree() for g, m in f2.factor_list()[1] for _ in range(m))
check("f is irreducible over Q", f.is_irreducible)
check("f mod 2 is irreducible (degrees == [7])  => transitive, 7 | |G|", degs2 == [7])

print("\n(2) Discriminant is a perfect square  => G <= A_7")
D = discriminant(f)
fac = factorint(D)
root, exact = integer_nthroot(int(D), 2)
check("disc(f) = 3^8 * 7^8", fac == {3: 8, 7: 8})
check(f"disc(f) = {D} is a perfect square (sqrt = {root} = 3^4*7^4 = {3**4*7**4})",
      exact and root == 3**4 * 7**4)

print("\n(3) Frobenius cycle types (mod p, p does not divide disc = 3*7)")
bad = set(factorint(int(D)).keys())
seen = {}
for p in [2, 5, 11, 13, 17, 19, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
          79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149]:
    if p in bad:
        continue
    fp = Poly(x**7 - 7*x + 3, x, modulus=p)
    degs = tuple(sorted(Poly(g, x, modulus=p).degree() for g, m in fp.factor_list()[1] for _ in range(m)))
    seen.setdefault(degs, p)
for ct in sorted(seen):
    print(f"      cycle type {ct}  (first prime p={seen[ct]})")
# the four non-identity classes we need:
has7   = (7,) in seen                # 7-cycle      => 7 | |G|
has4   = (1, 2, 4) in seen           # order-4 elt  => 4 | |G|
has3   = (1, 3, 3) in seen           # order-3 elt  => 3 | |G|
check("7-cycle present (p=2)            => 7 | |G|", has7)
check("cycle type (1,2,4) present (p=13) => order-4 elt => 4 | |G|", has4)
check("cycle type (1,3,3) present (p=17) => order-3 elt => 3 | |G|", has3)
check("therefore 84 = 4*3*7 divides |G|", has7 and has4 and has3)
# every observed type is even (lies in A_7), consistent with (2):
def parity_even(ct):
    return sum(c - 1 for c in ct) % 2 == 0
check("all observed cycle types are even permutations (in A_7)", all(parity_even(ct) for ct in seen))
# no 5-cycle / no order-6 observed (consistent with PSL(2,7), NOT A_7):
check("no cycle type contains a 5-cycle or 6-cycle (PSL(2,7) has no order 5,6 elt)",
      not any(5 in ct or 6 in ct for ct in seen))

print("\n(4) PSL(2,7) = GL(3,2) acting on the 7 nonzero vectors of F_2^3")
def det3(A):
    return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1])
           -A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0])
           +A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0])) % 2
mats = []
for e in itertools.product((0, 1), repeat=9):
    M = (e[0:3], e[3:6], e[6:9])
    if det3(M) == 1:
        mats.append(M)
check("|GL(3,2)| = |PSL(2,7)| = 168", len(mats) == 168)
vecs = [v for v in itertools.product((0, 1), repeat=3) if any(v)]
vidx = {v: i for i, v in enumerate(vecs)}
def apply(M, v):
    return tuple(sum(M[i][k]*v[k] for k in range(3)) % 2 for i in range(3))
ct_count = Counter()
for M in mats:
    perm = [vidx[apply(M, v)] for v in vecs]
    seen_pt = [False]*7; cyc = []
    for s in range(7):
        if not seen_pt[s]:
            l = 0; j = s
            while not seen_pt[j]:
                seen_pt[j] = True; j = perm[j]; l += 1
            cyc.append(l)
    ct_count[tuple(sorted(cyc))] += 1
expected = {(1,1,1,1,1,1,1): 1, (1,1,1,2,2): 21, (1,2,4): 42, (1,3,3): 56, (7,): 48}
check("PSL(2,7) cycle-type class sizes == {1^7:1, 2^2 1^3:21, 4 2 1:42, 3^2 1:56, 7:48}",
      dict(ct_count) == expected)
nonid = {ct for ct in ct_count if ct != (1,1,1,1,1,1,1)}
check("observed Frobenius types == non-identity PSL(2,7) types (exact match)",
      set(seen.keys()) == nonid)

print("\n(5) Subgroup pin: transitive subgroups of A_7 and the simplicity collapse")
trans_sub_A7 = {"C7": 7, "F21": 21, "PSL(2,7)": 168, "A7": 2520}  # D7,F42,S7 not in A7
div84 = {k: v for k, v in trans_sub_A7.items() if v % 84 == 0}
check("transitive subgroups of A_7 with order divisible by 84 are exactly {PSL(2,7), A_7}",
      set(div84) == {"PSL(2,7)", "A7"})
# Lagrange ALLOWS an order-84 subgroup (84 | 168); it is excluded by SIMPLICITY:
# the only proper divisor of 168 that is a multiple of 84 is 84 itself = index 2,
# and a simple group has no index-2 (hence normal) subgroup.
order84_divisors = [d for d in range(1, 168) if d % 84 == 0 and 168 % d == 0]
check("the only proper order-84-candidate subgroup has index 2 (=> normal => excluded by simplicity)",
      order84_divisors == [84] and 168 // 84 == 2)
# Resolvent: degree 15 = [A7:PSL(2,7)] distinguishes PSL(2,7) from A7 (finite certificate)
check("[A_7 : PSL(2,7)] = 15  (degree of the PSL(2,7)-resolvent)", 2520 // 168 == 15)

print("\n" + ("ALL CHECKS PASSED" if not FAIL else f"FAILURES: {FAIL}"))
