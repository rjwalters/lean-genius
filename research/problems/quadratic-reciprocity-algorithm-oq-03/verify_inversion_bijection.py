#!/usr/bin/env python3
"""Explicit BIJECTIVE characterization of the inversions of the grid-transpose
permutation for quadratic-reciprocity-algorithm-oq-03 (Milestone 2).

Why this exists.  `verify_grid_inversions.py` certifies the *count*
`inv(sigma) = C(p,2)*C(q,2)` by a brute O(n^2) pair scan, but it never says
*which* pairs are the inversions, nor exhibits the bijection that makes the
count fall out.  Mathlib defines `Equiv.Perm.sign` via `signAux` = parity of the
inversion set `{(a,b) : a<b, sigma b < sigma a}` (a `Finset.filter` over
`finPairsLT`), so the Lean M2 proof does not want the cycle structure of sigma —
it wants a closed form for the *cardinality of that filtered set*.  The cleanest
way to get the cardinality in Lean is a `Finset` bijection (`Finset.card_bij` /
`Finset.card_nbij'`) onto a product of "2-out-of-p rows" x "2-out-of-q columns".
This script pins exactly that bijection so the next live (Docker/Aristotle)
window can transcribe it with zero combinatorial ambiguity.

Setup.  N = p*q.  Row-major index a = i*q + j with i in [0,p), j in [0,q);
write i(a) = a // q (its row), j(a) = a % q (its column).

    sigma(a) = j(a)*p + i(a)     (column-major value).

CLAIM A (inversion characterization).  For a < b (row-major),

    (a,b) is an inversion of sigma   <=>   i(a) < i(b)  AND  j(a) > j(b).

  Proof sketch (the elementary case split the Lean proof will mirror):
    * a < b in row-major  <=>  i(a) < i(b),  OR  (i(a)=i(b) AND j(a)<j(b)).
    * sigma(a) > sigma(b) in column-major  <=>  j(a) > j(b),  OR
      (j(a)=j(b) AND i(a)>i(b)).
    - same row  (i(a)=i(b)):  a<b forces j(a)<j(b), incompatible with j(a)>j(b)
      and with j(a)=j(b)&i(a)>i(b) -> NO inversion.
    - same column (j(a)=j(b)):  sigma(a)>sigma(b) forces i(a)>i(b), incompatible
      with a<b (which forces i(a)<=i(b)) -> NO inversion.
    - i(a)!=i(b) and j(a)!=j(b):  a<b <=> i(a)<i(b);  sigma(a)>sigma(b) <=>
      j(a)>j(b).  Inversion <=> i(a)<i(b) AND j(a)>j(b).  QED

CLAIM B (the bijection -> closed-form count).  The map

    Phi : {(r,s,c,d) : 0<=r<s<p, 0<=c<d<q}  ->  inversions(sigma)
    Phi(r,s,c,d) = (a,b) = (r*q + d,  s*q + c)

is a well-defined bijection onto the inversion set.  Each unordered choice of two
rows {r<s} and two columns {c<d} yields EXACTLY ONE inversion, namely the cell
pair (smaller row, larger column) before (larger row, smaller column).  Hence

    inv(sigma) = #{2-row choices} * #{2-col choices} = C(p,2) * C(q,2).

  Well-defined: a = r*q+d < s*q+c = b because r<s (so r*q+d <= r*q+(q-1) =
  (r+1)*q-1 < s*q <= s*q+c); and i(a)=r<s=i(b), j(a)=d>c=j(b), so by CLAIM A
  (a,b) is an inversion.
  Surjective+injective: given any inversion (a,b), CLAIM A gives i(a)<i(b) and
  j(a)>j(b); set r=i(a), s=i(b), c=j(b), d=j(a) (so r<s, c<d) -> unique preimage.

Both claims are primality-free (verified over even/composite dimensions too); the
odd-prime reciprocity exponent then follows from the parity step (III) already in
verify_grid_inversions.py:  C(p,2) ≡ (p-1)/2 (mod 2) for odd p.

Run: python3 verify_inversion_bijection.py    (pure stdlib).  All asserts pass.
"""

from math import comb


def i_of(a, q):
    return a // q


def j_of(a, q):
    return a % q


def sigma(a, p, q):
    return j_of(a, q) * p + i_of(a, q)


def main():
    max_dim = 14
    n_grids = 0
    for p in range(1, max_dim):
        for q in range(1, max_dim):
            N = p * q

            # Ground truth: the inversion set, by direct definition.
            inv_set = set()
            for a in range(N):
                sa = sigma(a, p, q)
                for b in range(a + 1, N):
                    if sa > sigma(b, p, q):
                        inv_set.add((a, b))

            # CLAIM A: inversion  <=>  i(a)<i(b) and j(a)>j(b).
            charA = set()
            for a in range(N):
                ia, ja = i_of(a, q), j_of(a, q)
                for b in range(a + 1, N):
                    if ia < i_of(b, q) and ja > j_of(b, q):
                        charA.add((a, b))
            assert charA == inv_set, f"CLAIM A fails at (p,q)=({p},{q})"

            # CLAIM B: Phi is a bijection from {r<s}x{c<d} onto inv_set.
            image = set()
            tuples = 0
            for r in range(p):
                for s in range(r + 1, p):
                    for c in range(q):
                        for d in range(c + 1, q):
                            a, b = r * q + d, s * q + c
                            assert a < b, f"Phi not order-preserving at ({p},{q})"
                            image.add((a, b))
                            tuples += 1
            # bijection: image == inv_set AND injective (#tuples == #image).
            assert image == inv_set, f"CLAIM B image != inversions at ({p},{q})"
            assert tuples == len(image), \
                f"CLAIM B not injective at ({p},{q}): {tuples} tuples, {len(image)} images"
            assert len(inv_set) == comb(p, 2) * comb(q, 2), \
                f"count != C(p,2)C(q,2) at ({p},{q})"
            n_grids += 1

    print(f"CLAIM A  inversion(sigma) <=> i(a)<i(b) AND j(a)>j(b):  OK for {n_grids} grids "
          f"1<=p,q<{max_dim} (incl. even & composite)")
    print(f"CLAIM B  Phi(r<s,c<d)=(r*q+d, s*q+c) is a bijection onto inversions, exactly one")
    print(f"         per (2-row, 2-col) choice  =>  inv(sigma)=C(p,2)*C(q,2):  OK for {n_grids} grids")
    print("\nALL ASSERTS PASSED.  This pins the EXACT Finset bijection the Lean signAux")
    print("inversion-count proof must construct (Finset.card_nbij' onto offDiag-style")
    print("2-subsets of Fin p x 2-subsets of Fin q); the cycle structure of sigma is not")
    print("needed.  Closed form inv(sigma)=C(p,2)*C(q,2) is primality-free; odd-prime")
    print("reciprocity exponent follows from the parity step (III) in verify_grid_inversions.py.")


if __name__ == "__main__":
    main()
