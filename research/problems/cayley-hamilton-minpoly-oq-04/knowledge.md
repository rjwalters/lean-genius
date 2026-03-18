# Knowledge Base: cayley-hamilton-minpoly-oq-04

Nonderogatory matrix characterization: μ_M = χ_M iff cyclic vector.

---

## Problem Understanding

A matrix M ∈ M_n(K) is **nonderogatory** if its minimal polynomial equals its
characteristic polynomial. The classical characterization theorem says this
happens if and only if M has a **cyclic vector** v — a vector such that
{v, Mv, M²v, ..., M^{n-1}v} forms a basis of K^n.

This is equivalent to saying V (as a K[X]-module via M) is cyclic, i.e.,
V ≅ K[X]/(χ_M). The matrix is then similar to the companion matrix of χ_M.

---

## Insights

### Key Insight: Annihilator Formulation
The cyclic vector condition is most cleanly expressed NOT as linear independence
of Krylov vectors, but as: **no nonzero polynomial of degree < n annihilates v
under M**. This formulation directly connects to the minpoly and avoids the
need to expand polynomial evaluation into explicit sums.

### Forward Direction Proof Strategy
The forward direction is elegantly simple with the annihilator formulation:
1. minpoly(M) annihilates M, so (aeval M (minpoly K M)).mulVec v = 0
2. If deg(minpoly) < n, this gives a nonzero poly of degree < n annihilating v
3. Contradiction with cyclic vector property
4. So deg(minpoly) = n = deg(charpoly)
5. Bridge lemma: monic divisor with same degree → equal

### Bridge Lemma
The bridge lemma (monic p | monic q with natDeg(p) = natDeg(q) → p = q) is
proved by: the cofactor r satisfies natDeg(r) = 0 and r is monic (from the
product of leading coefficients), so r = 1.

### Backward Direction
Three approaches exist:
1. **PID module theory** (general fields): V ≅ ⊕ K[X]/(d_i), minpoly = d_k,
   charpoly = Π d_i. Equal iff k = 1.
2. **Jordan Normal Form** (algebraically closed): one block per eigenvalue
3. **Union of subspaces** (infinite fields): complement of ⋃ ker(d(M)) for
   proper divisors d of minpoly
All require substantial infrastructure not readily available in Mathlib.

### Backward Direction via Union Avoidance (Session 2)
Over infinite fields, the backward direction has a clean proof:
1. Non-cyclic vectors lie in ker(g(M)) for proper divisors g of minpoly
2. Each ker(g(M)) is proper (g(M) ≠ 0 since deg(g) < deg(minpoly))
3. The monic divisors of minpoly form a finite set → finite union
4. Over infinite K, V ≠ finite union of proper subspaces → cyclic vectors exist

The union avoidance lemma is proved by Finset induction with a line argument:
for v ∉ W_k and w ∉ W₁∪...∪W_{k-1}, the line {v+tw} meets each W_i in
at most one point (if two points, w ∈ W_i by subtraction, contradiction).
Since K is infinite and there are only finitely many bad t values, a good t exists.

**Finite fields remain open**: the union avoidance argument fails (K is finite),
and the backward direction requires the PID structure theorem or explicit counting.

---

## Dead Ends

None — the annihilator approach worked on first attempt for the forward direction.
For the backward direction, the direct polynomial approach works for infinite fields.

---

## Built Items

- `proofs/Proofs/CayleyHamiltonMinpolyOQ04.lean` (0 sorries, 1 axiom)
  - `IsCyclicVector` - annihilator formulation
  - `IsCyclicVectorLI` - linear independence formulation
  - `IsNonderogatory` - minpoly = charpoly
  - `minpoly_eq_charpoly_of_natDegree_eq` - bridge lemma
  - `cyclic_implies_nonderogatory` - forward direction (proved)
  - `nonderogatory_has_cyclic_vector` - backward direction (axiom)
  - `nonderogatory_iff_cyclic_vector` - full equivalence
  - `nonderogatory_iff_natDegree_eq` - degree characterization
  - `derogatory_iff_natDegree_lt` - derogatory characterization

- `proofs/Proofs/CayleyHamiltonMinpolyOQ04Backward.lean` (3 sorries, 0 axioms)
  - `not_union_proper_subspaces` - PROVED: union avoidance for infinite fields
  - `aeval_ne_zero_of_ne_zero` - PROVED: nonzero poly → nonzero matrix
  - `exists_mulVec_ne_zero` - PROVED: nonzero matrix has vector outside kernel
  - `powers_linearIndependent` - FULLY PROVED (coefficient extraction via C_mul_X_pow_eq_monomial + coeff_monomial; degree bound via natDegree_C_mul_X_pow_le + Finset.sup_lt_iff)
  - `isCyclicVector_of_linearIndependent` - 1 sorry (needs polynomial → matrix sum → mulVec distribution)
  - `nonderogatory_has_cyclic_vector_infinite` - main theorem, 1 sorry (wiring: kernel lattice + union avoidance)
  - `nilpotent_krylov_independent` - 1 sorry (descending induction extracting coefficients via N^{n-1-j})

  Session 2026-03-18 (researcher-5): Eliminated 2 sorries in powers_linearIndependent

- `proofs/Proofs/CayleyHamiltonMinpolyOQ04BackwardAristotle.lean`
  - Aristotle companion file with 5 routine lemmas for automated proof search

## Approaches Explored

### Annihilator-based forward direction
**Status**: succeeded
Define cyclic vector via annihilator ideal, prove forward direction using minpoly annihilation
**Outcome**: Clean proof with 0 sorries for forward direction

### Union avoidance for infinite fields
**Status**: in-progress
Prove backward direction by showing non-cyclic vectors lie in a finite union of proper subspaces, then applying union avoidance (infinite fields only)
**Outcome**: 3 key lemmas proved, main theorem wired with 6 helper sorries
