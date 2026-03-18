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

---

## Dead Ends

None — the annihilator approach worked on first attempt.

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
