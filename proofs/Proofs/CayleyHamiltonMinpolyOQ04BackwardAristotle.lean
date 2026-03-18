/-
  Aristotle targets for cayley-hamilton-minpoly-oq-04 (backward direction)
  Routine supporting lemmas for automated proof search.
  See CayleyHamiltonMinpolyOQ04Backward.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (backward direction of nonderogatory characterization)
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace Nonderogatory.Backward.Aristotle

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- Lemma 1: Nonzero low-degree polynomial evaluates to nonzero matrix
-- ============================================================

/-- If p is nonzero with deg < deg(minpoly), then p(M) ≠ 0. -/
theorem aeval_ne_zero_of_ne_zero {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree < (minpoly K M).natDegree) :
    aeval M p ≠ 0 := by sorry

-- ============================================================
-- Lemma 2: Nonzero matrix has a vector outside its kernel
-- ============================================================

/-- A nonzero matrix has a vector not in its kernel. -/
theorem exists_mulVec_ne_zero' {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (hA : A ≠ 0) :
    ∃ v : Fin n → K, A.mulVec v ≠ 0 := by sorry

-- ============================================================
-- Lemma 3: Polynomial coefficient extraction
-- ============================================================

/-- If ∑ cₖ Xᵏ = 0 as a polynomial, then cₖ = 0 for all k. -/
theorem coeff_sum_eq_zero_of_sum_eq_zero
    {s : Finset (Fin n)} {c : Fin n → K}
    (h : ∑ k ∈ s, C (c k) * X ^ (k : ℕ) = (0 : K[X]))
    (i : Fin n) (hi : i ∈ s) : c i = 0 := by sorry

-- ============================================================
-- Lemma 4: Degree bound for polynomial sum
-- ============================================================

/-- A polynomial ∑ cₖ Xᵏ for k : Fin n has degree < n. -/
theorem natDegree_sum_lt {s : Finset (Fin n)} {c : Fin n → K}
    (hn : 0 < n) :
    (∑ k ∈ s, C (c k) * X ^ (k : ℕ)).natDegree < n := by sorry

-- ============================================================
-- Lemma 5: Linear independence from annihilation
-- ============================================================

/-- If {v, Mv, ..., M^{n-1}v} are linearly independent and p(M)v = 0
    with deg(p) < n, then p = 0. -/
theorem eq_zero_of_aeval_mulVec_eq_zero
    {M : Matrix (Fin n) (Fin n) K} {v : Fin n → K}
    (hli : LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v))
    {p : K[X]} (hp_deg : p.natDegree < n) (hp_ann : (aeval M p).mulVec v = 0) :
    p = 0 := by sorry

end Nonderogatory.Backward.Aristotle
