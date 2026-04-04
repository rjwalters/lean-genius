/-
  Aristotle targets for CayleyHamiltonReductionOQ02OQ01
  (Rational Canonical Form: Companion Matrix Properties)
  Routine supporting lemmas for automated proof search.
  See CayleyHamiltonReductionOQ02OQ01.lean for the main formalization.

  These lemmas provide building blocks for the companion matrix proofs:
  - Polynomial evaluation at companion matrix helpers
  - minpoly divides p when p annihilates C(p)
  - Degree arguments for minpoly = p
  - charpoly and minpoly degree relationship
  - Linear independence from orbit argument
-/
import Mathlib

open Polynomial Matrix

namespace CayleyHamiltonOQ02OQ01.Aristotle

variable (F : Type*) [Field F]

/-
  ## Section 1: Polynomial Evaluation Helpers
-/

/-- If p annihilates M then minpoly divides p -/
lemma minpoly_dvd_of_aeval_zero {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (p : F[X]) (h : aeval M p = 0) :
    minpoly F M ∣ p := by
  sorry

/-- minpoly of M divides charpoly of M -/
lemma minpoly_dvd_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) : minpoly F M ∣ M.charpoly := by
  sorry

/-- charpoly of an n×n matrix has degree n -/
lemma charpoly_natDegree {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) : M.charpoly.natDegree = Fintype.card n := by
  sorry

/-- If minpoly | p and deg p ≤ deg minpoly then minpoly = p (both monic) -/
lemma dvd_antisymm_monic {p q : F[X]} (hp : p.Monic) (hq : q.Monic)
    (hdvd : q ∣ p) (hdeg : p.natDegree ≤ q.natDegree) : q = p := by
  sorry

/-
  ## Section 2: Orbit and Linear Independence Helpers
-/

/-- If C^k * e₀ = eₖ for 0 ≤ k < d, the vectors are linearly independent -/
lemma orbit_basis_independent {d : ℕ} [NeZero d] {F : Type*} [Field F]
    (C : Matrix (Fin d) (Fin d) F)
    (horbit : ∀ k : Fin d, (C ^ k.val) *ᵥ (Pi.single 0 1) = Pi.single k 1) :
    LinearIndependent F (fun k : Fin d => (C ^ k.val) *ᵥ (Pi.single 0 1)) := by
  sorry

/-- Standard basis vectors are linearly independent -/
lemma stdBasis_linearIndependent {d : ℕ} {F : Type*} [Field F] :
    LinearIndependent F (fun k : Fin d => (Pi.single k 1 : Fin d → F)) := by
  sorry

/-- If deg q < d and q annihilates C, and orbit gives standard basis, then q = 0 -/
lemma annihilator_degree_bound {d : ℕ} [NeZero d] {F : Type*} [Field F]
    (C : Matrix (Fin d) (Fin d) F)
    (horbit : ∀ k : Fin d, (C ^ k.val) *ᵥ (Pi.single 0 1) = Pi.single k 1)
    (q : F[X]) (hq : aeval C q = 0) (hdeg : q.natDegree < d) : q = 0 := by
  sorry

/-
  ## Section 3: Degree and Divisibility Arithmetic
-/

/-- Two monic polynomials with the same degree, one dividing the other, are equal -/
lemma monic_dvd_eq_of_same_degree {p q : F[X]} (hp : p.Monic) (hq : q.Monic)
    (hdvd : q ∣ p) (hdeg : p.natDegree = q.natDegree) : p = q := by
  sorry

/-- Monic polynomial of degree d has d + 1 coefficients -/
lemma monic_deg_d_card {p : F[X]} (hp : p.Monic) (hd : p.natDegree = d) :
    p.support.card ≤ d + 1 := by
  sorry

/-- natDegree of charpoly equals d for a d×d matrix -/
lemma charpoly_deg_eq_card {d : ℕ} [NeZero d] (C : Matrix (Fin d) (Fin d) F) :
    C.charpoly.natDegree = d := by
  sorry

/-
  ## Section 4: aeval Linearity
-/

/-- aeval distributes over matrix-vector multiplication -/
lemma aeval_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (p q : F[X]) :
    aeval M (p * q) = (aeval M p) * (aeval M q) := by
  sorry

/-- aeval M 1 = 1 -/
lemma aeval_one {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) : aeval M (1 : F[X]) = 1 := by
  sorry

end CayleyHamiltonOQ02OQ01.Aristotle
