/-
  Smith Normal Form — the solvability criterion is DERIVED, not assumed
  (bezout-identity-oq-04-oq-01-oq-03)

  The parent gallery entry `bezout-identity-oq-04-oq-01` (Linear Diophantine Systems
  via Smith Normal Form) carries TWO axioms:

    * `snf_exists`               — every integer matrix A admits a decomposition
                                   A = U * D * V with U, V unimodular and D diagonal;
    * `snf_solvability_criterion`— A x = b is solvable over ℤ iff a divisibility
                                   condition holds on a transformed right-hand side.

  This file answers the open question "can these axioms be eliminated using Mathlib's
  existing infrastructure?" with a precise, two-part finding:

  1. **`snf_exists` is genuinely missing from Mathlib in matrix form.** Mathlib has the
     module-theoretic Smith Normal Form (`Module.Basis.SmithNormalForm`,
     `Submodule.smithNormalForm` in `Mathlib/LinearAlgebra/FreeModule/PID.lean`): for a
     PID `R` and submodule `N ≤ M`, there are bases of `M` and `N` and a divisibility
     chain of scalars `a i` with `bN i = a i • bM (f i)`. It does NOT provide the
     *matrix* statement `D = U A V` with explicit unimodular integer matrices `U, V`.
     Bridging the two (image-of-the-map submodule ↔ change-of-basis matrices, with the
     change-of-basis matrices shown unimodular) is the ~hundreds-of-lines gap that made
     the original author axiomatize `snf_exists`. We do not close that gap here.

  2. **`snf_solvability_criterion` is NOT an independent assumption.** Given the
     decomposition `A = U * D * V` (i.e. assuming only `snf_exists`), the solvability
     criterion is a *theorem* of elementary matrix algebra — proved below with **zero
     axioms**. Hence the parent's axiom count can drop from 2 to 1.

     A subtle bookkeeping point falls out of the derivation: with the parent's own
     convention `A = U * D * V`, the transformed right-hand side is `U⁻¹ * b`, NOT
     `U * b`. The parent's `snf_solvability_criterion` axiom writes `snf.U.mulVec b`,
     which is the `U⁻¹` of this convention. The corrected, derivable statement uses the
     genuine inverse `U⁻¹`, as proved in `diophantine_solvable_iff` below.

  Everything here is over a general `Fin m × Fin n` integer matrix (rectangular), so it
  covers the parent's 1×2 Bézout specialisation as a particular case.

  Verified: 0 sorries, 0 axioms (foundational `propext`/`Classical.choice`/`Quot.sound`
  only). The decomposition itself is taken as a hypothesis, so importing this file adds
  no assumptions.
-/
import Mathlib

namespace BezoutIdentityOQ04OQ01OQ03

open Matrix

/-! ## The diagonal entry of a rectangular "diagonal" matrix

We say `D : Matrix (Fin m) (Fin n) ℤ` is diagonal when `D i j = 0` whenever the index
values differ. Its `i`-th diagonal entry `dEntry D i` is `D i ⟨i, _⟩` when the column
`i` exists (`i < n`) and `0` otherwise. -/

/-- The `i`-th diagonal entry of a (possibly rectangular) matrix: `D i i` if the column
    index `i` is in range, else `0`. -/
def dEntry {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) : ℤ :=
  if h : (i : ℕ) < n then D i ⟨i, h⟩ else 0

/-- For a diagonal matrix, `mulVec` collapses to a single product on each row:
    `(D *ᵥ y) i = D i ⟨i,_⟩ * y ⟨i,_⟩` when `i < n`, and `0` otherwise. -/
theorem diag_mulVec_apply {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℤ)
    (hD : ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0)
    (y : Fin n → ℤ) (i : Fin m) :
    (D *ᵥ y) i = if h : (i : ℕ) < n then D i ⟨i, h⟩ * y ⟨i, h⟩ else 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  by_cases h : (i : ℕ) < n
  · rw [dif_pos h]
    rw [Finset.sum_eq_single (⟨i, h⟩ : Fin n)]
    · intro j _ hj
      have : i.val ≠ j.val := by
        intro hcontra
        exact hj (Fin.ext hcontra.symm)
      rw [hD i j this, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have : i.val ≠ j.val := by
      intro hcontra
      exact h (hcontra ▸ j.isLt)
    rw [hD i j this, zero_mul]

/-! ## Solvability of a diagonal system

`∃ y, D *ᵥ y = c` holds iff every diagonal entry divides the corresponding component of
`c`.  Over ℤ the divisibility `d ∣ c` already encodes both branches of the parent's
criterion: when `d ≠ 0` it is ordinary divisibility, and when `d = 0` it is exactly
`c = 0` (`0 ∣ c ↔ c = 0`). -/
theorem diag_solvable_iff {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℤ)
    (hD : ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0) (c : Fin m → ℤ) :
    (∃ y : Fin n → ℤ, D *ᵥ y = c) ↔ ∀ i : Fin m, dEntry D i ∣ c i := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [diag_mulVec_apply D hD y i]
    simp only [dEntry]
    by_cases h : (i : ℕ) < n
    · simp only [dif_pos h]; exact dvd_mul_right _ _
    · simp only [dif_neg h]; exact dvd_zero 0
  · intro hdiv
    -- build the witness column vector
    refine ⟨fun j => if hjm : (j : ℕ) < m then c ⟨j, hjm⟩ / D ⟨j, hjm⟩ j else 0, ?_⟩
    funext i
    rw [diag_mulVec_apply D hD _ i]
    have hdi := hdiv i
    simp only [dEntry] at hdi
    by_cases h : (i : ℕ) < n
    · simp only [dif_pos h]
      rw [dif_pos h] at hdi
      -- the column ⟨i, h⟩ : Fin n has value i.val < m, so the inner `if` fires
      have him : (i : ℕ) < m := i.isLt
      rw [dif_pos him]
      -- ⟨i.val, him⟩ = i  in Fin m
      have e1 : (⟨i.val, him⟩ : Fin m) = i := Fin.ext rfl
      rw [e1]
      rcases eq_or_ne (D i ⟨i, h⟩) 0 with hz | hz
      · rw [hz, zero_mul]
        rw [hz] at hdi
        exact (zero_dvd_iff.mp hdi).symm
      · rw [Int.mul_ediv_cancel' hdi]
    · simp only [dif_neg h]
      rw [dif_neg h] at hdi
      exact (zero_dvd_iff.mp hdi).symm

/-! ## The solvability criterion, derived from the decomposition

This is the content of the parent's `snf_solvability_criterion` axiom, proved here as a
theorem from `snf_exists` alone (the decomposition `A = U * D * V` is the hypothesis).
The transformed right-hand side is the genuine inverse `U⁻¹ *ᵥ b`. -/

/-- A `±1` determinant is a unit of `ℤ` (so the matrix is invertible over `ℤ`). -/
theorem isUnit_det_of_unimodular {k : ℕ} {M : Matrix (Fin k) (Fin k) ℤ}
    (h : M.det = 1 ∨ M.det = -1) : IsUnit M.det := by
  rcases h with h | h
  · rw [h]; exact isUnit_one
  · rw [h]; exact isUnit_one.neg

/-- **Solvability criterion for linear Diophantine systems** (derived, 0-axiom).
    Given `A = U * D * V` with `U`, `V` invertible over `ℤ` and `D` diagonal, the system
    `A x = b` is solvable over `ℤ` iff every diagonal invariant factor of `D` divides the
    corresponding component of the transformed right-hand side `U⁻¹ * b`. -/
theorem diophantine_solvable_iff {m n : ℕ}
    (U : Matrix (Fin m) (Fin m) ℤ) (D : Matrix (Fin m) (Fin n) ℤ)
    (V : Matrix (Fin n) (Fin n) ℤ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : A = U * D * V) (hUdet : IsUnit U.det) (hVdet : IsUnit V.det)
    (hD : ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0) :
    (∃ x : Fin n → ℤ, A *ᵥ x = b) ↔ ∀ i : Fin m, dEntry D i ∣ (U⁻¹ *ᵥ b) i := by
  rw [← diag_solvable_iff D hD (U⁻¹ *ᵥ b)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨V *ᵥ x, ?_⟩
    have hUb : U *ᵥ (D *ᵥ (V *ᵥ x)) = b := by
      rw [mulVec_mulVec, mulVec_mulVec, ← hA]; exact hx
    have key : U⁻¹ *ᵥ (U *ᵥ (D *ᵥ (V *ᵥ x))) = D *ᵥ (V *ᵥ x) := by
      rw [mulVec_mulVec (D *ᵥ (V *ᵥ x)) U⁻¹ U, nonsing_inv_mul U hUdet, one_mulVec]
    rw [← key, hUb]
  · rintro ⟨y, hy⟩
    refine ⟨V⁻¹ *ᵥ y, ?_⟩
    rw [hA]
    have hVy : V *ᵥ (V⁻¹ *ᵥ y) = y := by
      rw [mulVec_mulVec, mul_nonsing_inv V hVdet, one_mulVec]
    calc (U * D * V) *ᵥ (V⁻¹ *ᵥ y)
        = U *ᵥ (D *ᵥ (V *ᵥ (V⁻¹ *ᵥ y))) := by
          rw [← mulVec_mulVec, ← mulVec_mulVec]
      _ = U *ᵥ (D *ᵥ y) := by rw [hVy]
      _ = U *ᵥ (U⁻¹ *ᵥ b) := by rw [hy]
      _ = b := by rw [mulVec_mulVec, mul_nonsing_inv U hUdet, one_mulVec]

/-- Over `ℤ`, `d ∣ c` is exactly the parent axiom's two-pronged branch condition. -/
theorem int_dvd_iff_branches (d c : ℤ) :
    d ∣ c ↔ (d ≠ 0 → d ∣ c) ∧ (d = 0 → c = 0) := by
  constructor
  · intro h
    exact ⟨fun _ => h, fun hd => by rw [hd] at h; exact zero_dvd_iff.mp h⟩
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne d 0 with hd | hd
    · rw [hd, zero_dvd_iff]; exact h2 hd
    · exact h1 hd

/-- **Solvability criterion in the parent's exact two-pronged shape** (derived, 0-axiom).
    This is `snf_solvability_criterion` from `bezout-identity-oq-04-oq-01`, but with the
    transformed right-hand side `U⁻¹ *ᵥ b` (the genuine inverse) — the convention-correct
    form for the decomposition `A = U * D * V`. -/
theorem diophantine_solvable_iff_branches {m n : ℕ}
    (U : Matrix (Fin m) (Fin m) ℤ) (D : Matrix (Fin m) (Fin n) ℤ)
    (V : Matrix (Fin n) (Fin n) ℤ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : A = U * D * V) (hUdet : IsUnit U.det) (hVdet : IsUnit V.det)
    (hD : ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0) :
    (∃ x : Fin n → ℤ, A *ᵥ x = b) ↔
      ∀ i : Fin m,
        (dEntry D i ≠ 0 → dEntry D i ∣ (U⁻¹ *ᵥ b) i) ∧
        (dEntry D i = 0 → (U⁻¹ *ᵥ b) i = 0) := by
  rw [diophantine_solvable_iff U D V A b hA hUdet hVdet hD]
  exact forall_congr' fun i => int_dvd_iff_branches _ _

end BezoutIdentityOQ04OQ01OQ03

