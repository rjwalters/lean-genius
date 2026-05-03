/-
# Omega-Fold Origami: Algebraic Completeness (OQ-05-OQ-02)

Open Question from angle-trisection-oq-05-oq-01:
"Can multi-fold origami solve ALL polynomial equations (is it algebraically complete)?"

## The Answer

YES: omega-fold origami (allowing arbitrary many simultaneous folds) is
algebraically complete. Every polynomial equation of positive degree d
is solvable by omega-fold origami operations.

## Proof Strategy

From AngleTrisectionOQ05OQ01:
- k-fold origami constructs degrees d that are p_{k+1}-smooth
- `eventually_constructible`: for d > 0, using k = d folds suffices
  (since p_{d+1} ≥ d+2 > d ≥ any prime factor of d, by Bertrand's postulate direction)

We define omega-fold constructibility as ∃ k, IsKFoldConstructible d k
and prove the sharp characterization: omega-fold constructible ↔ d > 0.

## Status: Verified (0 axioms, 0 sorries)
-/

import Proofs.AngleTrisectionOQ05OQ01
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace AngleTrisectionOQ05OQ02

open AngleTrisectionOQ05OQ01 Nat

/-
══════════════════════════════════════════════════════════════
PART I: OMEGA-FOLD CONSTRUCTIBILITY
══════════════════════════════════════════════════════════════ -/

/-- A degree d is omega-fold constructible if it is k-fold constructible for SOME k.
    This is the existential closure over all fold levels. -/
def IsOmegaFoldConstructible (d : ℕ) : Prop :=
  ∃ k : ℕ, IsKFoldConstructible d k

/-
══════════════════════════════════════════════════════════════
PART II: BASIC PROPERTIES
══════════════════════════════════════════════════════════════ -/

/-- Degree 1 is omega-fold constructible. -/
theorem omega_fold_one : IsOmegaFoldConstructible 1 :=
  ⟨1, degree_one_constructible 1 (by omega)⟩

/-- If d is k-fold constructible, it is omega-fold constructible. -/
theorem omega_fold_of_kfold {d k : ℕ} (h : IsKFoldConstructible d k) :
    IsOmegaFoldConstructible d :=
  ⟨k, h⟩

/-- Degree d is d-fold constructible when d ≥ 1:
    foldPrimeBound(d) = p_{d+1} ≥ d+2 > d ≥ any prime factor of d. -/
theorem kfold_self {d : ℕ} (hd : d ≥ 1) : IsKFoldConstructible d d := by
  refine ⟨by omega, by omega, fun q hq hqd => ?_⟩
  have hqle : q ≤ d := Nat.le_of_dvd (by omega) hqd
  have hbound : d + 2 ≤ foldPrimeBound d := by
    unfold foldPrimeBound
    exact add_two_le_nth_prime d
  omega

/-- Every degree d ≥ 1 is omega-fold constructible. -/
theorem omega_fold_pos {d : ℕ} (hd : d ≥ 1) : IsOmegaFoldConstructible d :=
  ⟨d, kfold_self hd⟩

/-
══════════════════════════════════════════════════════════════
PART III: SHARP CHARACTERIZATION
══════════════════════════════════════════════════════════════ -/

/-- Degree 0 is NOT omega-fold constructible.
    The IsSmooth condition requires d > 0. -/
theorem not_omega_fold_zero : ¬ IsOmegaFoldConstructible 0 := by
  intro ⟨k, _, hpos, _⟩
  omega

/-- **Main theorem**: A degree d is omega-fold constructible iff d > 0.
    Omega-fold origami is algebraically complete: it can solve every
    polynomial equation of positive degree. -/
theorem omega_fold_complete_iff {d : ℕ} :
    IsOmegaFoldConstructible d ↔ d > 0 := by
  constructor
  · intro ⟨_, _, hpos, _⟩
    exact hpos
  · intro hd
    exact omega_fold_pos hd

/-
══════════════════════════════════════════════════════════════
PART IV: FOLD LEVEL GROWTH
══════════════════════════════════════════════════════════════ -/

/-- For any d > 0, every fold level k ≥ d suffices to construct d.
    The minimum number of folds needed for degree d is at most d. -/
theorem eventually_all_folds_sufficient {d : ℕ} (hd : d > 0) :
    ∀ k : ℕ, k ≥ d → IsKFoldConstructible d k := by
  intro k hkd
  obtain ⟨_, hd_pos, hsm⟩ := kfold_self (by omega : d ≥ 1)
  refine ⟨by omega, hd_pos, fun q hq hqd => ?_⟩
  have hqle : q ≤ d := Nat.le_of_dvd hd hqd
  have hbound : d + 2 ≤ foldPrimeBound k := by
    unfold foldPrimeBound
    have h1 : d ≤ k := hkd
    have h2 : d + 2 ≤ k + 2 := by omega
    have h3 : k + 2 ≤ foldPrimeBound k := add_two_le_nth_prime k
    omega
  omega

/-- For any degree d > 0, the minimum fold level needed is finite and at most d.
    This gives the explicit bound: `d` folds always suffice. -/
theorem min_folds_finite {d : ℕ} (hd : d > 0) :
    ∃ k_min : ℕ, k_min ≤ d ∧ IsKFoldConstructible d k_min := by
  exact ⟨d, le_refl d, kfold_self (by omega)⟩

/-
══════════════════════════════════════════════════════════════
PART V: PRIME FOLD THRESHOLDS
══════════════════════════════════════════════════════════════ -/

/-- For a prime p, the minimum fold level needed is determined by its prime index:
    p is k-fold constructible iff p ≤ foldPrimeBound k. -/
theorem prime_kfold_iff_bound {p k : ℕ} (hp : p.Prime) (hk : k ≥ 1) :
    IsKFoldConstructible p k ↔ p ≤ foldPrimeBound k := by
  constructor
  · intro ⟨_, _, hsm⟩
    exact hsm p hp (dvd_refl p)
  · intro hle
    refine ⟨hk, hp.pos, fun q hq hqd => ?_⟩
    have : q = p := (hp.eq_one_or_self_of_dvd q hqd).resolve_left hq.one_lt.ne'
    omega

/-- Any degree d > 0 is omega-fold constructible. Omega-fold origami is
    algebraically complete: there is no positive-degree polynomial equation
    that omega-fold origami cannot solve. -/
theorem omega_fold_algebraically_complete :
    ∀ d : ℕ, d > 0 → IsOmegaFoldConstructible d :=
  fun d hd => omega_fold_complete_iff.mpr hd

/-
══════════════════════════════════════════════════════════════
PART VI: CONCRETE EXAMPLES
══════════════════════════════════════════════════════════════ -/

/-- Degree 2 (quadratic) is omega-fold constructible. -/
theorem omega_degree_2 : IsOmegaFoldConstructible 2 := omega_fold_complete_iff.mpr (by norm_num)

/-- Degree 3 (cubic, angle trisection) is omega-fold constructible. -/
theorem omega_degree_3 : IsOmegaFoldConstructible 3 := omega_fold_complete_iff.mpr (by norm_num)

/-- Degree 5 (quintic, Abel-Ruffini) is omega-fold constructible. -/
theorem omega_degree_5 : IsOmegaFoldConstructible 5 := omega_fold_complete_iff.mpr (by norm_num)

/-- Degree 7 is omega-fold constructible. -/
theorem omega_degree_7 : IsOmegaFoldConstructible 7 := omega_fold_complete_iff.mpr (by norm_num)

/-- Degree 11 (separates 3-fold from 4-fold) is omega-fold constructible. -/
theorem omega_degree_11 : IsOmegaFoldConstructible 11 := omega_fold_complete_iff.mpr (by norm_num)

/-- Large degree 100 is omega-fold constructible (100 folds suffice). -/
theorem omega_degree_100 : IsOmegaFoldConstructible 100 := omega_fold_complete_iff.mpr (by norm_num)

/-- Degree 0 is the unique non-constructible degree. -/
theorem omega_fold_zero_unique_failure :
    ∀ d : ℕ, ¬ IsOmegaFoldConstructible d ↔ d = 0 := by
  intro d
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rfl
    · exact absurd (omega_fold_complete_iff.mpr hd) h
  · rintro rfl
    exact not_omega_fold_zero

/-
══════════════════════════════════════════════════════════════
PART VII: FOLD LEVEL COMPARISON
══════════════════════════════════════════════════════════════ -/

/-- Omega-fold subsumes k-fold: every k-fold constructible degree is omega-fold constructible. -/
theorem kfold_le_omega {d k : ℕ} (h : IsKFoldConstructible d k) :
    IsOmegaFoldConstructible d :=
  ⟨k, h⟩

/-- The omega-fold threshold is the supremum of all fold levels:
    omega-fold constructible means constructible by SOME finite fold level. -/
theorem omega_fold_as_union {d : ℕ} :
    IsOmegaFoldConstructible d ↔ ∃ k : ℕ, IsKFoldConstructible d k :=
  Iff.rfl

end AngleTrisectionOQ05OQ02
