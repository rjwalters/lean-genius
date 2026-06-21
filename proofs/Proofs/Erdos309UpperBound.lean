/-
Erdős Problem #309 — The Trivial (Axiom-Free) Upper Bound  F(N) ≤ log N + 2

Source: https://erdosproblems.com/309

How many integers can be written as a sum of distinct unit fractions with
denominators from {1,…,N}?  Writing F(N) for that count, Erdős asked whether
F(N) = o(log N).  The answer is NO: F(N) = log N + γ + O((log log N)²/log N)
(Yokota 1997/2002, Croot 1999), so F(N) = Θ(log N).

The parent file `Erdos309Problem.lean` records the SOLVED status, with the hard
lower direction stated as the axiom `yokota_lower_bound_1997`.  That file no
longer builds against Mathlib 4.26.0 (its imports `Mathlib.Data.Rat.Basic`,
`Mathlib.Data.Rat.Order`, `Mathlib.Algebra.BigOperators.Group.Finset` were
removed/relocated upstream), so this file is deliberately **self-contained**:
it re-declares the handful of definitions it needs and imports only
`Mathlib.NumberTheory.Harmonic.Bounds`.

What is proved here, with ZERO axioms:

* `harmonicNumber_eq_harmonic`  — the file's harmonic number equals Mathlib's
  `harmonic`, the bridge that unlocks Mathlib's analytic estimates.
* `countRepresentable_le_floor_harmonic` — every representable integer lies in
  `{0,…,⌊H_N⌋}`, so `F(N) ≤ ⌊H_N⌋ + 1`.
* `countRepresentable_le_log_add_two` — the headline elementary upper bound
  `F(N) ≤ log N + 2`, the "trivial upper bound" of the literature, here fully
  machine-checked via Mathlib's `harmonic_le_one_add_log`.
* `two_le_countRepresentable` — the matching (trivial) lower bound `F(N) ≥ 2`.
* `countRepresentable_bracket` — `2 ≤ F(N) ≤ log N + 2` for `N ≥ 1`.

This is the *upper* (easy/known) half of Erdős #309.  The matching log-order
*lower* bound is the deep Yokota direction and is NOT reproved here.
-/
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset BigOperators Real Classical

namespace Erdos309UpperBound

/-! ## Definitions (self-contained mirror of the parent file) -/

/-- The reciprocal `1/n` for a positive natural number `n` (and `0` at `n = 0`). -/
noncomputable def unitFraction (n : ℕ) : ℚ :=
  if n = 0 then 0 else 1 / n

/-- Sum of unit fractions over a finite set of denominators. -/
noncomputable def sumUnitFractions (S : Finset ℕ) : ℚ :=
  ∑ d ∈ S, unitFraction d

/-- The denominator range `{1, 2, …, N}`. -/
def denominatorRange (N : ℕ) : Finset ℕ := Finset.range (N + 1) \ {0}

/-- The harmonic number `H_N = ∑_{d=1}^{N} 1/d`. -/
noncomputable def harmonicNumber (N : ℕ) : ℚ :=
  sumUnitFractions (denominatorRange N)

/-- `k` is representable if `k = ∑_{d ∈ S} 1/d` for some `S ⊆ {1,…,N}`. -/
def IsRepresentable (N k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ denominatorRange N ∧ sumUnitFractions S = k

/-- `F(N)`: the number of representable integers (bounded by `H_N`, so it
suffices to search `{0,…,N}`). -/
noncomputable def countRepresentable (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun k => IsRepresentable N k)).card

/-! ## Basic facts -/

theorem mem_denominatorRange (N n : ℕ) :
    n ∈ denominatorRange N ↔ 1 ≤ n ∧ n ≤ N := by
  simp only [denominatorRange, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
  omega

theorem unitFraction_nonneg (n : ℕ) : 0 ≤ unitFraction n := by
  rcases eq_or_ne n 0 with h | h
  · simp [unitFraction, h]
  · simp only [unitFraction, if_neg h]; positivity

theorem harmonicNumber_nonneg (N : ℕ) : 0 ≤ harmonicNumber N := by
  rw [harmonicNumber, sumUnitFractions]
  exact Finset.sum_nonneg (fun d _ => unitFraction_nonneg d)

theorem zero_representable (N : ℕ) : IsRepresentable N 0 :=
  ⟨∅, Finset.empty_subset _, by simp [sumUnitFractions]⟩

theorem one_representable (N : ℕ) (hN : N ≥ 1) : IsRepresentable N 1 := by
  refine ⟨{1}, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact (mem_denominatorRange N 1).mpr ⟨le_refl 1, hN⟩
  · simp [sumUnitFractions, unitFraction]

/-- Any representable integer is at most `H_N`: its representing set is a subset
of the full denominator range, and all unit fractions are nonnegative. -/
theorem max_representable_le_harmonic (N k : ℕ) (hk : IsRepresentable N k) :
    (k : ℚ) ≤ harmonicNumber N := by
  obtain ⟨S, hS, hsum⟩ := hk
  rw [← hsum, harmonicNumber, sumUnitFractions, sumUnitFractions]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun d _ _ => unitFraction_nonneg d)

/-! ## The bridge to Mathlib's `harmonic` -/

/-- The file's `harmonicNumber` coincides with Mathlib's `harmonic`. -/
theorem harmonicNumber_eq_harmonic (N : ℕ) :
    harmonicNumber N = harmonic N := by
  rw [harmonic_eq_sum_Icc, harmonicNumber, sumUnitFractions]
  have hset : denominatorRange N = Finset.Icc 1 N := by
    ext d
    rw [mem_denominatorRange, Finset.mem_Icc]
  rw [hset]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  simp only [unitFraction, if_neg (by omega : d ≠ 0), one_div]

/-! ## The upper bound -/

/-- The representable integers all lie in `{0, 1, …, ⌊H_N⌋}`, so there are at
most `⌊H_N⌋ + 1` of them. -/
theorem countRepresentable_le_floor_harmonic (N : ℕ) :
    countRepresentable N ≤ ⌊harmonicNumber N⌋₊ + 1 := by
  rw [countRepresentable]
  calc ((Finset.range (N + 1)).filter (fun k => IsRepresentable N k)).card
      ≤ (Finset.range (⌊harmonicNumber N⌋₊ + 1)).card := by
        apply Finset.card_le_card
        intro k hk
        rw [Finset.mem_filter] at hk
        rw [Finset.mem_range]
        have hle : (k : ℚ) ≤ harmonicNumber N := max_representable_le_harmonic N k hk.2
        have : k ≤ ⌊harmonicNumber N⌋₊ := Nat.le_floor hle
        omega
    _ = ⌊harmonicNumber N⌋₊ + 1 := Finset.card_range _

/-- **The trivial upper bound, axiom-free:** `F(N) ≤ log N + 2`.

Chains `F(N) ≤ ⌊H_N⌋ + 1 ≤ H_N + 1` with Mathlib's `harmonic_le_one_add_log`
(`H_N ≤ 1 + log N`). -/
theorem countRepresentable_le_log_add_two (N : ℕ) :
    (countRepresentable N : ℝ) ≤ Real.log N + 2 := by
  have hfloor : countRepresentable N ≤ ⌊harmonicNumber N⌋₊ + 1 :=
    countRepresentable_le_floor_harmonic N
  have step1 : (countRepresentable N : ℝ) ≤ (⌊harmonicNumber N⌋₊ : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hfloor
    push_cast at this
    linarith
  have step2 : (⌊harmonicNumber N⌋₊ : ℝ) ≤ (harmonicNumber N : ℝ) := by
    calc (⌊harmonicNumber N⌋₊ : ℝ) = ((⌊harmonicNumber N⌋₊ : ℚ) : ℝ) := by push_cast; ring
      _ ≤ (harmonicNumber N : ℝ) := by exact_mod_cast Nat.floor_le (harmonicNumber_nonneg N)
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have hEq : (harmonicNumber N : ℝ) = (harmonic N : ℝ) := by
    rw [harmonicNumber_eq_harmonic]
  calc (countRepresentable N : ℝ)
      ≤ (⌊harmonicNumber N⌋₊ : ℝ) + 1 := step1
    _ ≤ (harmonicNumber N : ℝ) + 1 := by linarith
    _ = (harmonic N : ℝ) + 1 := by rw [hEq]
    _ ≤ (1 + Real.log N) + 1 := by linarith
    _ = Real.log N + 2 := by ring

/-! ## The (trivial) lower bound and the bracket -/

/-- `0` and `1` are both representable for `N ≥ 1`, so `F(N) ≥ 2`. -/
theorem two_le_countRepresentable (N : ℕ) (hN : N ≥ 1) :
    2 ≤ countRepresentable N := by
  rw [countRepresentable]
  have hsub : {0, 1} ⊆ (Finset.range (N + 1)).filter (fun k => IsRepresentable N k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h <;> subst h <;>
      rw [Finset.mem_filter, Finset.mem_range]
    · exact ⟨by omega, zero_representable N⟩
    · exact ⟨by omega, one_representable N hN⟩
  calc 2 = ({0, 1} : Finset ℕ).card := by decide
    _ ≤ _ := Finset.card_le_card hsub

/-- **Bracket for Erdős #309's counting function:** `2 ≤ F(N) ≤ log N + 2`
for `N ≥ 1`.  The upper bound is sharp up to the additive constant; the matching
*log-order lower bound* `F(N) ≥ log N − O(log log N)` is the deep Yokota
direction (axiomatized in the parent file) and is not reproved here. -/
theorem countRepresentable_bracket (N : ℕ) (hN : N ≥ 1) :
    (2 : ℝ) ≤ (countRepresentable N : ℝ) ∧
    (countRepresentable N : ℝ) ≤ Real.log N + 2 :=
  ⟨by exact_mod_cast two_le_countRepresentable N hN, countRepresentable_le_log_add_two N⟩

end Erdos309UpperBound
