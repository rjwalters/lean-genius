/-
  Quantitative Bounds for Roth's Theorem

  Formalizes the Roth number r₃(N) — the maximum size of a 3-AP-free
  subset of {0, ..., N-1} — and states quantitative bounds.

  Part I: Definition of r₃(N) and basic properties
  Part II: Iteration bound from density increment
  Part III: Statement of quantitative bounds (Roth, Behrend, Kelley-Meka)

  Builds on RothTheorem.lean which proves the qualitative r₃(N) = o(N).
-/
import Mathlib
import Proofs.RothTheorem

namespace Szemeredi.Roth.Quantitative

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE ROTH NUMBER r₃(N)
-- ═══════════════════════════════════════════════════════════════════

/-- A subset A of ZMod N is AP-free if it contains no 3-term arithmetic
    progression a, a+d, a+2d with d ≠ 0. -/
def APFree {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ a d : ZMod N, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2 * d ∉ A

/-- A single global (noncomputable, classical) decidability instance for `APFree`.

    Every `Finset.filter (fun A => APFree A)` site in this file — the
    `rothNumber` definition and the theorems that unfold it — elaborates
    against this one instance, so the filtered sets are syntactically equal
    and unify. Without it, instance synthesis fails on Mathlib v4.26.0
    (`APFree` is a plain `def`, invisible to typeclass resolution), and
    per-theorem `classical` patches produce filter terms that do NOT unify
    with the one inside `rothNumber`. -/
noncomputable instance {N : ℕ} : DecidablePred (@APFree N) :=
  fun _ => Classical.dec _

/-- The Roth number r₃(N): the maximum cardinality of an AP-free subset
    of ZMod N. This is the central quantity in Roth's theorem.

    r₃(N) = max { |A| : A ⊆ ZMod N, A is AP-free }

    When N = 0, ZMod 0 = ℤ is infinite, so `Finset.univ` does not exist
    (`Fintype (ZMod N)` requires `NeZero N`); we assign the junk value 0.
    All substantive theorems assume `NeZero N` and work through the
    equation lemma `rothNumber_def`. -/
noncomputable def rothNumber (N : ℕ) : ℕ :=
  if h : N = 0 then 0
  else
    haveI : NeZero N := ⟨h⟩
    Finset.sup (Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A))
      Finset.card

/-- Equation lemma for `rothNumber` in the meaningful case `N ≠ 0`. -/
theorem rothNumber_def {N : ℕ} [NeZero N] :
    rothNumber N =
      Finset.sup (Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A))
        Finset.card :=
  dif_neg (NeZero.ne N)

/-- The empty set is AP-free. -/
theorem apFree_empty {N : ℕ} : APFree (∅ : Finset (ZMod N)) := by
  intro a d _ ha
  exact absurd ha (Finset.notMem_empty a)

/-- A singleton set is AP-free. -/
theorem apFree_singleton {N : ℕ} (x : ZMod N) : APFree ({x} : Finset (ZMod N)) := by
  intro a d hd ha had _
  rw [Finset.mem_singleton] at ha had
  apply hd
  have : a + d - a = x - a := congr_arg (· - a) had
  simp only [add_sub_cancel_left] at this
  rw [ha] at this; simp at this; exact this

/-- Subsets of AP-free sets are AP-free. -/
theorem apFree_subset {N : ℕ} {A B : Finset (ZMod N)} (h : B ⊆ A) (hA : APFree A) :
    APFree B :=
  fun a d hd ha had hadd => hA a d hd (h ha) (h had) (h hadd)

/-- For N ≥ 2, ZMod N contains the 3-AP {0, 1, 2}, so is not AP-free.
    (`NeZero N` is needed for `Finset.univ` to exist in the statement.) -/
theorem not_apFree_univ {N : ℕ} [NeZero N] (hN : 1 < N) :
    ¬APFree (Finset.univ : Finset (ZMod N)) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  intro h
  exact h 0 1 one_ne_zero (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _)

/-- r₃(N) ≤ N: no AP-free subset of ZMod N can exceed N elements. -/
theorem rothNumber_le (N : ℕ) [NeZero N] : rothNumber N ≤ N := by
  rw [rothNumber_def]
  apply Finset.sup_le
  intro A hA
  rw [Finset.mem_filter] at hA
  calc A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    _ = N := ZMod.card N

/-- r₃(N) < N for N ≥ 2: the full ZMod N is never AP-free. -/
theorem rothNumber_lt {N : ℕ} (hN : 1 < N) : rothNumber N < N := by
  haveI : NeZero N := ⟨by omega⟩
  rw [rothNumber_def, Finset.sup_lt_iff (show (0 : ℕ) < N by omega)]
  intro A hA
  rw [Finset.mem_filter] at hA
  by_contra hge; push_neg at hge
  have hcard : A.card = Fintype.card (ZMod N) := by
    have h1 : A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    have h2 : Fintype.card (ZMod N) = N := ZMod.card N
    omega
  exact absurd (Finset.eq_univ_of_card A hcard ▸ hA.2) (not_apFree_univ hN)

/-- r₃(N) ≤ N - 1 for N ≥ 2 (corollary of the strict bound). -/
theorem rothNumber_le_sub_one {N : ℕ} (hN : 1 < N) : rothNumber N ≤ N - 1 := by
  have := rothNumber_lt hN; omega

/-- r₃(N) ≥ 1 when N ≥ 1: any singleton is AP-free. -/
theorem rothNumber_pos (N : ℕ) [NeZero N] : 1 ≤ rothNumber N := by
  rw [rothNumber_def]
  have hset : ({0} : Finset (ZMod N)) ∈
      Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), apFree_singleton 0⟩
  calc 1 = ({0} : Finset (ZMod N)).card := by simp
    _ ≤ Finset.sup (Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A))
          Finset.card :=
        Finset.le_sup hset

/-- Any AP-free subset A of ZMod N satisfies |A| ≤ r₃(N).
    (`NeZero N` is required: for N = 0 the junk value `rothNumber 0 = 0`
    is exceeded by any AP-free singleton in ZMod 0 = ℤ.) -/
theorem card_le_rothNumber {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (hA : APFree A) :
    A.card ≤ rothNumber N := by
  rw [rothNumber_def]
  apply Finset.le_sup
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hA⟩

/-- The Roth number is achieved: there exists an AP-free set of maximum size. -/
theorem rothNumber_achieved {N : ℕ} [NeZero N] :
    ∃ A : Finset (ZMod N), APFree A ∧ A.card = rothNumber N := by
  have hne : (Finset.univ.powerset.filter
      (fun A : Finset (ZMod N) => APFree A)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), apFree_empty⟩⟩
  obtain ⟨A, hAS, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  refine ⟨A, (Finset.mem_filter.mp hAS).2, ?_⟩
  rw [rothNumber_def]
  exact le_antisymm (Finset.le_sup hAS) (Finset.sup_le fun B hB => hmax B hB)

/-- r₃(2) = 1: in ZMod 2, every 2-element set contains the AP {0, 1, 0}. -/
theorem rothNumber_two : rothNumber 2 = 1 := by
  have h1 : rothNumber 2 < 2 := rothNumber_lt (by omega)
  have h2 : 1 ≤ rothNumber 2 := rothNumber_pos 2
  omega

/-- r₃(3) = 2: {0, 1} is AP-free in ZMod 3, and the full set is not. -/
theorem rothNumber_three : rothNumber 3 = 2 := by
  have hlt : rothNumber 3 < 3 := rothNumber_lt (by omega)
  suffices 2 ≤ rothNumber 3 by omega
  apply card_le_rothNumber ({0, 1} : Finset (ZMod 3))
  -- Unfold `APFree` by defeq so `decide` can use the computable
  -- `Fintype (ZMod 3)` instances (the global `APFree` instance is
  -- classical and does not evaluate).
  show ∀ a d : ZMod 3, d ≠ 0 → a ∈ ({0, 1} : Finset (ZMod 3)) →
    a + d ∈ ({0, 1} : Finset (ZMod 3)) → a + 2 * d ∉ ({0, 1} : Finset (ZMod 3))
  decide

-- ═══════════════════════════════════════════════════════════════════
-- PART I.B: QUALITATIVE ROTH ASYMPTOTIC
-- ═══════════════════════════════════════════════════════════════════

/-- The two `APFree` definitions (here in `Szemeredi.Roth.Quantitative` and
    in the parent `Szemeredi.Roth`) have identical bodies. -/
private lemma apFree_to_parent {N : ℕ} {A : Finset (ZMod N)} (h : APFree A) :
    Szemeredi.Roth.APFree A :=
  fun a d hd ha had => h a d hd ha had

/-- **Qualitative Roth asymptotic** over `ZMod N`: `r₃(N)/N → 0` as `N → ∞`.

    This is the qualitative content of Roth's theorem for the cyclic-group
    setting: the maximum density of an AP-free subset of `ZMod N` tends to
    zero. The quantitative theorems in Part III (all sorried) sharpen this
    to explicit decay rates from Roth (1953) through Kelley–Meka (2023).

    The proof reduces to `Szemeredi.Roth.roth_density_bound`, which routes
    through Mathlib's `roth_3ap_theorem_nat` via the corners-theorem chain
    (Regularity Lemma → Triangle Removal → Corners → Roth). -/
theorem rothNumber_div_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => (rothNumber N : ℝ) / N) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Reduce to `δ = min ε 1 ∈ (0, 1]` so we can invoke `roth_density_bound`.
  set δ := min ε 1 with hδ_def
  have hδ_pos : 0 < δ := lt_min hε one_pos
  have hδ_le_one : δ ≤ 1 := min_le_right _ _
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  obtain ⟨N₀, hN₀⟩ := Szemeredi.Roth.roth_density_bound δ hδ_pos hδ_le_one
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hN₀_le : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1_le : 1 ≤ N := (le_max_right _ _).trans hN
  haveI : NeZero N := ⟨by omega⟩
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN1_le
  -- `|rothNumber N / N - 0| = rothNumber N / N` (both numerator and denominator nonneg).
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_pos hN_pos, div_lt_iff₀ hN_pos]
  -- Suffices to show `rothNumber N < δ * N`, since `δ ≤ ε` and `N ≥ 0`.
  suffices h : (rothNumber N : ℝ) < δ * N by
    calc (rothNumber N : ℝ) < δ * N := h
      _ ≤ ε * N := by
          have hN_nn : (0 : ℝ) ≤ N := le_of_lt hN_pos
          exact mul_le_mul_of_nonneg_right hδ_le_ε hN_nn
  by_contra hge
  push_neg at hge  -- `(rothNumber N : ℝ) ≥ δ * N`
  obtain ⟨A, hA_free, hA_card⟩ := rothNumber_achieved (N := N)
  have hA_dens : (A.card : ℝ) ≥ δ * N := by rw [hA_card]; exact hge
  exact hN₀ N hN₀_le A hA_dens (apFree_to_parent hA_free)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: ITERATION BOUND FROM DENSITY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

-- NOTE: max_iterations_bound (δ + kδ²/100 > 1 → k > ⌊100/δ²⌋₊) was REMOVED.
-- The statement is FALSE for δ > 1: with δ = 2, k = 0 the hypothesis holds
-- (2 > 1) but the conclusion demands 0 > ⌊25⌋₊ = 25. Only the weaker bound
-- k > 100(1-δ)/δ² follows from the hypothesis; no extra side condition
-- (including δ ≤ 1) recovers the stated bound. See S3 session memo
-- (research/problems/roth-theorem-k3-oq-01-incomplete-01, 2026-06-01).

/-- If density δ > 0 satisfies δ + kδ²/100 ≤ 1 (i.e., k increments of
    δ²/100 starting from δ have not yet pushed the density past 1),
    then k ≤ 100/δ². -/
theorem iterations_before_contradiction (delta : ℝ) (hdelta : 0 < delta) (k : ℕ)
    (hk : delta + k * delta ^ 2 / 100 ≤ 1) :
    (k : ℝ) ≤ 100 / delta ^ 2 := by
  have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
  rw [le_div_iff₀ hd2]
  -- From the hypothesis, k·δ²/100 ≤ 1 - δ ≤ 1, hence k·δ² ≤ 100.
  linarith

-- NOTE: density_upper_bound_from_iteration (δ² ≤ 100/N) was REMOVED.
-- The claim r₃(N) ≤ 10√N is FALSE for large N:
-- Behrend (1946) gives r₃(N) ≥ N·exp(-c√(log N)) >> √N.
-- The density increment lemma gives M < N with no lower bound on M,
-- so the iteration cannot yield quantitative bounds without a modulus
-- decay rate (e.g., M ≥ N^{2/3} in Roth's analysis).

-- ═══════════════════════════════════════════════════════════════════
-- PART III: QUANTITATIVE BOUNDS (STATEMENTS)
-- ═══════════════════════════════════════════════════════════════════

/-- **Roth's quantitative bound** (1953): r₃(N) ≤ C·N/log(log N).

    Roth's density increment gives density increase δ → δ + δ²/100 with
    M ≥ N^c at each step. After ⌊log₂(log N)⌋ iterations, the modulus
    reaches O(1), so density must have reached 1. This forces
    ⌊100/δ²⌋ ≥ ⌊log₂(log N)⌋, giving δ ≤ C/√(log log N).
    Roth's more careful analysis (tracking M ≥ N^{2/3}) gives C/log(log N). -/
theorem roth_quantitative_upper_bound :
    ∃ (C : ℝ), C > 0 ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumber N : ℝ) ≤ C * N / Real.log (Real.log N) := by
  sorry

/-- **Behrend's lower bound** (1946): r₃(N) ≥ N·exp(-c·√(log N)).

    Behrend constructed large AP-free sets by projecting lattice points
    on a high-dimensional sphere onto a residue class. The construction
    uses the fact that d-dimensional spheres contain many lattice points
    but no 3-term APs (since a + c = 2b and ‖a‖ = ‖b‖ = ‖c‖ on a
    sphere forces a = c, hence a = b = c).

    This lower bound has remained essentially optimal for 80 years. -/
theorem behrend_lower_bound :
    ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumber N : ℝ) ≥ N * Real.exp (-c * Real.sqrt (Real.log N)) := by
  sorry

/-- **Bloom-Sisask bound** (2020): r₃(N) ≤ N/(log N)^{1+c}.

    Broke the long-standing "logarithmic barrier" in Roth's theorem.
    Previous bounds (Bourgain 1999, 2008; Sanders 2011) could not
    surpass N/(log N)^{1-ε}. -/
theorem bloom_sisask_bound :
    ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumber N : ℝ) ≤ N / (Real.log N) ^ (1 + c) := by
  sorry

/-- **Kelley-Meka bound** (2023): r₃(N) ≤ N·exp(-c·(log N)^{1/12}).

    The breakthrough result approaching the Behrend lower bound.
    Uses density increment on Bohr sets with improved spectral analysis.

    Gap remaining: Behrend gives exp(-c√(log N)), Kelley-Meka gives
    exp(-c(log N)^{1/12}). Closing this gap is a major open problem. -/
theorem kelley_meka_upper_bound :
    ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumber N : ℝ) ≤ N * Real.exp (-c * (Real.log N) ^ (1/12 : ℝ)) := by
  sorry

-- NOTE: The previously stated crude_sqrt_bound (r₃(N) ≤ 10√N) was FALSE.
-- Behrend's lower bound gives r₃(N) ≥ N·exp(-c√(log N)) >> √N for large N.
-- The proof sketch (iterate density_increment N times) does not work because
-- density_increment_lemma gives M < N with no lower bound on M.
-- For quantitative bounds, need M ≥ N^c (e.g., M ≥ N^{2/3} in Roth's analysis).

end Szemeredi.Roth.Quantitative
