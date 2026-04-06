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

namespace Szemeredi.Roth.Quantitative

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE ROTH NUMBER r₃(N)
-- ═══════════════════════════════════════════════════════════════════

/-- A subset A of ZMod N is AP-free if it contains no 3-term arithmetic
    progression a, a+d, a+2d with d ≠ 0. -/
def APFree {N : ℕ} (A : Finset (ZMod N)) : Prop :=
  ∀ a d : ZMod N, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2 * d ∉ A

/-- The Roth number r₃(N): the maximum cardinality of an AP-free subset
    of ZMod N. This is the central quantity in Roth's theorem.

    r₃(N) = max { |A| : A ⊆ ZMod N, A is AP-free }

    Note: When N = 0, ZMod 0 = ℤ and Finset.univ is not finite, so
    this definition is only meaningful for N ≥ 1 (where ZMod N is finite). -/
noncomputable def rothNumber (N : ℕ) : ℕ :=
  Finset.sup (Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A))
    Finset.card

/-- The empty set is AP-free. -/
theorem apFree_empty {N : ℕ} : APFree (∅ : Finset (ZMod N)) := by
  intro a d _ ha
  exact absurd ha (Finset.not_mem_empty a)

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

/-- For N ≥ 2, ZMod N contains the 3-AP {0, 1, 2}, so is not AP-free. -/
theorem not_apFree_univ {N : ℕ} (hN : 1 < N) :
    ¬APFree (Finset.univ : Finset (ZMod N)) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  intro h
  exact h 0 1 one_ne_zero (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _)

/-- r₃(N) ≤ N: no AP-free subset of ZMod N can exceed N elements. -/
theorem rothNumber_le (N : ℕ) [NeZero N] : rothNumber N ≤ N := by
  unfold rothNumber
  apply Finset.sup_le
  intro A hA
  rw [Finset.mem_filter] at hA
  calc A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    _ = N := ZMod.card N

/-- r₃(N) < N for N ≥ 2: the full ZMod N is never AP-free. -/
theorem rothNumber_lt {N : ℕ} (hN : 1 < N) : rothNumber N < N := by
  haveI : NeZero N := ⟨by omega⟩
  unfold rothNumber
  rw [Finset.sup_lt_iff (show (0 : ℕ) < N by omega)]
  intro A hA
  rw [Finset.mem_filter] at hA
  by_contra hge; push_neg at hge
  have hcard : A.card = Fintype.card (ZMod N) :=
    le_antisymm (Finset.card_le_univ A) (ZMod.card N ▸ hge)
  exact absurd (Finset.eq_univ_of_card A hcard ▸ hA.2) (not_apFree_univ hN)

/-- r₃(N) ≤ N - 1 for N ≥ 2 (corollary of the strict bound). -/
theorem rothNumber_le_sub_one {N : ℕ} (hN : 1 < N) : rothNumber N ≤ N - 1 := by
  have := rothNumber_lt hN; omega

/-- r₃(N) ≥ 1 when N ≥ 1: any singleton is AP-free. -/
theorem rothNumber_pos (N : ℕ) [NeZero N] : 1 ≤ rothNumber N := by
  unfold rothNumber
  have hset : ({0} : Finset (ZMod N)) ∈
      Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), apFree_singleton 0⟩
  calc 1 = ({0} : Finset (ZMod N)).card := by simp
    _ ≤ Finset.sup (Finset.univ.powerset.filter (fun A => APFree A)) Finset.card :=
        Finset.le_sup hset

/-- Any AP-free subset A of ZMod N satisfies |A| ≤ r₃(N). -/
theorem card_le_rothNumber {N : ℕ} (A : Finset (ZMod N)) (hA : APFree A) :
    A.card ≤ rothNumber N := by
  unfold rothNumber
  apply Finset.le_sup
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hA⟩

/-- The Roth number is achieved: there exists an AP-free set of maximum size. -/
theorem rothNumber_achieved {N : ℕ} [NeZero N] :
    ∃ A : Finset (ZMod N), APFree A ∧ A.card = rothNumber N := by
  set S := Finset.univ.powerset.filter (fun A : Finset (ZMod N) => APFree A)
  have hne : S.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), apFree_empty⟩⟩
  obtain ⟨A, hAS, hmax⟩ := Finset.exists_max_image S Finset.card hne
  exact ⟨A, (Finset.mem_filter.mp hAS).2,
    le_antisymm (Finset.le_sup hAS) (Finset.sup_le fun B hB => hmax B hB)⟩

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
  intro a d hd ha had hadd
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha had hadd
  fin_cases a <;> fin_cases d <;> simp_all

-- ═══════════════════════════════════════════════════════════════════
-- PART II: ITERATION BOUND FROM DENSITY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

/-- The density increment gives an explicit iteration bound:
    if density starts at δ, then after k increments of δ²/100 each,
    the density reaches δ + kδ²/100. For this to stay ≤ 1, we need
    k ≤ ⌊100/δ²⌋. -/
theorem max_iterations_bound (delta : ℝ) (hdelta : 0 < delta) :
    ∀ k : ℕ, delta + k * delta ^ 2 / 100 > 1 → k > ⌊100 / delta ^ 2⌋₊ := by
  intro k hk
  by_contra h
  push_neg at h
  have hd2 : delta ^ 2 > 0 := by positivity
  have hk_le : (k : ℝ) ≤ ⌊100 / delta ^ 2⌋₊ := Nat.cast_le.mpr h
  have hfloor : (⌊100 / delta ^ 2⌋₊ : ℝ) ≤ 100 / delta ^ 2 := Nat.floor_le (by positivity)
  have hk_bound : (k : ℝ) ≤ 100 / delta ^ 2 := le_trans hk_le hfloor
  have hkd : k * delta ^ 2 / 100 ≤ 1 := by
    rw [div_le_one (by norm_num : (100 : ℝ) > 0)]
    calc (k : ℝ) * delta ^ 2
        ≤ (100 / delta ^ 2) * delta ^ 2 :=
          mul_le_mul_of_nonneg_right hk_bound (le_of_lt hd2)
      _ = 100 := by field_simp
  linarith

/-- Contrapositive form: if density δ satisfies δ + kδ²/100 ≤ 1, then
    we can perform at least k density increments. -/
theorem iterations_before_contradiction (delta : ℝ) (hdelta : 0 < delta) (k : ℕ)
    (hk : delta + k * delta ^ 2 / 100 ≤ 1) :
    (k : ℝ) ≤ 100 / delta ^ 2 := by
  have hd2 : delta ^ 2 > 0 := by positivity
  rw [div_le_iff (by norm_num : (100 : ℝ) > 0)] at hk
  linarith [mul_comm (k : ℝ) (delta ^ 2)]

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
