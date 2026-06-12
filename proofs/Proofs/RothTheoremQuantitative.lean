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

/-- The Roth number r₃(N): the maximum cardinality of an AP-free subset
    of ZMod N. This is the central quantity in Roth's theorem.

    r₃(N) = max { |A| : A ⊆ ZMod N, A is AP-free }

    Defined as the supremum of the achievable AP-free cardinalities. This
    formulation needs no `Fintype (ZMod N)` instance, so it is total over all
    `N : ℕ`. When `N = 0` the set of AP-free cardinalities is unbounded (ℤ has
    arbitrarily large finite AP-free subsets), so `sSup` returns the junk value
    `0`; the definition is only meaningful for `N ≥ 1`. -/
noncomputable def rothNumber (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset (ZMod N), APFree A ∧ A.card = n}

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

/-- The set of AP-free cardinalities is nonempty (the empty set witnesses `0`). -/
private theorem apFreeCards_nonempty (N : ℕ) :
    {n | ∃ A : Finset (ZMod N), APFree A ∧ A.card = n}.Nonempty :=
  ⟨0, ∅, apFree_empty, Finset.card_empty⟩

/-- For `N ≥ 1` the AP-free cardinalities are bounded above by `N`. -/
private theorem bddAbove_apFreeCards (N : ℕ) [NeZero N] :
    BddAbove {n | ∃ A : Finset (ZMod N), APFree A ∧ A.card = n} := by
  refine ⟨N, ?_⟩
  rintro n ⟨A, -, rfl⟩
  calc A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    _ = N := ZMod.card N

/-- For N ≥ 2, ZMod N contains the 3-AP {0, 1, 2}, so is not AP-free. -/
theorem not_apFree_univ {N : ℕ} [NeZero N] (hN : 1 < N) :
    ¬APFree (Finset.univ : Finset (ZMod N)) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  intro h
  exact h 0 1 one_ne_zero (Finset.mem_univ _) (Finset.mem_univ _) (Finset.mem_univ _)

/-- r₃(N) ≤ N: no AP-free subset of ZMod N can exceed N elements. -/
theorem rothNumber_le (N : ℕ) [NeZero N] : rothNumber N ≤ N := by
  unfold rothNumber
  apply csSup_le (apFreeCards_nonempty N)
  rintro n ⟨A, -, rfl⟩
  calc A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    _ = N := ZMod.card N

/-- r₃(N) < N for N ≥ 2: the full ZMod N is never AP-free. -/
theorem rothNumber_lt {N : ℕ} (hN : 1 < N) : rothNumber N < N := by
  haveI : NeZero N := ⟨by omega⟩
  have h : rothNumber N ≤ N - 1 := by
    unfold rothNumber
    apply csSup_le (apFreeCards_nonempty N)
    rintro n ⟨A, hA, rfl⟩
    by_contra hgt
    push_neg at hgt
    have hcard : A.card = Fintype.card (ZMod N) := by
      have h1 : A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
      have h2 : Fintype.card (ZMod N) = N := ZMod.card N
      omega
    exact not_apFree_univ hN (Finset.eq_univ_of_card A hcard ▸ hA)
  omega

/-- r₃(N) ≤ N - 1 for N ≥ 2 (corollary of the strict bound). -/
theorem rothNumber_le_sub_one {N : ℕ} (hN : 1 < N) : rothNumber N ≤ N - 1 := by
  have := rothNumber_lt hN; omega

/-- r₃(N) ≥ 1 when N ≥ 1: any singleton is AP-free. -/
theorem rothNumber_pos (N : ℕ) [NeZero N] : 1 ≤ rothNumber N := by
  unfold rothNumber
  exact le_csSup (bddAbove_apFreeCards N) ⟨{0}, apFree_singleton 0, Finset.card_singleton 0⟩

/-- Any AP-free subset A of ZMod N satisfies |A| ≤ r₃(N). -/
theorem card_le_rothNumber {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (hA : APFree A) :
    A.card ≤ rothNumber N := by
  unfold rothNumber
  exact le_csSup (bddAbove_apFreeCards N) ⟨A, hA, rfl⟩

/-- The Roth number is achieved: there exists an AP-free set of maximum size. -/
theorem rothNumber_achieved {N : ℕ} [NeZero N] :
    ∃ A : Finset (ZMod N), APFree A ∧ A.card = rothNumber N := by
  unfold rothNumber
  obtain ⟨A, hA, hcard⟩ :=
    Nat.sSup_mem (apFreeCards_nonempty N) (bddAbove_apFreeCards N)
  exact ⟨A, hA, hcard⟩

/-- The pair {0, 1} is AP-free in ZMod N for N ≥ 3.

    If a, a+d ∈ {0,1} with d ≠ 0 then either a=0,d=1 (so a+2d=2 ∉ {0,1},
    as 2 ≠ 0 and 2 ≠ 1 since 2 < N) or a=1,d=-1 (so a+2d=-1 ∉ {0,1},
    as -1 ≠ 0 and -1 ≠ 1, the latter because 2 ≠ 0). -/
theorem apFree_pair {N : ℕ} (hN : 3 ≤ N) : APFree ({0, 1} : Finset (ZMod N)) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hv2 : (2 : ZMod N).val = 2 := by
    show ((2 : ℕ) : ZMod N).val = 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hv0 : (0 : ZMod N).val = 0 := ZMod.val_zero
  have hv1 : (1 : ZMod N).val = 1 := ZMod.val_one N
  have val_inj : ∀ x y : ZMod N, x = y → x.val = y.val := fun _ _ h => congr_arg ZMod.val h
  have h2ne0 : (2 : ZMod N) ≠ 0 :=
    fun h => by have := val_inj _ _ h; rw [hv2, hv0] at this; omega
  have h2ne1 : (2 : ZMod N) ≠ 1 :=
    fun h => by have := val_inj _ _ h; rw [hv2, hv1] at this; omega
  have hn1ne0 : (-1 : ZMod N) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hn1ne1 : (-1 : ZMod N) ≠ 1 := fun h => h2ne0 (by linear_combination -h)
  intro a d hd ha had
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha had
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases ha with rfl | rfl <;> rcases had with h | h
  · simp only [zero_add] at h; exact absurd h hd
  · simp only [zero_add] at h; subst h
    simp only [zero_add, mul_one]; exact ⟨h2ne0, h2ne1⟩
  · have hd_eq : d = -1 := by linear_combination h
    subst hd_eq
    have h_simp : (1 : ZMod N) + 2 * (-1) = -1 := by ring
    rw [h_simp]; exact ⟨hn1ne0, hn1ne1⟩
  · have hd_eq : d = 0 := by linear_combination h
    exact absurd hd_eq hd

/-- r₃(N) ≥ 2 for N ≥ 3: the pair {0, 1} is an AP-free witness of size 2.
    Generalizes the lower bound in `rothNumber_three` to all N ≥ 3. -/
theorem rothNumber_ge_two {N : ℕ} (hN : 3 ≤ N) : 2 ≤ rothNumber N := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  have h01 : (0 : ZMod N) ≠ 1 := zero_ne_one
  have hcard : ({0, 1} : Finset (ZMod N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact h01),
      Finset.card_singleton]
  calc 2 = ({0, 1} : Finset (ZMod N)).card := hcard.symm
    _ ≤ rothNumber N := card_le_rothNumber _ (apFree_pair hN)

/-- r₃(2) = 1: in ZMod 2, every 2-element set contains the AP {0, 1, 0}. -/
theorem rothNumber_two : rothNumber 2 = 1 := by
  have h1 : rothNumber 2 < 2 := rothNumber_lt (by omega)
  have h2 : 1 ≤ rothNumber 2 := rothNumber_pos 2
  omega

/-- r₃(3) = 2: {0, 1} is AP-free in ZMod 3 (the size-2 witness), and the
    full set is not AP-free. -/
theorem rothNumber_three : rothNumber 3 = 2 := by
  have hlt : rothNumber 3 < 3 := rothNumber_lt (by omega)
  have hge : 2 ≤ rothNumber 3 := rothNumber_ge_two (by norm_num)
  omega

/-- r₃(1) = 1: ZMod 1 is trivial, so its only AP-free set is the singleton. -/
theorem rothNumber_one : rothNumber 1 = 1 := by
  have h1 : rothNumber 1 ≤ 1 := rothNumber_le 1
  have h2 : 1 ≤ rothNumber 1 := rothNumber_pos 1
  omega

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

/-- If the linear density estimate δ + kδ²/100 stays ≤ 1, then the real
    iteration count is bounded: k ≤ 100/δ².

    From δ + kδ²/100 ≤ 1 and δ > 0 we get kδ²/100 ≤ 1 - δ ≤ 1, so kδ² ≤ 100. -/
theorem iterations_before_contradiction (delta : ℝ) (hdelta : 0 < delta) (k : ℕ)
    (hk : delta + k * delta ^ 2 / 100 ≤ 1) :
    (k : ℝ) ≤ 100 / delta ^ 2 := by
  have hd2 : delta ^ 2 > 0 := by positivity
  rw [le_div_iff₀ hd2]
  nlinarith [hk, hdelta]

/-- The density increment gives an explicit iteration bound:
    if density starts at δ, then after k increments of δ²/100 each,
    the density reaches δ + kδ²/100. For this to stay ≤ 1, we need
    k ≤ ⌊100/δ²⌋. -/
theorem max_iterations_bound (delta : ℝ) (hdelta : 0 < delta) (k : ℕ)
    (hk : delta + k * delta ^ 2 / 100 ≤ 1) :
    k ≤ ⌊100 / delta ^ 2⌋₊ :=
  Nat.le_floor (iterations_before_contradiction delta hdelta k hk)

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
