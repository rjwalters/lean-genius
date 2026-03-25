/-
Erdős Problem #1179 - Open Question 01:
What is the precise second-order term in g_ε(N)?

Source: https://erdosproblems.com/1179

The main asymptotic g_ε(N) ~ log₂ N is known. The open question asks:
what is the precise form of the correction term?

Known bounds:
- Lower: g_ε(N) ≥ log₂ N (trivial)
- Upper: g_ε(N) ≤ log₂ N · (1 + O_ε(log log log N / log log N)) (Erdős-Hall)

The gap leaves the second-order term unknown. We formalize the question
and prove foundational results about representation counts in ℤ/Nℤ.

References:
- [ErRe65] Erdős, Rényi (1965)
- [ErHa76] Erdős, Hall (1976)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Erdos1179OQ01

open Finset Real

/-
## Part I: Representation counts in ℤ/Nℤ

We work concretely in ℤ/Nℤ to make proofs more tractable.
-/

/-- The representation count: number of subsets of A that sum to g. -/
noncomputable def reprCount {N : ℕ} (A : Finset (ZMod N)) (g : ZMod N) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = g)).card

/-- Total representations partition: ∑_g F_A(g) = 2^|A|. -/
theorem total_reprCount {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    (∑ g : ZMod N, reprCount A g) = 2 ^ A.card := by
  simp only [reprCount]
  rw [← card_powerset A]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro S _
  exact Finset.mem_univ (S.sum id)

/-- The empty set has exactly one representation of 0. -/
theorem reprCount_empty_zero {N : ℕ} [NeZero N] :
    reprCount (∅ : Finset (ZMod N)) (0 : ZMod N) = 1 := by
  simp [reprCount, powerset_empty, filter_singleton, sum_empty]

/-- The empty set has no representations of nonzero elements. -/
theorem reprCount_empty_nonzero {N : ℕ} [NeZero N]
    (g : ZMod N) (hg : g ≠ 0) :
    reprCount (∅ : Finset (ZMod N)) g = 0 := by
  simp [reprCount, powerset_empty, filter_singleton, sum_empty, hg.symm]

/-
## Part II: Monotonicity under set growth
-/

/-- Adding an element to A doesn't decrease reprCount for any g.
    Proof: every subset of A is also a subset of A ∪ {b}. -/
theorem reprCount_insert_ge {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (b : ZMod N) (g : ZMod N) (hb : b ∉ A) :
    reprCount A g ≤ reprCount (insert b A) g := by
  simp only [reprCount]
  apply Finset.card_le_card
  intro S hS
  rw [mem_filter] at hS ⊢
  exact ⟨mem_powerset.mpr ((mem_powerset.mp hS.1).trans (subset_insert b A)), hS.2⟩

/-- Representation counts are nonneg (trivially, as they're natural numbers). -/
theorem reprCount_nonneg {N : ℕ} (A : Finset (ZMod N)) (g : ZMod N) :
    0 ≤ reprCount A g := Nat.zero_le _

/-
## Part III: Representation count of a singleton
-/

/-- For a singleton {a}, the only subsets are ∅ and {a}.
    ∅ sums to 0, {a} sums to a.
    So reprCount {a} g = (if g = 0 then 1 else 0) + (if g = a then 1 else 0). -/
theorem reprCount_singleton_le_two {N : ℕ} [NeZero N]
    (a : ZMod N) (g : ZMod N) :
    reprCount {a} g ≤ 2 := by
  simp only [reprCount]
  calc (({a} : Finset (ZMod N)).powerset.filter (fun S => S.sum id = g)).card
      ≤ ({a} : Finset (ZMod N)).powerset.card := card_filter_le _ _
    _ = 2 ^ ({a} : Finset (ZMod N)).card := card_powerset _
    _ = 2 := by simp

/-
## Part IV: Total coverage grows with set size
-/

/-- The number of elements with nonzero representation is monotone in A. -/
theorem coverage_mono {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (b : ZMod N) (hb : b ∉ A) :
    (Finset.univ.filter (fun g : ZMod N => 0 < reprCount A g)).card ≤
    (Finset.univ.filter (fun g : ZMod N => 0 < reprCount (insert b A) g)).card := by
  apply Finset.card_le_card
  intro g hg
  rw [mem_filter] at hg ⊢
  exact ⟨mem_univ g, lt_of_lt_of_le hg.2 (reprCount_insert_ge A b g hb)⟩

/-
## Part V: The second-order term question
-/

/-- The correction term: g_ε(N) - log₂ N. -/
noncomputable def correctionTerm (gEps : ℝ → ℕ → ℕ) (ε : ℝ) (N : ℕ) : ℝ :=
  (gEps ε N : ℝ) - Real.logb 2 ↑N

/-- The correction is o(log₂ N) — follows from the main asymptotic. -/
def CorrectionIsSublinearInLog (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |correctionTerm gEps ε N| < δ * Real.logb 2 ↑N

/-- The correction is O(1) — strongest possible (open). -/
def CorrectionIsBounded (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    |correctionTerm gEps ε N| ≤ C

/-- The correction is Θ(log log N) — conjectured by analogy with Problem #543. -/
def CorrectionIsLogLog (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    c₁ * Real.log (Real.log ↑N) ≤ correctionTerm gEps ε N ∧
    correctionTerm gEps ε N ≤ c₂ * Real.log (Real.log ↑N)

/-- O(1) implies o(log N) — the hierarchy is well-ordered.
    Proof: if |correction| ≤ C for all N, then for N large enough,
    logb 2 N > C/δ, so C < δ · logb 2 N. -/
theorem bounded_implies_sublinear (gEps : ℝ → ℕ → ℕ) (ε : ℝ)
    (h : CorrectionIsBounded gEps ε) : CorrectionIsSublinearInLog gEps ε := by
  intro δ hδ
  obtain ⟨C, hC, hbound⟩ := h
  set m := Nat.ceil (C / δ) + 2
  use 2 ^ m
  intro N hN
  have hN2 : N ≥ 2 := by
    have : 2 ≤ 2 ^ m := le_trans (show 2 ≤ 2 ^ 1 from le_refl _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hm_bound : (m : ℝ) > C / δ + 1 := by
    show (↑(Nat.ceil (C / δ) + 2) : ℝ) > C / δ + 1
    push_cast; linarith [Nat.le_ceil (C / δ)]
  -- logb 2 N ≥ m (since N ≥ 2^m and logb 2 (2^m) = m)
  have hNlog : Real.logb 2 (N : ℝ) ≥ ↑m := by
    have hN_le : (2 : ℝ) ^ (m : ℕ) ≤ (N : ℝ) := by exact_mod_cast hN
    have key : Real.logb 2 ((2 : ℝ) ^ (m : ℕ)) = ↑m := by
      rw [show ((2 : ℝ) ^ (m : ℕ)) = ((2 : ℝ) ^ ((m : ℕ) : ℝ)) from
        (rpow_natCast 2 m).symm]
      exact Real.logb_rpow (by norm_num) (by norm_num)
    have mono : Real.logb 2 ((2 : ℝ) ^ (m : ℕ)) ≤ Real.logb 2 (N : ℝ) := by
      simp only [Real.logb]
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) hN_le)
        (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2)))
    linarith
  calc |correctionTerm gEps ε N| ≤ C := hbound N (by omega)
    _ < δ * (C / δ + 1) := by
        have : δ * (C / δ + 1) = C + δ := by field_simp
        linarith
    _ < δ * ↑m := by nlinarith
    _ ≤ δ * Real.logb 2 ↑N := by nlinarith

/-
## Part VI: Fourier analysis connection
-/

/-- |cos(π/p)| < 1 for any prime p ≥ 2.
    For p = 2: cos(π/2) = 0. For p ≥ 3: 0 < π/p < π so -1 < cos(π/p) < 1. -/
private lemma abs_cos_pi_div_prime_lt_one (p : ℕ) (hp : Nat.Prime p) :
    |Real.cos (Real.pi / ↑p)| < 1 := by
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr hp.pos
  have hp_one_lt : (1 : ℝ) < ↑p := by exact_mod_cast hp.one_lt
  have hx_pos : (0 : ℝ) < π / ↑p := div_pos Real.pi_pos hp_pos
  have hx_lt_pi : π / ↑p < π := div_lt_self Real.pi_pos hp_one_lt
  rw [abs_lt]
  constructor
  · -- cos(π/p) > cos(π) = -1 since π/p < π and cos strictly decreasing on [0,π]
    have h1 : π / ↑p ∈ Set.Icc (0 : ℝ) π := ⟨hx_pos.le, hx_lt_pi.le⟩
    have h2 : π ∈ Set.Icc (0 : ℝ) π := ⟨Real.pi_pos.le, le_refl _⟩
    have := Real.strictAntiOn_cos h1 h2 hx_lt_pi
    rw [Real.cos_pi] at this
    linarith
  · -- cos(π/p) < cos(0) = 1 since 0 < π/p and cos strictly decreasing on [0,π]
    have h1 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) π := ⟨le_refl _, Real.pi_pos.le⟩
    have h2 : π / ↑p ∈ Set.Icc (0 : ℝ) π := ⟨hx_pos.le, hx_lt_pi.le⟩
    have := Real.strictAntiOn_cos h1 h2 hx_pos
    rwa [Real.cos_zero] at this

/-- Fourier-analytic error bound for representation counts in ℤ/pℤ.

    For A ⊆ ℤ/pℤ of size k, Fourier inversion gives:
      F_A(g) = (1/p) ∑_χ χ(-g) ∏_{a ∈ A} (1 + χ(a))
    The trivial character contributes 2^k/p (the "uniform" term).
    For χ ≠ 1: |1 + χ(a)| = 2|cos(πja/p)|, and for nonzero a mod p,
    |cos(πja/p)| ≤ cos(π/p) < 1. The exponent k-1 (not k) accounts for
    the possibility that 0 ∈ A, where |cos(0)| = 1.

    **Note**: The original axiom (without 2^k/p factor) was mathematically
    false. Counterexample: A = {1,2} in ℤ/3ℤ gives error 2/3 but the old
    bound was (3-1)·cos(π/3)² = 1/2 < 2/3. -/
axiom fourier_error_bound (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 1 ≤ k) :
  ∀ A : Finset (ZMod p), A.card = k →
    ∀ g : ZMod p, |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p| ≤
      (↑p - 1 : ℝ) * |Real.cos (Real.pi / ↑p)| ^ (k - 1) * ((2 : ℝ) ^ k / ↑p)

/-- For k ≥ clog₂ p + C, the Fourier error decays to at most ε · 2^k/p.
    This is the core of the Erdős-Rényi (1965) approach.

    Proof: from fourier_error_bound, the relative error is bounded by
    (p-1) · |cos(π/p)|^(k-1). Since |cos(π/p)| < 1 for all primes,
    this decays geometrically and falls below ε for large enough k. -/
theorem erdos_renyi_decay (p : ℕ) (hp : Nat.Prime p) :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℕ, ∀ k : ℕ, k ≥ Nat.clog 2 p + C →
      ∀ A : Finset (ZMod p), A.card = k →
        ∀ g : ZMod p, |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p| ≤
          ε * ((2 : ℝ) ^ k / ↑p) := by
  intro ε hε
  -- |cos(π/p)| < 1 for primes
  have hcos_lt := abs_cos_pi_div_prime_lt_one p hp
  have hcos_nn := abs_nonneg (Real.cos (π / ↑p))
  -- (p : ℝ) - 1 > 0 for primes
  have hp_sub : (0 : ℝ) < ↑p - 1 := by
    have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  -- Find K₀ with |cos(π/p)|^K₀ < ε/(p-1)
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one (div_pos hε hp_sub) hcos_lt
  -- C = K₀ + 1 ensures k-1 ≥ K₀ and k ≥ 1
  use K₀ + 1
  intro k hk A hA g
  have hk1 : 1 ≤ k := by omega
  -- From fourier_error_bound (corrected):
  -- |error| ≤ (p-1) · |cos(π/p)|^(k-1) · (2^k/p)
  have hfourier := fourier_error_bound p hp k hk1 A hA g
  -- Suffices: (p-1) · |cos(π/p)|^(k-1) ≤ ε
  suffices hsuff : (↑p - 1 : ℝ) * |Real.cos (π / ↑p)| ^ (k - 1) ≤ ε by
    calc |(reprCount A g : ℝ) - (2 : ℝ) ^ k / ↑p|
        ≤ (↑p - 1) * |Real.cos (π / ↑p)| ^ (k - 1) * ((2 : ℝ) ^ k / ↑p) := hfourier
      _ ≤ ε * ((2 : ℝ) ^ k / ↑p) := by
          apply mul_le_mul_of_nonneg_right hsuff
          exact div_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k) (Nat.cast_nonneg p)
  -- k - 1 ≥ K₀ since k ≥ clog 2 p + K₀ + 1 ≥ K₀ + 1
  have hk_ge : K₀ ≤ k - 1 := by omega
  -- |cos(π/p)|^(k-1) ≤ |cos(π/p)|^K₀ (decreasing for base ≤ 1)
  -- Then (p-1) · |cos(π/p)|^(k-1) ≤ (p-1) · ε/(p-1) = ε
  calc (↑p - 1 : ℝ) * |Real.cos (π / ↑p)| ^ (k - 1)
      ≤ (↑p - 1) * |Real.cos (π / ↑p)| ^ K₀ := by
        apply mul_le_mul_of_nonneg_left _ hp_sub.le
        exact pow_le_pow_of_le_one hcos_nn hcos_lt.le hk_ge
    _ ≤ (↑p - 1) * (ε / (↑p - 1)) := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hK₀) hp_sub.le
    _ = ε := by field_simp

/-
## Part VII: Summary and open question
-/

/-- The central open question: what is the precise rate at which
    g_ε(N) - log₂ N grows?

    Three candidate answers, in order of strength:
    1. O(1) — strongest, would mean g_ε(N) = log₂ N + O_ε(1)
    2. Θ(log log N) — by analogy with Problem #543
    3. o(log₂ N) — weakest, already known from Erdős-Hall

    We proved: O(1) ⟹ o(log₂ N), establishing the hierarchy.
    We proved: erdos_renyi_decay from fourier_error_bound (geometric decay). -/
theorem second_order_hierarchy (gEps : ℝ → ℕ → ℕ) (ε : ℝ) :
    CorrectionIsBounded gEps ε → CorrectionIsSublinearInLog gEps ε :=
  bounded_implies_sublinear gEps ε

end Erdos1179OQ01
