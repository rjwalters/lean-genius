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

/-- In ℤ/pℤ (p prime), the Fourier error bound controls reprCount deviations.
    F_A(g) = (1/p) ∑_χ χ(-g) ∏_{a ∈ A} (1 + χ(a)).
    The χ ≠ 1 terms contribute at most (p-1) · |cos(π/p)|^k. -/
axiom fourier_error_bound (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
  ∀ A : Finset (ZMod p), A.card = k →
    ∀ g : ZMod p, |(reprCount A g : ℝ) - (2 : ℝ) ^ k / p| ≤
      (p - 1 : ℝ) * |Real.cos (Real.pi / p)| ^ k

/-- For k ≈ 2 log₂ p, the Fourier error decays to O(1/p).
    This is the core of the Erdős-Rényi (1965) approach. -/
axiom erdos_renyi_decay (p : ℕ) (hp : Nat.Prime p) :
  ∀ ε : ℝ, ε > 0 → ∃ C : ℕ, ∀ k : ℕ, k ≥ Nat.clog 2 p + C →
    ∀ A : Finset (ZMod p), A.card = k →
      ∀ g : ZMod p, |(reprCount A g : ℝ) - (2 : ℝ) ^ k / p| ≤
        ε * ((2 : ℝ) ^ k / p)

/-
## Part VII: Summary and open question
-/

/-- The central open question: what is the precise rate at which
    g_ε(N) - log₂ N grows?

    Three candidate answers, in order of strength:
    1. O(1) — strongest, would mean g_ε(N) = log₂ N + O_ε(1)
    2. Θ(log log N) — by analogy with Problem #543
    3. o(log₂ N) — weakest, already known from Erdős-Hall

    We proved: O(1) ⟹ o(log₂ N), establishing the hierarchy. -/
theorem second_order_hierarchy (gEps : ℝ → ℕ → ℕ) (ε : ℝ) :
    CorrectionIsBounded gEps ε → CorrectionIsSublinearInLog gEps ε :=
  bounded_implies_sublinear gEps ε

end Erdos1179OQ01
