/-
Erdős Problem #1179: Uniform Subset Sum Representations in Abelian Groups

  Source: https://erdosproblems.com/1179
  Status: PROVED (answered in the affirmative)

  Statement:
  For 0 < ε < 1, let g_ε(N) be the minimal k such that: if G is an abelian
  group of size N and A ⊆ G is a uniformly random subset of size k, then with
  probability → 1 as N → ∞, the representation function

    F_A(g) = #{S ⊆ A : ∑_{x ∈ S} x = g}

  satisfies |F_A(g) - 2^k/N| ≤ ε · 2^k/N for all g ∈ G.

  Question: Estimate g_ε(N). In particular, is g_ε(N) = (1 + o_ε(1)) log₂ N?

  Answer: YES (for the main asymptotic).

  Known Results:
  - Trivial lower bound: g_ε(N) ≥ log₂ N (need 2^k ≥ N representations)
  - Erdős-Rényi (1965): g_ε(N) ≤ (2 + o(1)) log₂ N + O_ε(1)
  - Erdős-Hall (1976): g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N

  Relation to Problem #543:
  Problem #543 asks about spanning (every element represented at least once).
  Problem #1179 is stronger: every element must have approximately the same
  number of representations (≈ 2^k/N each).

  References:
  - [ErRe65] Erdős, Rényi: Probabilistic Methods in Group Theory (1965)
  - [ErHa76] Erdős, Hall (1976)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos1179

open Finset Real

/- ## Part I: Representation Counts -/

-- The number of subsets of A whose elements sum to g.
-- F_A(g) = #{S ⊆ A : ∑_{x ∈ S} x = g}
noncomputable def reprCount {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = g)).card

-- The expected representation count: 2^k / N
noncomputable def expectedReprCount (k N : ℕ) : ℝ :=
  (2 : ℝ) ^ k / N

/- ## Part II: Uniformity of Representations -/

-- A set A has ε-uniform representations if for every g ∈ G,
-- the representation count F_A(g) is within ε of the expected value.
def IsEpsUniform {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (ε : ℝ) : Prop :=
  ∀ g : G, |((reprCount A g : ℝ) - expectedReprCount A.card (Fintype.card G))|
    ≤ ε * expectedReprCount A.card (Fintype.card G)

/- ## Part III: Elementary Properties -/

-- Total representations: ∑_g F_A(g) = 2^|A|.
-- Each subset S ⊆ A sums to exactly one element, so the counts partition 2^|A|.
theorem total_reprCount {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) : (∑ g : G, reprCount A g) = 2 ^ A.card := by
  simp only [reprCount]
  rw [← card_powerset A]
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro S hS
  exact Finset.mem_univ (S.sum id)

-- The empty set represents only 0 (via the empty subset).
theorem reprCount_empty_zero {G : Type*} [AddCommGroup G] [DecidableEq G] :
    reprCount (∅ : Finset G) (0 : G) = 1 := by
  simp [reprCount, powerset_empty, filter_singleton, sum_empty]

-- The empty set gives 0 representations for nonzero elements.
theorem reprCount_empty_nonzero {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) : reprCount (∅ : Finset G) g = 0 := by
  simp [reprCount, powerset_empty, filter_singleton, sum_empty, hg.symm]

/- ## Part IV: The Function g_ε(N) -/

-- g_ε(N) is the minimal k such that a random k-subset of any abelian group
-- of size N has ε-uniform representations with high probability.
-- Axiomatized since it requires quantification over all groups and
-- probabilistic convergence.
axiom gEps (ε : ℝ) (N : ℕ) : ℕ

-- g_ε is well-defined for valid parameters.
axiom gEps_pos (ε : ℝ) (N : ℕ) (hε : 0 < ε) (hε1 : ε < 1) (hN : N ≥ 2) :
    gEps ε N ≥ 1

/- ## Part V: Trivial Lower Bound -/

-- **Trivial lower bound:** g_ε(N) ≥ log₂ N for all 0 < ε < 1.
--
-- Proof sketch: A set of size k has 2^k subsets. For the representation counts
-- to be approximately uniform at 2^k/N ≈ 1 per element, we need 2^k ≥ N,
-- which means k ≥ log₂ N. More precisely, if k < log₂ N then 2^k < N,
-- so total representations < N, meaning some element has F_A(g) = 0, which
-- prevents ε-uniformity for ε < 1.
axiom trivial_lower_bound (ε : ℝ) (N : ℕ) (hε : 0 < ε) (hε1 : ε < 1) (hN : N ≥ 2) :
    (gEps ε N : ℝ) ≥ Real.logb 2 N

/- ## Part VI: Upper Bounds -/

-- **Erdős-Rényi (1965):** g_ε(N) ≤ (2 + o(1)) log₂ N + O_ε(1).
--
-- The proof uses second moment method: for a random k-subset A,
-- when k ≈ 2 log₂ N, the variance is small enough relative to the
-- mean that concentration occurs.
axiom erdos_renyi_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      (gEps ε N : ℝ) ≤ 2 * Real.logb 2 N + C

-- **Erdős-Hall (1976):** Improved upper bound.
--
-- g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) · log₂ N
--
-- This brings the leading coefficient from 2 down to 1 + o(1).
-- The proof uses character sum estimates and large deviation bounds.
axiom erdos_hall_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      (gEps ε N : ℝ) ≤ (1 + C * Real.log (Real.log (Real.log ↑N)) /
        Real.log (Real.log ↑N)) * Real.logb 2 ↑N

/- ## Part VII: The Main Result -/

-- The asymptotic answer: g_ε(N) = (1 + o_ε(1)) · log₂ N.
--
-- Combining the trivial lower bound g_ε(N) ≥ log₂ N with the
-- Erdős-Hall upper bound gives g_ε(N) / log₂ N → 1 as N → ∞.
axiom main_asymptotic (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      |((gEps ε N : ℝ) / Real.logb 2 ↑N) - 1| < δ

/- ## Part VIII: Comparison with Problem #543 -/

-- Problem #543 defines f(N) = min k such that random k-subset spans G.
-- Problem #1179 defines g_ε(N) = min k for ε-uniform representations.
--
-- Spanning is weaker than ε-uniformity:
-- if representations are ε-uniform (for any ε < 1), then every element
-- has at least (1-ε) · 2^k/N > 0 representations, so the set spans.
theorem uniform_implies_spanning {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (A : Finset G) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hk : A.card ≥ Nat.clog 2 (Fintype.card G))
    (hunif : IsEpsUniform A ε) :
    ∀ g : G, reprCount A g ≥ 1 := by
  intro g
  -- From ε-uniformity: |F(g) - μ| ≤ ε·μ where μ = 2^k/N
  have hunif_g := hunif g
  set μ := expectedReprCount A.card (Fintype.card G) with hμ_def
  -- From |F(g) - μ| ≤ ε·μ we get F(g) ≥ (1-ε)·μ
  have hge : (reprCount A g : ℝ) ≥ (1 - ε) * μ := by
    have h := (abs_le.mp hunif_g).1
    nlinarith
  -- Show μ ≥ 1: since k ≥ ⌈log₂ N⌉, we have 2^k ≥ N, so μ = 2^k/N ≥ 1
  have hN_pos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hμ_ge : μ ≥ 1 := by
    rw [hμ_def, ge_iff_le, ← sub_nonneg]
    simp only [expectedReprCount]
    have h2k : (Fintype.card G : ℝ) ≤ (2 : ℝ) ^ A.card := by
      have h1 := (Nat.le_pow_clog (show 1 < 2 by omega) (Fintype.card G)).trans
        (Nat.pow_le_pow_right (show 0 < 2 by omega) hk)
      exact_mod_cast h1
    rw [show (2 : ℝ) ^ A.card / ↑(Fintype.card G) - 1 =
      ((2 : ℝ) ^ A.card - ↑(Fintype.card G)) / ↑(Fintype.card G) from by field_simp]
    exact div_nonneg (by linarith) (by linarith)
  -- So (reprCount A g : ℝ) ≥ (1-ε)·1 = 1-ε > 0
  have hpos : (reprCount A g : ℝ) > 0 := by nlinarith
  -- A natural number that's > 0 as a real is ≥ 1
  have : reprCount A g ≠ 0 := by intro h; simp [h] at hpos
  omega

/- ## Part IX: Monotonicity -/

-- g_ε is non-increasing in ε: tighter tolerance requires more elements.
axiom gEps_mono (ε₁ ε₂ : ℝ) (N : ℕ) (h : ε₁ ≤ ε₂)
    (hε₁ : 0 < ε₁) (hε₂ : ε₂ < 1) (hN : N ≥ 2) :
    gEps ε₁ N ≥ gEps ε₂ N

/- ## Part X: Summary -/

-- **Summary of Erdős Problem #1179:**
--
-- The function g_ε(N) satisfies:
-- - Lower bound: g_ε(N) ≥ log₂ N (trivial, from counting)
-- - Upper bound: g_ε(N) ≤ (1 + o(1)) log₂ N (Erdős-Hall 1976)
-- - Main result: g_ε(N) ~ log₂ N as N → ∞
--
-- In contrast to Problem #543 (spanning) where f(N) = log₂ N + Θ(log log N),
-- the extra log log N is needed for spanning but NOT for approximate uniformity.
theorem erdos_1179_summary (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∀ N : ℕ, N ≥ 2 → (gEps ε N : ℝ) ≥ Real.logb 2 ↑N) ∧
    (∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      |((gEps ε N : ℝ) / Real.logb 2 ↑N) - 1| < δ) :=
  ⟨fun N hN => trivial_lower_bound ε N hε hε1 hN,
   main_asymptotic ε hε hε1⟩

end Erdos1179
