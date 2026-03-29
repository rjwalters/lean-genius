/-
Erdős Problem #1005: Farey Fractions and Similar Ordering

Let a₁/b₁, a₂/b₂, ... be the Farey fractions of order n ≥ 4.
Let f(n) be the largest integer such that if 1 ≤ k < l ≤ k + f(n)
then a_k/b_k and a_l/b_l are "similarly ordered": (a_k - a_l)(b_k - b_l) ≥ 0.

Estimate f(n). Is there a constant c > 0 such that f(n) = (c + o(1))n?

**Status**: OPEN
**Known**: (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1) (van Doorn 2025)

Reference: https://erdosproblems.com/1005
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

open Finset

namespace Erdos1005

/-
## Farey Fractions

The Farey sequence F_n consists of all reduced fractions a/b
with 0 ≤ a ≤ b ≤ n and gcd(a,b) = 1, in increasing order.
-/

/-- A Farey fraction is a pair (a, b) with gcd(a, b) = 1 and 0 ≤ a ≤ b. -/
structure FareyFraction where
  num : ℕ
  denom : ℕ
  denom_pos : denom > 0
  num_le_denom : num ≤ denom
  coprime : Nat.Coprime num denom

-- ══════════════════════════════════════════════════════════════════
-- § 1b: Constructive Farey Pairs
-- ══════════════════════════════════════════════════════════════════

/-- Farey pairs of order n: coprime pairs (a, b) with 1 ≤ b ≤ n, 0 ≤ a ≤ b.
    This is the constructive representation of the Farey sequence F_n. -/
def fareyPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter fun p =>
    0 < p.2 ∧ p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2

@[simp]
theorem mem_fareyPairs {n a b : ℕ} :
    (a, b) ∈ fareyPairs n ↔ b ≤ n ∧ 0 < b ∧ a ≤ b ∧ Nat.Coprime a b := by
  simp only [fareyPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨ha, hb⟩, hpos, hle, hcop⟩
    exact ⟨by omega, hpos, hle, hcop⟩
  · rintro ⟨hbn, hpos, hle, hcop⟩
    exact ⟨⟨by omega, by omega⟩, hpos, hle, hcop⟩

/-- (0, 1) is a Farey pair for n ≥ 1 (represents the fraction 0/1). -/
theorem zero_one_mem_fareyPairs {n : ℕ} (hn : 1 ≤ n) :
    (0, 1) ∈ fareyPairs n := by
  rw [mem_fareyPairs]
  exact ⟨hn, one_pos, zero_le 1, rfl⟩

/-- (1, 1) is a Farey pair for n ≥ 1 (represents the fraction 1/1). -/
theorem one_one_mem_fareyPairs {n : ℕ} (hn : 1 ≤ n) :
    (1, 1) ∈ fareyPairs n := by
  rw [mem_fareyPairs]
  exact ⟨hn, one_pos, le_refl 1, rfl⟩

/-- (1, b) is a Farey pair when b ≤ n (represents 1/b). -/
theorem one_b_mem_fareyPairs {n b : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    (1, b) ∈ fareyPairs n := by
  rw [mem_fareyPairs]
  exact ⟨hbn, hb, hb, Nat.coprime_one_left b⟩

/-- The Farey pairs set is nonempty for n ≥ 1. -/
theorem fareyPairs_nonempty {n : ℕ} (hn : 1 ≤ n) : (fareyPairs n).Nonempty :=
  ⟨(0, 1), zero_one_mem_fareyPairs hn⟩

/-- Farey pairs for n = 0 is empty (no positive denominators ≤ 0). -/
theorem fareyPairs_zero : fareyPairs 0 = ∅ := by
  ext ⟨a, b⟩
  simp [mem_fareyPairs]
  omega

/-- Monotonicity: fareyPairs n ⊆ fareyPairs (n + 1). -/
theorem fareyPairs_mono {n : ℕ} : fareyPairs n ⊆ fareyPairs (n + 1) := by
  intro ⟨a, b⟩ h
  rw [mem_fareyPairs] at h ⊢
  exact ⟨by omega, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The count of Farey pairs equals 1 + sum of Euler totients:
    |F_n| = 1 + Σ_{k=1}^{n} φ(k).
    The extra 1 accounts for 0/1 which is coprime but not counted by totient. -/
theorem fareyPairs_card (n : ℕ) :
    (fareyPairs n).card = 1 + ∑ k in Finset.Icc 1 n, Nat.totient k := by sorry

/-- The rational value of a Farey pair. -/
def pairRatVal (p : ℕ × ℕ) : ℚ := p.1 / p.2

-- ══════════════════════════════════════════════════════════════════
-- § 1c: Farey Sequence (FareyFraction-based, partially constructive)
-- ══════════════════════════════════════════════════════════════════

/-- The Farey sequence of order n: all Farey fractions with denominator ≤ n.
    TODO: Define constructively from fareyPairs once DecidableEq FareyFraction is added. -/
def fareySequence (n : ℕ) : Finset FareyFraction :=
  sorry

/-- The number of Farey fractions of order n. -/
def fareyCount (n : ℕ) : ℕ := (fareySequence n).card

/-- Farey count is asymptotically 3n²/π². -/
theorem farey_count_asymptotic (n : ℕ) :
    ∃ C : ℝ, |(fareyCount n : ℝ) - 3 * n^2 / Real.pi^2| ≤ C * n * Real.log n := by sorry

/-
## Similarly Ordered Fractions

Two fractions a/b and c/d are similarly ordered if (a-c)(b-d) ≥ 0.
This means: either both numerator and denominator increase together,
or both decrease together.
-/

/-- Two Farey fractions are similarly ordered if (a-c)(b-d) ≥ 0. -/
def similarlyOrdered (f g : FareyFraction) : Prop :=
  (f.num : ℤ) - g.num ≥ 0 ∧ (f.denom : ℤ) - g.denom ≥ 0 ∨
  (f.num : ℤ) - g.num ≤ 0 ∧ (f.denom : ℤ) - g.denom ≤ 0

/-- Similarly ordered is symmetric. -/
lemma similarlyOrdered_symm (f g : FareyFraction) :
    similarlyOrdered f g ↔ similarlyOrdered g f := by
  simp only [similarlyOrdered]
  constructor <;> intro h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; constructor <;> linarith
  · left; constructor <;> linarith
  · right; constructor <;> linarith
  · left; constructor <;> linarith

/-- Similarly ordered is reflexive. -/
lemma similarlyOrdered_refl (f : FareyFraction) : similarlyOrdered f f := by
  left
  constructor <;> linarith

/-- Product form: similarly ordered iff (a-c)(b-d) ≥ 0. -/
theorem similarlyOrdered_iff_product (f g : FareyFraction) :
    similarlyOrdered f g ↔
    ((f.num : ℤ) - g.num) * ((f.denom : ℤ) - g.denom) ≥ 0 := by
  simp only [similarlyOrdered, ge_iff_le]
  exact mul_nonneg_iff.symm

/-- Similarly ordered on pairs: (a-c)(b-d) ≥ 0. -/
def pairSimilarlyOrdered (p q : ℕ × ℕ) : Prop :=
  ((p.1 : ℤ) - q.1) * ((p.2 : ℤ) - q.2) ≥ 0

instance (p q : ℕ × ℕ) : Decidable (pairSimilarlyOrdered p q) :=
  inferInstanceAs (Decidable (_ ≥ 0))

-- ══════════════════════════════════════════════════════════════════
-- § 2b: Pair-Based Runs (constructive alternative)
-- ══════════════════════════════════════════════════════════════════

/-- Sort Farey pairs by rational value: a/b ≤ c/d iff a·d ≤ c·b. -/
private def fareyPairLE : ℕ × ℕ → ℕ × ℕ → Bool :=
  fun p q => decide (p.1 * q.2 ≤ q.1 * p.2)

/-- The sorted list of Farey pairs of order n (sorted by rational value). -/
def fareySortedPairs (n : ℕ) : List (ℕ × ℕ) :=
  (fareyPairs n).val.toList.mergeSort fareyPairLE

/-- A run of length k in a pair list is similarly ordered. -/
def isPairSimOrdered (pairs : List (ℕ × ℕ)) (i k : ℕ) : Prop :=
  ∀ j₁ j₂, i ≤ j₁ → j₁ < j₂ → j₂ ≤ i + k →
    ∀ p₁ p₂, pairs[j₁]? = some p₁ → pairs[j₂]? = some p₂ →
    pairSimilarlyOrdered p₁ p₂

/-
## Consecutive Similarly Ordered Runs

A run of consecutive Farey fractions is similarly ordered if every
pair in the run satisfies the similarly ordered property.
-/

/-- The Farey sequence as a list (for indexing).
    See fareySortedPairs for the constructive pair-based version. -/
def fareyList (n : ℕ) : List FareyFraction :=
  sorry  -- Requires DecidableEq FareyFraction for full construction

/-- A run of length k starting at index i is similarly ordered. -/
def isSimOrdered (n : ℕ) (i k : ℕ) : Prop :=
  ∀ j₁ j₂, i ≤ j₁ → j₁ < j₂ → j₂ ≤ i + k →
    ∀ f₁ f₂, (fareyList n)[j₁]? = some f₁ →
             (fareyList n)[j₂]? = some f₂ →
             similarlyOrdered f₁ f₂

/-
## The Function f(n)

f(n) is the largest length of a consecutive similarly ordered run.
-/

/-- f(n) = max length of consecutive similarly ordered Farey fractions.
    This is the supremum over all i of the longest run starting at i. -/
noncomputable def mayerErdosF (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ i, isSimOrdered n i k }

/-
## Historical Results

The study of f(n) began with Mayer (1942) and Erdős (1943).
-/

/-- Mayer (1942): f(n) → ∞ as n → ∞. -/
theorem mayer_theorem : Filter.Tendsto mayerErdosF Filter.atTop Filter.atTop := by sorry

/-- Erdős (1943): f(n) grows at least linearly in n. -/
theorem erdos_1943_linear : ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (mayerErdosF n : ℝ) ≥ c * n := by sorry

/-
## Modern Bounds (van Doorn 2025)

van Doorn established the best known bounds for f(n).
-/

/-- van Doorn (2025): Lower bound f(n) ≥ (1/12 - o(1))n. -/
theorem vanDoorn_lower_bound :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, (mayerErdosF n : ℝ) ≥ (1/12 - ε) * n := by sorry

/-- van Doorn (2025): Upper bound f(n) ≤ n/4 + O(1). -/
theorem vanDoorn_upper_bound :
    ∃ C : ℝ, ∀ n : ℕ, (mayerErdosF n : ℝ) ≤ n / 4 + C := by sorry

/-- Combined: (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1). -/
theorem vanDoorn_bounds :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, (mayerErdosF n : ℝ) ≥ (1/12 - ε) * n) ∧
    (∃ C : ℝ, ∀ n : ℕ, (mayerErdosF n : ℝ) ≤ n / 4 + C) :=
  ⟨vanDoorn_lower_bound, vanDoorn_upper_bound⟩

/-
## The Main Conjecture (OPEN)

The central question is whether f(n) has a precise asymptotic.
-/

/-- OPEN: Does there exist c > 0 with f(n) = (c + o(1))n? -/
def hasAsymptoticConstant : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N,
    |(mayerErdosF n : ℝ) / n - c| < ε

/-- van Doorn's conjecture: c = 1/4 is optimal. -/
def vanDoornConjecture : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |(mayerErdosF n : ℝ) / n - 1/4| < ε

/-- The main question: Does f(n) have an asymptotic constant? -/
def erdos_1005_question : Prop := hasAsymptoticConstant

-- The problem is OPEN - we cannot prove or disprove this
-- axiom erdos_1005_holds : erdos_1005_question

/-
## Mediant Property of Farey Fractions

Farey fractions have special properties that constrain similar ordering.
-/

/-- The mediant of two fractions a/b and c/d is (a+c)/(b+d). -/
def mediant (f g : FareyFraction) : ℚ :=
  (f.num + g.num) / (f.denom + g.denom)

/-- Adjacent Farey fractions satisfy |ad - bc| = 1. -/
theorem farey_adjacent_property (n : ℕ) (i : ℕ) :
    ∀ (f g : FareyFraction), (fareyList n)[i]? = some f →
         (fareyList n)[i + 1]? = some g →
         (f.num : ℤ) * g.denom - f.denom * g.num = 1 ∨
         (f.num : ℤ) * g.denom - f.denom * g.num = -1 := by sorry

/-
## Geometric Interpretation

Similarly ordered fractions correspond to points in the Stern-Brocot
tree that lie on monotone paths.
-/

/-- A fraction corresponds to a point (a, b) in ℤ². -/
def toPoint (f : FareyFraction) : ℤ × ℤ := (f.num, f.denom)

/-- Similarly ordered = monotone in both coordinates. -/
theorem similarlyOrdered_iff_monotone (f g : FareyFraction) :
    similarlyOrdered f g ↔
    (toPoint f).1 ≤ (toPoint g).1 ∧ (toPoint f).2 ≤ (toPoint g).2 ∨
    (toPoint f).1 ≥ (toPoint g).1 ∧ (toPoint f).2 ≥ (toPoint g).2 := by
  simp only [similarlyOrdered, toPoint]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; exact ⟨Int.le_of_sub_nonneg h1, Int.le_of_sub_nonneg h2⟩
    · left
      constructor
      · have : (g.num : ℤ) - f.num ≥ 0 := by linarith
        exact Int.le_of_sub_nonneg this
      · have : (g.denom : ℤ) - f.denom ≥ 0 := by linarith
        exact Int.le_of_sub_nonneg this
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; constructor <;> omega
    · left; constructor <;> omega

/-
## Why the Gap Between 1/12 and 1/4?

The gap between lower and upper bounds suggests complex structure
in how Farey fractions are ordered.
-/

/-- The ratio of bounds is 3:1. -/
theorem bounds_ratio : (1 : ℝ) / 4 / (1 / 12) = 3 := by
  field_simp
  ring

/-- Closing the gap requires understanding local structure of Farey sequence. -/
theorem gap_significance :
    (1 : ℝ) / 4 - 1 / 12 = 1 / 6 := by
  field_simp
  ring

/-
## Summary

This file formalizes Erdős Problem #1005 on similarly ordered Farey fractions.

**Status**: OPEN

**The Question**: For Farey fractions of order n, let f(n) be the longest
run of consecutive similarly ordered fractions. Is there c > 0 with
f(n) = (c + o(1))n?

**Known Results**:
- Mayer (1942): f(n) → ∞
- Erdős (1943): f(n) ≫ n (linear growth)
- van Doorn (2025): (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1)

**Conjecture**: c = 1/4 (van Doorn)

**Open Problems**:
- Determine the exact asymptotic constant c
- Close the gap between 1/12 and 1/4
- Understand the structure of maximal similarly ordered runs
-/

end Erdos1005
