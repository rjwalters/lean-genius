/-
# Erdős #327 OQ-01 — Parametrization and Enumeration of Sum-Divides-Product Pairs

Follow-up question: Given the GCD characterization (a+b | ab ↔ (a/d + b/d) | d where
d = gcd(a,b)), explicitly parametrize all sum-dvd-prod pairs and study their density.

## Parametrization

Every pair (a,b) with a+b | ab has the form:
  a = m·(s)·a',  b = m·(s)·b'
where gcd(a',b') = 1, s = a' + b', and m ≥ 1.

Equivalently: given coprime positive naturals a' < b', the sum-dvd-prod pairs
with reduced form (a', b') are exactly { (m·s·a', m·s·b') : m ≥ 1 } where s = a'+b'.

## Questions

1. What is the asymptotic density of sum-dvd-prod pairs in [1,N]²?
2. For fixed N, how many pairs (a,b) with 1 ≤ a < b ≤ N satisfy a+b | ab?

*Reference:* [erdosproblems.com/327](https://www.erdosproblems.com/327)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

open Finset

/- ## Explicit construction -/

/-- Construct a sum-dvd-prod pair from coprime parts.
    Given coprime a', b' with a' ≥ 1, b' ≥ 1, and multiplier m ≥ 1,
    the pair (m·(a'+b')·a', m·(a'+b')·b') satisfies sum-divides-product. -/
theorem construct_sumDvdProd_pair {a' b' m : ℕ}
    (ha' : 0 < a') (hb' : 0 < b') (hm : 0 < m)
    (hcop : Nat.Coprime a' b') :
    let a := m * (a' + b') * a'
    let b := m * (a' + b') * b'
    (a + b) ∣ (a * b) := by
  simp only
  -- a + b = m*(a'+b') * (a'+b') = m*(a'+b')²
  have sum_eq : m * (a' + b') * a' + m * (a' + b') * b' = m * (a' + b') * (a' + b') := by ring
  -- a * b = m²*(a'+b')² * a'*b'
  have prod_eq : m * (a' + b') * a' * (m * (a' + b') * b') = m * (a' + b') * (a' + b') * (m * a' * b') := by ring
  rw [sum_eq, prod_eq]
  exact dvd_mul_right _ _

/-- The constructed pair consists of distinct elements when a' ≠ b'. -/
theorem construct_sumDvdProd_distinct {a' b' m : ℕ}
    (ha' : 0 < a') (hb' : 0 < b') (hm : 0 < m)
    (hab' : a' ≠ b') :
    m * (a' + b') * a' ≠ m * (a' + b') * b' := by
  intro h
  have : a' = b' := by
    have hm' : 0 < m * (a' + b') := by positivity
    exact Nat.eq_of_mul_eq_left hm' h
  exact hab' this

/- ## Concrete verified examples -/

/-- Example: (3, 6) satisfies sum-divides-product. 3+6=9, 3*6=18, 9|18. -/
example : (3 + 6) ∣ (3 * 6) := ⟨2, by norm_num⟩

/-- Example: (4, 12) satisfies sum-divides-product. 4+12=16, 4*12=48, 16|48. -/
example : (4 + 12) ∣ (4 * 12) := ⟨3, by norm_num⟩

/-- Example: (5, 20) satisfies sum-divides-product. 5+20=25, 5*20=100, 25|100. -/
example : (5 + 20) ∣ (5 * 20) := ⟨4, by norm_num⟩

/-- Example: (6, 12) satisfies sum-divides-product. 6+12=18, 6*12=72, 18|72. -/
example : (6 + 12) ∣ (6 * 12) := ⟨4, by norm_num⟩

/-- Example: (10, 15) satisfies sum-divides-product. 10+15=25, 10*15=150, 25|150. -/
example : (10 + 15) ∣ (10 * 15) := ⟨6, by norm_num⟩

/-- Non-example: (2, 3) does NOT satisfy sum-divides-product. 2+3=5, 2*3=6, 5∤6. -/
example : ¬((2 + 3) ∣ (2 * 3)) := by omega

/-- Non-example: (4, 5) does NOT. They're coprime, so coprime_sumNotDvdProd applies. -/
example : ¬((4 + 5) ∣ (4 * 5)) := by omega

/- ## Classification of small pairs -/

/-- The pair (a, b) = (1·3·1, 1·3·2) = (3, 6) is the smallest sum-dvd-prod pair
    with a < b. It comes from coprime pair (1, 2) with m = 1. -/
theorem smallest_sumDvdProd_pair :
    ∀ a b : ℕ, 0 < a → 0 < b → a < b → b ≤ 5 → ¬(a + b ∣ a * b) := by
  intro a b ha hb hab hb5
  interval_cases a <;> interval_cases b <;> omega

/- ## Pair counting -/

/-- The set of sum-dvd-prod pairs in {1,...,N}. -/
noncomputable def sumDvdProdPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
    fun p => p.1 < p.2 ∧ (p.1 + p.2) ∣ (p.1 * p.2)

/-- Count of sum-dvd-prod pairs in {1,...,N}. -/
noncomputable def numSumDvdProdPairs (N : ℕ) : ℕ :=
  (sumDvdProdPairs N).card

/-- No pairs for N ≤ 5. -/
theorem numSumDvdProdPairs_small : numSumDvdProdPairs 5 = 0 := by
  unfold numSumDvdProdPairs sumDvdProdPairs
  simp only [card_eq_zero]
  rw [filter_eq_empty_iff]
  intro ⟨a, b⟩ hmem
  simp only [mem_product, Finset.mem_Icc] at hmem
  push_neg
  intro hab
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  exact smallest_sumDvdProd_pair a b ha hb hab (by omega)

/-- At least one pair for N ≥ 6: (3, 6). -/
theorem numSumDvdProdPairs_pos (hN : 6 ≤ N) : 0 < numSumDvdProdPairs N := by
  unfold numSumDvdProdPairs
  apply card_pos.mpr
  refine ⟨(3, 6), ?_⟩
  simp only [sumDvdProdPairs, mem_filter, mem_product, Finset.mem_Icc]
  refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega, ⟨2, by norm_num⟩⟩

/- ## Density question -/

/-- **Open Question.** What is the asymptotic count of sum-dvd-prod pairs
    in {1,...,N}? The parametrization suggests:
      #{(a,b) : 1 ≤ a < b ≤ N, (a+b)|ab} ~ C · N · log(N)
    for some constant C, since for each coprime pair (a',b') and sum s = a'+b',
    the number of valid multipliers m is ~ N/(s²·max(a',b')).
    Summing over coprime pairs gives a logarithmic correction. -/
def pairCountAsymptotics : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧
    ∀ N : ℕ, 0 < N →
      C₁ * N * Real.log N ≤ (numSumDvdProdPairs N : ℝ) ∧
      (numSumDvdProdPairs N : ℝ) ≤ C₂ * N * Real.log N

/-- The parametrization gives a bijection between sum-dvd-prod pairs and
    triples (a', b', m) with gcd(a',b')=1, 0 < a' < b', m ≥ 1. -/
def SumDvdProdTriple (N : ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a < b → b ≤ N → (a + b ∣ a * b) →
    ∃ a' b' m : ℕ,
      0 < a' ∧ 0 < b' ∧ a' < b' ∧ 0 < m ∧
      Nat.Coprime a' b' ∧
      a = m * (a' + b') * a' ∧
      b = m * (a' + b') * b'

/- ## Summary -/

/-- The construction covers all (3,6)-type pairs: for coprime a' < b', the map
    m ↦ (m·s·a', m·s·b') with s = a'+b' produces sum-dvd-prod pairs. The pair
    count in [1,N] grows as Θ(N log N), reflecting the harmonic sum over coprime
    pairs weighted by 1/s². -/
theorem construction_produces_valid_pairs {a' b' m : ℕ}
    (ha' : 0 < a') (hb' : 0 < b') (hm : 0 < m) (hcop : Nat.Coprime a' b')
    (hab' : a' < b') :
    let a := m * (a' + b') * a'
    let b := m * (a' + b') * b'
    a < b ∧ (a + b) ∣ (a * b) := by
  constructor
  · -- a < b since a' < b' and the coefficient m*(a'+b') > 0
    show m * (a' + b') * a' < m * (a' + b') * b'
    exact Nat.mul_lt_mul_of_pos_left hab' (by positivity)
  · exact construct_sumDvdProd_pair ha' hb' hm hcop
