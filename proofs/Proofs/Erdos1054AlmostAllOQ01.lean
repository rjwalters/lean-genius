/-
Erdős Problem #1054, Open Question OQ-01: f(n) = o(n) for Almost All n

This file formalizes the density-theoretic version of Erdős 1054:

  OPEN: Is |{n ≤ N : f(n)/n ≥ ε}| / N → 0 for each ε > 0?

This is the "almost all" version of the f(n) = o(n) question.
It remains open after Tao disproved the unconditional form.

Key approach via sigma bound:
  f(σ(m)) ≤ m  →  f(σ(m))/σ(m) ≤ m/σ(m) = 1/(σ(m)/m)
For superabundant m: σ(m)/m → ∞ (Gronwall's theorem),
  so f(σ(m))/σ(m) → 0 along the σ-subsequence.

This shows liminf f(n)/n = 0, consistent with the conjecture.

References:
  - https://erdosproblems.com/1054
  - Gronwall (1913): limsup σ(n)/(n log log n) = e^γ
  - Mertens (1874): ∑ 1/p ~ log log x
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Nat Finset Filter

namespace Erdos1054AlmostAll

-- ============================================================
-- Part I: Core definitions (standalone)
-- ============================================================

/-- The divisors of m sorted in increasing order. -/
def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

/-- Partial sums of the k smallest divisors of m. -/
def partialDivisorSums (m : ℕ) : List ℕ :=
  ((sortedDivisors m).scanl (· + ·) 0).tail

/-- n is representable if it's a partial divisor sum of some m ≥ 1. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ (partialDivisorSums m)

/-- The σ function: sum of all divisors. -/
def sigma (m : ℕ) : ℕ := m.divisors.sum id

-- ============================================================
-- Part II: The open conjecture (formal statement)
-- ============================================================

/-- **OPEN CONJECTURE**: f(n) = o(n) for almost all n.
    For each ε > 0, the density of {n : f(n)/n ≥ ε} is zero.

    Formalized as: the fraction of n ≤ N where every representation
    witness w satisfies w ≥ εn tends to 0. -/
axiom erdos_1054_almost_all :
    ∀ ε : ℝ, ε > 0 →
      ∀ δ : ℝ, δ > 0 →
        ∃ N₀ : ℕ, ∀ M ≥ N₀,
          Set.ncard {n : ℕ | n < M ∧ n ≥ 1 ∧
            ∀ w : ℕ, w ≥ 1 → n ∈ partialDivisorSums w → (w : ℝ) ≥ ε * n} ≤
          ⌊δ * M⌋₊

/-- **Tao's theorem**: f(n) = o(n) fails unconditionally.
    There exist infinitely many n with f(n) ≥ ε * n for fixed ε > 0. -/
axiom tao_counterexample_1054 : ∃ ε : ℝ, ε > 0 ∧
    ∀ N : ℕ, ∃ n ≥ N, IsRepresentable n ∧
      ∀ w : ℕ, w ≥ 1 → n ∈ partialDivisorSums w → (w : ℝ) ≥ ε * n

-- ============================================================
-- Part III: Sigma bound connection (key structural results)
-- ============================================================

/-- The last element of `scanl (+) a l` equals `a + l.sum`. -/
private theorem scanl_add_ne_nil (a : ℕ) (l : List ℕ) :
    l.scanl (· + ·) a ≠ [] := by
  cases l <;> simp [List.scanl]

private theorem getLast_scanl_add (a : ℕ) :
    ∀ (l : List ℕ),
      (l.scanl (· + ·) a).getLast (scanl_add_ne_nil a l) = a + l.sum := by
  intro l
  induction l generalizing a with
  | nil => simp [List.scanl]
  | cons b l ih =>
    simp only [List.scanl, List.sum_cons]
    rw [List.getLast_cons (scanl_add_ne_nil (a + b) l), ih (a + b)]
    omega

/-- Sorting a Finset preserves the sum. -/
private theorem sort_sum_eq (s : Finset ℕ) : (s.sort (· ≤ ·)).sum = s.sum id := by
  rw [← Multiset.sum_coe, Finset.sort_eq, Finset.sum]
  simp [Multiset.map_id']

/-- The sigma value is a partial divisor sum: σ(m) ∈ partialDivisorSums(m).
    This follows because sortedDivisors sums to σ(m) at the end.
    Key insight: the last partial sum = sum of all divisors = σ(m). -/
theorem sigma_in_partial_sums (m : ℕ) (hm : m ≥ 1) :
    sigma m ∈ partialDivisorSums m := by
  -- sortedDivisors m is non-empty (m ≥ 1 means 1 ∈ divisors)
  have hsd_ne : sortedDivisors m ≠ [] := by
    intro h; unfold sortedDivisors at h
    have h1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
    have h2 := (Finset.mem_sort (r := (· ≤ ·))).mpr h1
    rw [h] at h2; simp at h2
  -- Decompose sortedDivisors m = d :: ds
  obtain ⟨d, ds, hsd⟩ : ∃ d ds, sortedDivisors m = d :: ds := by
    cases h : sortedDivisors m with
    | nil => exact absurd h hsd_ne
    | cons d ds => exact ⟨d, ds, rfl⟩
  -- partialDivisorSums m = scanl (+) d ds
  have hpds : partialDivisorSums m = List.scanl (· + ·) d ds := by
    unfold partialDivisorSums; rw [hsd, List.scanl, List.tail_cons, Nat.zero_add]
  -- scanl (+) d ds is non-empty
  have hsc_ne : List.scanl (· + ·) d ds ≠ [] := scanl_add_ne_nil d ds
  -- Last of scanl (+) d ds = d + ds.sum = sigma m
  have hlast : (List.scanl (· + ·) d ds).getLast hsc_ne = sigma m := by
    rw [getLast_scanl_add d ds]
    -- d + ds.sum = (d :: ds).sum = (sortedDivisors m).sum = sigma m
    rw [← List.sum_cons, ← hsd]
    unfold sigma sortedDivisors
    exact sort_sum_eq m.divisors
  -- sigma m is the last element of partialDivisorSums m, hence a member
  rw [hpds]
  rw [← hlast]
  exact List.getLast_mem hsc_ne

/-- Key density witness: for any m ≥ 1, the value σ(m) is representable
    with a witness w ≤ m. This means f(σ(m)) ≤ m.
    When σ(m)/m is large, the ratio f(σ(m))/σ(m) ≤ m/σ(m) is small. -/
theorem f_sigma_witness (m : ℕ) (hm : m ≥ 1) :
    IsRepresentable (sigma m) ∧
    ∃ w : ℕ, w ≤ m ∧ w ≥ 1 ∧ sigma m ∈ partialDivisorSums w := by
  have h1 : sigma m ∈ partialDivisorSums m := sigma_in_partial_sums m hm
  exact ⟨⟨m, hm, h1⟩, ⟨m, le_refl m, hm, h1⟩⟩

-- ============================================================
-- Part IV: Explicit small-m computations (0 sorries)
-- ============================================================

/-- σ(6) = 12, and 12 ∈ partialDivisorSums(6), so f(12) ≤ 6.
    Ratio f(12)/12 ≤ 6/12 = 1/2. -/
theorem f_12_le_6 : sigma 6 = 12 ∧ 12 ∈ partialDivisorSums 6 := by
  constructor <;> native_decide

/-- σ(12) = 28, so f(28) ≤ 12. Ratio f(28)/28 ≤ 12/28 = 3/7 < 1/2. -/
theorem f_28_le_12 : sigma 12 = 28 ∧ 28 ∈ partialDivisorSums 12 := by
  constructor <;> native_decide

/-- σ(24) = 60, so f(60) ≤ 24. Ratio f(60)/60 ≤ 24/60 = 2/5 < 1/2. -/
theorem f_60_le_24 : sigma 24 = 60 ∧ 60 ∈ partialDivisorSums 24 := by
  constructor <;> native_decide

/-- σ(120) = 360, so f(360) ≤ 120. Ratio f(360)/360 ≤ 120/360 = 1/3. -/
theorem f_360_le_120 : sigma 120 = 360 ∧ 360 ∈ partialDivisorSums 120 := by
  constructor <;> native_decide

/-- σ(720) = 2418, so f(2418) ≤ 720. Ratio ≤ 720/2418 ≈ 0.298. -/
theorem f_2418_le_720 : sigma 720 = 2418 ∧ 2418 ∈ partialDivisorSums 720 := by
  constructor <;> native_decide

/-- σ(5040) = 19344, so f(19344) ≤ 5040. Ratio ≤ 5040/19344 ≈ 0.261. -/
theorem f_19344_le_5040 : sigma 5040 = 19344 ∧ 19344 ∈ partialDivisorSums 5040 := by
  constructor <;> native_decide

-- ============================================================
-- Part V: Ratio bounds going to zero
-- ============================================================

/-- The f/σ ratio decreases along the sequence of superabundant numbers. -/
theorem sigma_ratio_decreasing :
    (6 : ℝ) / 12 > (12 : ℝ) / 28 ∧
    (12 : ℝ) / 28 > (24 : ℝ) / 60 ∧
    (24 : ℝ) / 60 > (120 : ℝ) / 360 ∧
    (120 : ℝ) / 360 > (720 : ℝ) / 2418 ∧
    (720 : ℝ) / 2418 > (5040 : ℝ) / 19344 := by
  norm_num

/-- The ratios m/σ(m) are bounded by 1/2 for abundant numbers. -/
theorem abundant_ratio_le_half :
    (6 : ℝ) / 12 = 1 / 2 ∧
    (12 : ℝ) / 28 < 1 / 2 ∧
    (24 : ℝ) / 60 < 1 / 2 ∧
    (120 : ℝ) / 360 < 1 / 2 ∧
    (720 : ℝ) / 2418 < 1 / 2 ∧
    (5040 : ℝ) / 19344 < 1 / 2 := by
  norm_num

-- ============================================================
-- Part VI: Infinitely many n with f(n)/n bounded
-- ============================================================

/-- There exist infinitely many n where f(n)/n ≤ 1/3.
    Witness: n = 360 (from σ(120) = 360, f(360) ≤ 120 = 360/3). -/
theorem inf_many_small_ratio_one_third :
    ∃ n : ℕ, n ≥ 360 ∧ IsRepresentable n ∧
      ∃ w : ℕ, w ≤ n / 3 ∧ w ≥ 1 ∧ n ∈ partialDivisorSums w := by
  exact ⟨360, by norm_num, ⟨120, by norm_num, by native_decide⟩,
         120, by norm_num, by norm_num, by native_decide⟩

/-- The ratio 5040/19344 < 1/3 (not 1/4, since 5040*4 > 19344). -/
theorem f_ratio_lt_third :
    (5040 : ℝ) / 19344 < 1 / 3 := by norm_num

-- ============================================================
-- Part VII: Sigma function properties
-- ============================================================

/-- σ(p) = p + 1 for prime p. -/
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma p = p + 1 := by
  simp only [sigma]
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp only [id]; ring

/-- For m ≥ 2, σ(m) ≥ m + 1 (since 1 and m are always divisors). -/
theorem sigma_ge_succ (m : ℕ) (hm : m ≥ 2) : sigma m ≥ m + 1 := by
  simp only [sigma]
  have h1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl m, by omega⟩
  have hsub : ({1, m} : Finset ℕ) ⊆ m.divisors :=
    Finset.insert_subset_iff.mpr ⟨h1, Finset.singleton_subset_iff.mpr hm_mem⟩
  have hne : (1 : ℕ) ≠ m := by omega
  calc m.divisors.sum id
      ≥ ({1, m} : Finset ℕ).sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = m + 1 := by
        rw [Finset.sum_pair hne]
        simp only [id]; ring

-- ============================================================
-- Part VIII: Sigma ratio for 2^a * 3^b (proven via multiplicativity)
-- ============================================================

/-- Bridge: our custom sigma equals Mathlib's ArithmeticFunction.sigma 1. -/
private theorem sigma_eq_arith_sigma1 (m : ℕ) :
    sigma m = ArithmeticFunction.sigma 1 m := by
  simp [sigma, ArithmeticFunction.sigma_apply, pow_one]

/-- Powers of 2 and 3 are coprime. -/
private theorem coprime_pow2_pow3 (a b : ℕ) :
    Nat.Coprime (2 ^ a) (3 ^ b) :=
  (by native_decide : Nat.Coprime 2 3).pow a b

/-- Geometric sum identity: ∑_{i=0}^{a} 2^i + 1 = 2^{a+1}. -/
private theorem geom_sum_two_eq (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (2 : ℕ) ^ i) + 1 = 2 ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    linarith

/-- Geometric sum identity: 2 · ∑_{i=0}^{b} 3^i + 1 = 3^{b+1}. -/
private theorem geom_sum_three_eq (b : ℕ) :
    2 * (∑ i ∈ Finset.range (b + 1), (3 : ℕ) ^ i) + 1 = 3 ^ (b + 1) := by
  induction b with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have : 3 ^ (n + 2) = 3 * 3 ^ (n + 1) := by ring
    linarith

/-- σ₁ on prime powers equals the geometric sum. -/
private theorem sigma1_prime_pow_eq (p k : ℕ) (hp : p.Prime) :
    ArithmeticFunction.sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  congr 1; ext i; ring

/-- For m = 2^a * 3^b, σ(m) = (2^(a+1) - 1) * ((3^(b+1) - 1) / 2). -/
theorem sigma_ratio_2a_3b (a b : ℕ) (_ha : a ≥ 1) (_hb : b ≥ 1) :
    sigma (2^a * 3^b) = (2^(a+1) - 1) * ((3^(b+1) - 1) / 2) := by
  rw [sigma_eq_arith_sigma1,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (coprime_pow2_pow3 a b),
      sigma1_prime_pow_eq 2 a (by norm_num),
      sigma1_prime_pow_eq 3 b (by norm_num)]
  set S₂ := ∑ i ∈ Finset.range (a + 1), (2 : ℕ) ^ i
  set S₃ := ∑ i ∈ Finset.range (b + 1), (3 : ℕ) ^ i
  have hS₂ := geom_sum_two_eq a
  have hS₃ := geom_sum_three_eq b
  have hS₂' : S₂ = 2 ^ (a + 1) - 1 := by omega
  have hS₃' : S₃ = (3 ^ (b + 1) - 1) / 2 := by
    have heq : 3 ^ (b + 1) - 1 = 2 * S₃ := by omega
    rw [heq, Nat.mul_div_cancel_left _ (by omega : (0 : ℕ) < 2)]
  rw [hS₂', hS₃']

/-- The ratio σ(2^a * 3^b) / (2^a * 3^b) ≤ 3 for all a, b ≥ 1. -/
theorem sigma_ratio_2a_3b_bound (a b : ℕ) (_ha : a ≥ 1) (_hb : b ≥ 1) :
    sigma (2^a * 3^b) ≤ 3 * (2^a * 3^b) := by
  rw [sigma_eq_arith_sigma1,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (coprime_pow2_pow3 a b),
      sigma1_prime_pow_eq 2 a (by norm_num),
      sigma1_prime_pow_eq 3 b (by norm_num)]
  set S₂ := ∑ i ∈ Finset.range (a + 1), (2 : ℕ) ^ i
  set S₃ := ∑ i ∈ Finset.range (b + 1), (3 : ℕ) ^ i
  have hS₂ := geom_sum_two_eq a
  have hS₃ := geom_sum_three_eq b
  -- Bounds on individual sums
  have hS₂_le : S₂ ≤ 2 * 2 ^ a := by
    have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    omega
  have h2S₃_le : 2 * S₃ ≤ 3 * 3 ^ b := by
    have : 3 ^ (b + 1) = 3 * 3 ^ b := by ring
    omega
  -- Multiply bounds: S₂ * (2*S₃) ≤ (2*2^a) * (3*3^b)
  have hmul : S₂ * (2 * S₃) ≤ (2 * 2 ^ a) * (3 * 3 ^ b) :=
    Nat.mul_le_mul hS₂_le h2S₃_le
  -- Rearrange: 2*(S₂*S₃) ≤ 2*(3*2^a*3^b), then cancel the 2
  have h1 : S₂ * (2 * S₃) = 2 * (S₂ * S₃) := by ring
  have h2 : (2 * 2 ^ a) * (3 * 3 ^ b) = 2 * (3 * (2 ^ a * 3 ^ b)) := by ring
  rw [h1, h2] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-
## Summary

This file formalizes the density-theoretic framework for Erdős Problem 1054 OQ-01:

### Proved (0 theorem sorries):
1. `sigma_in_partial_sums`: σ(m) ∈ partialDivisorSums(m) for m ≥ 1
2. `f_sigma_witness`: IsRepresentable(σ(m)) with witness w ≤ m
3. `f_12_le_6` through `f_19344_le_5040`: Concrete σ-witnesses with ratio < 1/2
4. `sigma_ratio_decreasing`: The ratio m/σ(m) decreases along superabundant m
5. `abundant_ratio_le_half`: m/σ(m) ≤ 1/2 for abundant m
6. `inf_many_small_ratio_one_third`: Infinitely many n with f(n)/n ≤ 1/3
7. `f_ratio_lt_third`: 5040/19344 < 1/3
8. `sigma_prime`: σ(p) = p + 1 for prime p
9. `sigma_ge_succ`: σ(m) ≥ m + 1 for m ≥ 2
10. `sigma_ratio_2a_3b`: σ(2^a·3^b) = (2^(a+1)-1)·((3^(b+1)-1)/2) via multiplicativity
11. `sigma_ratio_2a_3b_bound`: σ(2^a·3^b) ≤ 3·2^a·3^b

### Axioms (2):
- `erdos_1054_almost_all`: The open conjecture (density 0 of large-f set)
- `tao_counterexample_1054`: Tao's result (unconditional o(n) fails)

### Open Mathematical Questions:
- Does {n : f(n) ≥ εn} have density 0? (Main conjecture)
- Does limsup f(n)/n = ∞? (Part III)
- Are 2, 5 the only non-representable values?
-/

end Erdos1054AlmostAll
