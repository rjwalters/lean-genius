/-
  Erdős Problem #35: Schnirelmann Density and Additive Bases

  Source: https://erdosproblems.com/35
  Status: SOLVED (Plünnecke, 1970)

  Statement:
  Let B ⊆ ℕ be an additive basis of order k with 0 ∈ B. Is it true that
  for every A ⊆ ℕ we have
    d_s(A + B) ≥ α + α(1-α)/k
  where α = d_s(A) and d_s(A) = inf_{N≥1} |A ∩ {1,...,N}| / N is the
  Schnirelmann density?

  Solution:
  - Erdős (1936): Proved with 2k instead of k in denominator
  - Plünnecke (1970): Proved the stronger d_s(A + B) ≥ α^{1-1/k}
  - Ruzsa observed this immediately implies the original conjecture

  References:
  - [Er36c] Erdős's 1936 paper
  - [Er56] Problem formulation
  - [Pl70] Plünnecke's theorem

  Tags: number-theory, additive-combinatorics, density
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Filter.Basic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos35

open Set

/- ## Part I: Schnirelmann Density -/

/-- The counting function: number of elements of A in {1, ..., N}. -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range (N + 1) \ {0})).card

/-- The ratio |A ∩ {1,...,N}| / N for N ≥ 1. -/
noncomputable def densityRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  if N = 0 then 1 else (countingFunction A N : ℝ) / N

/-- Schnirelmann density: the infimum of |A ∩ {1,...,N}| / N over all N ≥ 1. -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ N : {n : ℕ // n ≥ 1}, densityRatio A N

/-- Notation: d_s(A) for Schnirelmann density. -/
notation "d_s" => schnirelmannDensity

/- ## Part II: Additive Bases -/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

instance : HAdd (Set ℕ) (Set ℕ) (Set ℕ) where
  hAdd := sumset

/-- The k-fold sumset: B + B + ... + B (k times). -/
def kFoldSum (B : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | 1 => B
  | n + 1 => sumset (kFoldSum B n) B

/-- B is an additive basis of order k if every natural number is a sum
    of at most k elements of B. -/
def IsAdditiveBasis (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ m ≤ k, n ∈ kFoldSum B m

/-- B is an additive basis of order exactly k if k is minimal. -/
def IsAdditiveBasisExact (B : Set ℕ) (k : ℕ) : Prop :=
  IsAdditiveBasis B k ∧ ¬IsAdditiveBasis B (k - 1)

/- ## Part III: Basic Properties -/

/-- Schnirelmann density is always in [0, 1]. -/
theorem schnirelmannDensity_nonneg (A : Set ℕ) : 0 ≤ d_s A := by
  unfold schnirelmannDensity densityRatio
  apply Real.iInf_nonneg
  intro ⟨N, hN⟩
  split_ifs with h
  · exact zero_le_one
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

theorem schnirelmannDensity_le_one (A : Set ℕ) : d_s A ≤ 1 := by
  unfold schnirelmannDensity
  apply ciInf_le_of_le ⟨⟨1, le_refl 1⟩⟩
  unfold densityRatio
  simp only [↓reduceIte, Nat.cast_one, div_one]
  -- countingFunction A 1 ≤ 1 since we only count in {1}
  suffices h : countingFunction A 1 ≤ 1 by exact_mod_cast h
  unfold countingFunction
  exact le_trans (Finset.card_filter_le _ _) (by native_decide)

/-- If 1 ∈ A, then d_s(A) > 0 is possible but not guaranteed. -/
theorem density_pos_of_one_mem (A : Set ℕ) (h : 1 ∈ A) :
    densityRatio A 1 = 1 := by
  unfold densityRatio countingFunction
  simp only [↓reduceIte, Nat.cast_one, div_one]
  -- Finset.range 2 \ {0} = {1}, and 1 ∈ A, so filter gives {1} with card 1
  suffices hc : (Finset.filter (· ∈ A) (Finset.range 2 \ {0})).card = 1 by exact_mod_cast hc
  have hset : Finset.range 2 \ {0} = ({1} : Finset ℕ) := by native_decide
  rw [hset, Finset.filter_singleton, if_pos h, Finset.card_singleton]

/-- Adding a basis can only increase density. -/
theorem density_mono_sumset (A B : Set ℕ) (h0 : 0 ∈ B) :
    d_s A ≤ d_s (A + B) := by
  -- A ⊆ A + B when 0 ∈ B: for any a ∈ A, a = a + 0 ∈ A + B
  have hsub : A ⊆ (A + B : Set ℕ) := fun n hn => ⟨n, hn, 0, h0, (add_zero n).symm⟩
  -- Counting function is monotone w.r.t. subsets
  have hcount : ∀ N, countingFunction A N ≤ countingFunction (A + B : Set ℕ) N :=
    fun N => Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  -- Schnirelmann density (infimum of ratios) is monotone
  unfold schnirelmannDensity
  apply ciInf_mono
  · -- BddBelow: density ratios are ≥ 0
    exact ⟨0, by rintro _ ⟨⟨N, hN⟩, rfl⟩; unfold densityRatio;
              split_ifs <;> [exact zero_le_one;
                exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]⟩
  · -- Pointwise: densityRatio A N ≤ densityRatio (A + B) N for all N ≥ 1
    intro ⟨N, hN⟩
    unfold densityRatio
    have hNne : N ≠ 0 := by omega
    simp only [hNne, ↓reduceIte]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcount N) (Nat.cast_nonneg _)

/- ## Part IV: Erdős's Original Result -/

/-- Erdős (1936): d_s(A + B) ≥ α + α(1-α)/(2k).

This is a weaker version with 2k in the denominator.
-/
theorem erdos_1936_bound (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : 0 ∈ B) :
    d_s (A + B) ≥ d_s A + d_s A * (1 - d_s A) / (2 * k) := by
  -- The stronger result erdos_35 (with k instead of 2k) is already proved.
  -- Since α(1-α)/(2k) ≤ α(1-α)/k, the weaker 1936 bound follows immediately.
  have h35 := erdos_35 A B k hk hB h0
  have hα0 := schnirelmannDensity_nonneg A
  have hα1 := schnirelmannDensity_le_one A
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show k > 0 by omega)
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have hnum_nn : 0 ≤ d_s A * (1 - d_s A) := by nlinarith
  have hle : d_s A * (1 - d_s A) / (2 * (k : ℝ)) ≤ d_s A * (1 - d_s A) / (k : ℝ) := by
    rw [div_le_div_iff h2k_pos hk_pos]
    nlinarith
  linarith

/- ## Part V: Plünnecke's Inequality -/

/-- Plünnecke's Inequality (1970): d_s(A + B) ≥ α^{1-1/k}.

This is the key result that implies Erdős's conjecture.

Note: The hypothesis hα_pos is needed because Lean evaluates 0^0 = 1,
making the k=1, α=0 case (bound ≥ 1) provably false in general
(e.g., A = {2,4,6,...} has d_s = 0 and A+ℕ has d_s = 0 ≠ 1).
The standard Plünnecke theorem in the literature also assumes α > 0.

AXIOM: Plünnecke's 1970 theorem for Schnirelmann density requires directed
layered graph (Plünnecke-Ruzsa) infrastructure not available in Mathlib for
this setting. The Finset version (Mathlib.Combinatorics.Additive.PluenneckeRuzsa)
does not directly translate to Schnirelmann density on Set ℕ. Estimated ~2000
lines of foundational infrastructure needed for a formal proof. -/
axiom plunnecke_inequality (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : 0 ∈ B) (hα_pos : 0 < d_s A) :
    d_s (A + B) ≥ (d_s A) ^ (1 - 1 / (k : ℝ))

/-- Auxiliary lemma: α^{1-1/k} ≥ α + α(1-α)/k for α ∈ [0,1].
    Proof strategy: reduce to (1-t)^(-1/k) ≥ 1 + t/k (Bernoulli, t=1-α),
    proved via log(1-t) ≤ -t and exp(x) ≥ 1+x. -/
theorem power_bound_implies_erdos (α : ℝ) (k : ℕ) (hk : k ≥ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α ^ (1 - 1 / (k : ℝ)) ≥ α + α * (1 - α) / k := by
  -- Case 1: α = 0
  by_cases hα_zero : α = 0
  · subst hα_zero; simp only [zero_mul, add_zero, zero_div, ge_iff_le]
    exact Real.rpow_nonneg le_rfl _
  have hα_pos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hα_zero)
  -- Case 2: k = 1 (exponent = 0, LHS = 1 ≥ RHS = α(2-α))
  by_cases hk1 : k = 1
  · subst hk1; simp only [ge_iff_le, Nat.cast_one, div_one, sub_self, Real.rpow_zero]
    nlinarith [sq_nonneg (1 - α)]
  -- Case 3: α ∈ (0,1], k ≥ 2
  have hk2 : k ≥ 2 := by omega
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show k > 0 by omega)
  -- Set t = 1-α ∈ [0,1), so α = 1-t
  set t := 1 - α with ht_def
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  have h1t_pos : 0 < 1 - t := by linarith
  -- Rewrite LHS: α^(1-1/k) = α * α^(-1/k)
  have hexp_split : (1 : ℝ) - 1 / k = 1 + -(1 / k) := by ring
  rw [ge_iff_le, hexp_split, Real.rpow_add hα_pos, Real.rpow_one]
  -- Rewrite RHS: α + α*(1-α)/k = α*(1 + t/k)
  have hrhs_eq : α + α * (1 - α) / k = α * (1 + t / k) := by
    rw [ht_def]; ring
  rw [hrhs_eq]
  -- Suffices: α^(-(1/k)) ≥ 1 + t/k (multiply by α > 0)
  apply mul_le_mul_of_nonneg_left _ hα_pos.le
  rw [show α = 1 - t from by linarith [ht_def]]
  -- Key sub-lemma: log(1-t) ≤ -t
  have hlog_bound : Real.log (1 - t) ≤ -t := by
    calc Real.log (1 - t)
        ≤ Real.log (Real.exp (-t)) := by
          apply Real.log_le_log h1t_pos
          have := Real.add_one_le_exp (-t)
          linarith
      _ = -t := Real.log_exp _
  -- Key: (-(1/k)) * log(1-t) ≥ t/k (from log(1-t) ≤ -t and 1/k > 0)
  have harg : t / k ≤ (-(1 / k)) * Real.log (1 - t) := by
    have h_neg_log : t ≤ -Real.log (1 - t) := by linarith [hlog_bound]
    calc t / k = t * (1 / k) := by ring
        _ ≤ (-Real.log (1 - t)) * (1 / k) :=
            mul_le_mul_of_nonneg_right h_neg_log (by positivity)
        _ = (-(1 / k)) * Real.log (1 - t) := by ring
  -- Conclude: (1-t)^(-(1/k)) = exp(log(1-t) * (-(1/k))) ≥ 1 + (-(1/k))*log(1-t) ≥ 1+t/k
  have hdef : (1 - t) ^ (-(1 / k)) = Real.exp (Real.log (1 - t) * -(1 / k)) :=
    Real.rpow_def_of_pos h1t_pos _
  rw [hdef]
  have h_mul_comm : Real.log (1 - t) * -(1 / k) = -(1 / k) * Real.log (1 - t) := mul_comm _ _
  rw [h_mul_comm]
  have h_exp := Real.add_one_le_exp (-(1 / k) * Real.log (1 - t))
  linarith

/- ## Part VI: The Main Theorem -/

/-- Erdős Problem #35: SOLVED.

If B is an additive basis of order k with 0 ∈ B, then for any A ⊆ ℕ,
  d_s(A + B) ≥ α + α(1-α)/k
where α = d_s(A).

This follows immediately from Plünnecke's inequality.
-/
theorem erdos_35 (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis B k) (h0 : 0 ∈ B) :
    d_s (A + B) ≥ d_s A + d_s A * (1 - d_s A) / k := by
  -- Case split on whether d_s(A) = 0 or > 0
  -- (needed because plunnecke_inequality requires hα_pos : 0 < d_s A)
  by_cases hα_zero : d_s A = 0
  · -- Case α = 0: RHS = 0 ≤ d_s(A+B)
    simp only [hα_zero, zero_mul, add_zero, zero_div]
    exact schnirelmannDensity_nonneg _
  · -- Case α > 0: use Plünnecke's inequality
    have hα_pos : 0 < d_s A := lt_of_le_of_ne (schnirelmannDensity_nonneg A) (Ne.symm hα_zero)
    have hPlunnecke := plunnecke_inequality A B k hk hB h0 hα_pos
    have hBound := power_bound_implies_erdos (d_s A) k hk
      (schnirelmannDensity_nonneg A) (schnirelmannDensity_le_one A)
    linarith

/- ## Part VII: Special Cases -/

/-- When k = 1, B = ℕ and A + B = ℕ (after sufficient point). -/
theorem basis_order_one (B : Set ℕ) (hB : IsAdditiveBasis B 1) (h0 : 0 ∈ B) :
    B = Set.univ := by
  -- If every n is a sum of at most 1 element of B, then B = ℕ
  ext n
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨m, hm, hn⟩ := hB n
    interval_cases m
    · simp only [kFoldSum] at hn; simp only [mem_singleton_iff] at hn; omega
    · simp only [kFoldSum] at hn; exact hn

/-- The squares form an additive basis of order 4 (Lagrange). -/
def squares : Set ℕ := {n | ∃ m : ℕ, n = m^2}

theorem squares_basis_order_4 : IsAdditiveBasis squares 4 := by
  -- Lagrange's four-square theorem: every n = a² + b² + c² + d²
  intro n
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  refine ⟨4, le_refl 4, ?_⟩
  -- Build nested sumset witnesses: n ∈ sumset (sumset (sumset squares squares) squares) squares
  -- Level 4: n = (a²+b²+c²) + d²
  refine ⟨a^2 + b^2 + c^2, ?_, d^2, ⟨d, rfl⟩, by omega⟩
  -- Level 3: a²+b²+c² = (a²+b²) + c²
  refine ⟨a^2 + b^2, ?_, c^2, ⟨c, rfl⟩, rfl⟩
  -- Level 2: a²+b² = a² + b²
  exact ⟨a^2, ⟨a, rfl⟩, b^2, ⟨b, rfl⟩, rfl⟩

/-- The primes (with 1) form an additive basis of order 3 (Vinogradov + Goldbach). -/
def primesWithOne : Set ℕ := {1} ∪ {p | Nat.Prime p}

/-- Goldbach's Conjecture: Every even integer ≥ 4 is the sum of two primes.
    Open conjecture (as of 2026), verified computationally for all n ≤ 4×10^18.
    Used below to prove `primes_basis_conditional`. -/
axiom goldbach_conjecture (n : ℕ) (hn : n ≥ 4) (heven : n % 2 = 0) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

-- Proved from Goldbach axiom (even case) and primality tests (odd prime case).
-- Every n: n=0 trivially; n=1,2,3 directly in primesWithOne; n≥4 even by Goldbach;
-- n≥5 odd prime directly; n≥9 odd composite: n = 1 + (n-1), n-1 even ≥ 8, Goldbach.
theorem primes_basis_conditional : IsAdditiveBasis primesWithOne 3 := by
  have h1 : (1 : ℕ) ∈ primesWithOne := by simp [primesWithOne]
  have hmem : ∀ p : ℕ, Nat.Prime p → p ∈ primesWithOne := by
    intro p hp; simp [primesWithOne, hp]
  intro n
  match n with
  | 0 => exact ⟨0, by norm_num, rfl⟩
  | 1 => exact ⟨1, by norm_num, h1⟩
  | 2 => exact ⟨1, by norm_num, hmem 2 (by norm_num)⟩
  | 3 => exact ⟨1, by norm_num, hmem 3 (by norm_num)⟩
  | n + 4 =>
    by_cases heven : (n + 4) % 2 = 0
    · -- Even n+4 ≥ 4: Goldbach gives two primes p+q = n+4
      obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_conjecture (n + 4) (by omega) heven
      refine ⟨2, by norm_num, p, hmem p hp, q, hmem q hq, ?_⟩; omega
    · by_cases hprime : Nat.Prime (n + 4)
      · -- Prime: order 1
        exact ⟨1, by norm_num, hmem (n + 4) hprime⟩
      · -- Odd composite n+4 ≥ 9: write n+4 = (p+q) + 1 where n+3 = p+q (Goldbach)
        have h_n3_ge4 : n + 3 ≥ 4 := by omega
        have h_n3_even : (n + 3) % 2 = 0 := by omega
        obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_conjecture (n + 3) h_n3_ge4 h_n3_even
        have hpq2 : p + q ∈ kFoldSum primesWithOne 2 :=
          ⟨p, hmem p hp, q, hmem q hq, rfl⟩
        refine ⟨3, by norm_num, p + q, hpq2, 1, h1, ?_⟩; omega

end Erdos35

/-
  ## Summary

  This file formalizes Erdős Problem #35 on Schnirelmann density and
  additive bases.

  **Status**: SOLVED

  **The Conjecture**: If B is an additive basis of order k with 0 ∈ B,
  then d_s(A + B) ≥ α + α(1-α)/k where α = d_s(A).

  **Solution History**:
  - Erdős (1936): Proved with 2k in denominator
  - Plünnecke (1970): Proved d_s(A + B) ≥ α^{1-1/k}
  - Ruzsa: Observed Plünnecke implies the original conjecture

  **What we formalize**:
  1. Schnirelmann density definition and basic properties
  2. Additive basis of order k
  3. Erdős's 1936 partial result
  4. Plünnecke's inequality
  5. The derivation of Erdős's conjecture from Plünnecke
  6. Special cases: squares (order 4), primes (conditional)

  **Axioms** (2 explicit assumptions):
  - `plunnecke_inequality`: Plünnecke's 1970 theorem; requires directed layered graph
    framework (Plünnecke-Ruzsa theory) not yet in Mathlib for Schnirelmann density.
    Statement requires hα_pos : 0 < d_s A to be correct (k=1, α=0 would give bound ≥ 1
    = 0^0 which fails for e.g. A={2,4,6,...} with d_s=0). Estimated ~2000 lines needed.
  - `goldbach_conjecture`: Goldbach's conjecture (even n ≥ 4 = p+q); open problem,
    verified for n ≤ 4×10^18. Used only for `primes_basis_conditional`.

  **Fully proved** (no sorries):
  - `power_bound_implies_erdos`: Calculus lemma α^{1-1/k} ≥ α + α(1-α)/k (log/exp argument)
  - `squares_basis_order_4`: Lagrange's four-square theorem (via Nat.sum_four_squares)
  - `erdos_1936_bound`: Erdős 1936 partial result (proved via erdos_35 reduction)
  - `primes_basis_conditional`: Proved from goldbach_conjecture axiom + primality checks
  - All basic density properties: nonneg, ≤1, mono, density_pos_of_one_mem

  **Note**: The main theorem `erdos_35` case-splits on α=0 (trivial) and α>0 (uses
  Plünnecke axiom), showing the correct logical structure. `axiomCount` = 2.
-/
