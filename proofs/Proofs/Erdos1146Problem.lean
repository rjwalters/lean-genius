/-
  Erdős Problem #1146: Is {2^m · 3^n} an Essential Component?

  Source: https://erdosproblems.com/1146
  Status: OPEN

  Statement:
  A set A ⊂ ℕ is called an *essential component* if d_s(A + B) > d_s(B)
  for every B ⊂ ℕ with 0 < d_s(B) < 1, where d_s denotes Schnirelmann density.

  **Question**: Is B = {2^m · 3^n : m, n ≥ 0} an essential component?

  Context:
  Ruzsa (1987) proved that essential components must satisfy
  |A ∩ {1,...,N}| ≥ (log N)^{1+c} for some c > 0, ruling out lacunary sets.
  The set {2^m · 3^n} has counting function ~ C · (log N)², which is
  exactly at the threshold (c = 1). Ruzsa (1999) specifically asked
  whether this set is essential.

  This problem is closely related to Erdős #37, which asks whether lacunary
  sets can be essential components (answer: NO). See Erdos37Problem.lean.

  References:
  - Ruzsa (1987, 1999) [Ru87], [Ru99]
  - [Va99, Problem 1.19]
-/

import Proofs.Erdos37Problem

open Set Finset BigOperators Filter Erdos37

namespace Erdos1146

/-
## Properties of 3-Smooth Numbers

The set {2^m · 3^n : m, n ≥ 0} consists of all positive integers whose
prime factors are at most 3. These are also called "regular numbers" or
"3-smooth numbers".
-/

/-- 1 is a 3-smooth number (2^0 · 3^0 = 1). -/
theorem one_mem_smooth23 : 1 ∈ smoothNumbers23 :=
  ⟨0, 0, by simp⟩

/-- 2 is a 3-smooth number (2^1 · 3^0 = 2). -/
theorem two_mem_smooth23 : 2 ∈ smoothNumbers23 :=
  ⟨1, 0, by simp⟩

/-- 3 is a 3-smooth number (2^0 · 3^1 = 3). -/
theorem three_mem_smooth23 : 3 ∈ smoothNumbers23 :=
  ⟨0, 1, by simp⟩

/-- 6 is a 3-smooth number (2^1 · 3^1 = 6). -/
theorem six_mem_smooth23 : 6 ∈ smoothNumbers23 :=
  ⟨1, 1, by norm_num⟩

/-- If n is 3-smooth, then 2n is 3-smooth. -/
theorem mul_two_mem_smooth23 {n : ℕ} (hn : n ∈ smoothNumbers23) :
    2 * n ∈ smoothNumbers23 := by
  obtain ⟨m, k, rfl⟩ := hn
  exact ⟨m + 1, k, by ring⟩

/-- If n is 3-smooth, then 3n is 3-smooth. -/
theorem mul_three_mem_smooth23 {n : ℕ} (hn : n ∈ smoothNumbers23) :
    3 * n ∈ smoothNumbers23 := by
  obtain ⟨m, k, rfl⟩ := hn
  exact ⟨m, k + 1, by ring⟩

/-- The product of two 3-smooth numbers is 3-smooth. -/
theorem mul_mem_smooth23 {a b : ℕ} (ha : a ∈ smoothNumbers23)
    (hb : b ∈ smoothNumbers23) : a * b ∈ smoothNumbers23 := by
  obtain ⟨m₁, k₁, rfl⟩ := ha
  obtain ⟨m₂, k₂, rfl⟩ := hb
  exact ⟨m₁ + m₂, k₁ + k₂, by ring⟩

/-- 3-smooth numbers are positive (nonzero). -/
theorem smooth23_pos {n : ℕ} (hn : n ∈ smoothNumbers23) : 0 < n := by
  obtain ⟨m, k, rfl⟩ := hn
  positivity

/-- 3-smooth numbers are unbounded: for every N, there exists a 3-smooth
    number greater than N. -/
theorem smooth23_unbounded : ∀ N : ℕ, ∃ n ∈ smoothNumbers23, N < n := by
  intro N
  refine ⟨2^(N + 1), ⟨N + 1, 0, by simp⟩, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N))

/-
## Non-Lacunary Property

The set {2^m · 3^n} is NOT lacunary. Lacunary sets have elements growing
exponentially with ratio r > 1, but consecutive 3-smooth numbers can have
ratios arbitrarily close to 1 (e.g., 2^a · 3^b and 2^(a+1) · 3^(b-1)
differ by factor 2/3).
-/

/-- The set {2^m · 3^n} is not lacunary.
    The ratios between consecutive smooth numbers approach 1: for instance,
    3^k and 2 · 3^(k-1) = 2 · 3^(k-1) have ratio 3/2, but higher
    powers give ratios like 2^a·3^b / 2^c·3^d arbitrarily close to 1
    (by the three-distance theorem / Beatty sequence theory). -/
axiom smooth23_not_lacunary : ¬ IsLacunarySet smoothNumbers23

/-
## Growth Rate

The counting function for {2^m · 3^n} grows as (log N)². More precisely,
|{2^m · 3^n : 2^m · 3^n ≤ N}| ~ (log N)² / (2 · log 2 · log 3).

This is exactly at Ruzsa's threshold: essential components need growth
≥ (log N)^{1+c} for some c > 0, and here c = 1.
-/

/-- The counting function growth ~ (log N)² is fast enough to satisfy
    Ruzsa's necessary condition for essential components with c = 1.
    This means the growth rate alone does NOT rule out essentiality.

    Proof sketch: From smooth23_counting, counting ~ C · (log N)².
    For any 0 < c < 1, (log N)^{1+c} = o((log N)²), so
    counting ≥ (log N)^{1+c} for large N. -/
theorem growth_satisfies_ruzsa_necessary :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
      (countingFunction smoothNumbers23 N : ℝ) ≥ (Real.log N)^(1 + c) := by
  use 1/2
  refine ⟨by norm_num, ?_⟩
  obtain ⟨C, hCpos, hcount⟩ := smooth23_counting
  -- Strategy: from |counting - C·(log N)²| ≤ log N, extract lower bound
  -- Then show C·(log N)² - log N ≥ (log N)^(3/2) for large N
  -- Combine the counting approximation with the algebraic bound
  have h_alg : ∀ᶠ (N : ℕ) in atTop,
      C * (Real.log (N : ℝ)) ^ 2 - Real.log (N : ℝ) ≥
        (Real.log (N : ℝ)) ^ ((1 : ℝ) + 1 / 2) := by
    -- For x = log N ≥ max(1, 4/C²), we have C·x² - x ≥ x^(3/2)
    -- Proof: C·√x ≥ 2, so C·x² = C·x^(3/2)·√x ≥ 2·x^(3/2),
    -- and x^(3/2) ≥ x for x ≥ 1, giving C·x² - x ≥ x^(3/2)
    filter_upwards [(Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max 1 (4 / C ^ 2)))] with N hN
    set x := Real.log (N : ℝ)
    have hx_ge1 : x ≥ 1 := le_trans (le_max_left _ _) hN
    have hx_pos : 0 < x := lt_of_lt_of_le one_pos hx_ge1
    have hx_ge4C2 : x ≥ 4 / C ^ 2 := le_trans (le_max_right _ _) hN
    -- Convert x^(1+1/2) to x · √x via rpow_add and sqrt_eq_rpow
    have h_eq : x ^ ((1 : ℝ) + 1 / 2) = x * Real.sqrt x := by
      rw [Real.rpow_add hx_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [h_eq]
    -- Now goal: C * x ^ 2 - x ≥ x * √x. Let s = √x, so x = s².
    set s := Real.sqrt x
    have hs_nn : 0 ≤ s := Real.sqrt_nonneg x
    have hsx : s ^ 2 = x := Real.sq_sqrt hx_pos.le
    have hs1 : s ≥ 1 := by
      have := Real.sqrt_le_sqrt hx_ge1; rwa [Real.sqrt_one] at this
    -- From x ≥ 4/C², derive C·√x ≥ 2 (by contradiction)
    have hCs : C * s ≥ 2 := by
      by_contra h_lt; push_neg at h_lt
      have h_nn := mul_nonneg hCpos.le hs_nn
      -- (C·s)² < 4 since 0 ≤ C·s < 2
      have h1 : (C * s) ^ 2 < 4 := by
        nlinarith [mul_nonneg h_nn (show (0 : ℝ) ≤ 2 - C * s by linarith)]
      -- (C·s)² = C²·x ≥ 4 since x ≥ 4/C²
      have h2 : (C * s) ^ 2 ≥ 4 := by
        have h_c2 := pow_pos hCpos 2
        calc (C * s) ^ 2 = C ^ 2 * s ^ 2 := by ring
          _ = C ^ 2 * x := by rw [hsx]
          _ ≥ C ^ 2 * (4 / C ^ 2) := mul_le_mul_of_nonneg_left hx_ge4C2 h_c2.le
          _ = 4 := by field_simp
      linarith
    -- Substitute x = s² and prove s³ ≤ C·s⁴ - s² by polynomial arithmetic
    -- Decompose as s²·(C·s−2)·s + s²·(s−1), both nonneg
    rw [show x = s ^ 2 from hsx.symm]
    nlinarith [mul_nonneg (sq_nonneg s) (mul_nonneg (show (0 : ℝ) ≤ C * s - 2 by linarith) hs_nn),
               mul_nonneg (sq_nonneg s) (show (0 : ℝ) ≤ s - 1 by linarith)]
  exact (hcount.and h_alg).mono fun N ⟨hcounting, halg⟩ => by
    have h_lower : (countingFunction smoothNumbers23 N : ℝ) ≥
        C * (Real.log (N : ℝ)) ^ 2 - Real.log (N : ℝ) := by
      linarith [neg_abs_le ((countingFunction smoothNumbers23 N : ℝ) -
        C * (Real.log (N : ℝ)) ^ 2)]
    linarith

/-
## Schnirelmann Density

The Schnirelmann density of {2^m · 3^n} is 0, since no positive integer
below 2 belongs to the set except 1 (and d_s considers the infimum over
all initial segments, including n = 4 where only {1,2,3,4} are smooth).

Actually d_s({2^m · 3^n}) = 0 because the density of smooth numbers in
initial segments approaches 0.
-/

/-- The Schnirelmann density of {2^m · 3^n} is 0.
    Since smooth numbers become increasingly sparse (gaps grow),
    the infimum of counting(N)/N over N ≥ 1 is 0. -/
axiom smooth23_schnirelmann_zero : schnirelmannDensity smoothNumbers23 = 0

/-
## Sumset Growth

A key approach to the essential component question is understanding how
the sumset {2^m · 3^n} + B behaves for sets B with positive Schnirelmann
density.

If B has d_s(B) > 0, then B contains a positive proportion of every
initial segment. Adding 3-smooth numbers to B creates new elements
because 3-smooth numbers are spread through many residue classes.
-/

/-- Mann's theorem applied: for any B, the sumset density is at least
    min(1, d_s(smoothNumbers23) + d_s(B)) = min(1, d_s(B)) = d_s(B).
    This gives only d_s(A + B) ≥ d_s(B), not strict inequality.
    The essential component question asks whether strict inequality holds. -/
theorem mann_lower_bound (B : Set ℕ) :
    schnirelmannDensity (smoothNumbers23 +ₛ B) ≥ schnirelmannDensity B := by
  have h := mann_theorem smoothNumbers23 B
  rw [smooth23_schnirelmann_zero, zero_add] at h
  have hB := (schnirelmannDensity_mem_Icc B).2
  rw [min_eq_right hB] at h
  exact h

/-
## The Main Open Question

Erdős Problem #1146 (= Ruzsa's Open Question from 1999):
Is {2^m · 3^n : m, n ≥ 0} an essential component?

Equivalently: for every B with 0 < d_s(B) < 1, is
d_s({2^m · 3^n} + B) > d_s(B)?
-/

/-- **Erdős Problem #1146** (OPEN):
    Is the set {2^m · 3^n : m, n ≥ 0} an essential component?

    This is equivalent to: for every B ⊂ ℕ with 0 < d_s(B) < 1,
    does adding 3-smooth numbers to B strictly increase the
    Schnirelmann density? -/
def Erdos1146Conjecture : Prop := IsEssentialComponent smoothNumbers23

/-- Equivalently stated using the definition from Erdős #37. -/
theorem erdos_1146_eq_ruzsa : Erdos1146Conjecture ↔ RuzsaOpenQuestion := by
  rfl

/-
## What Would Resolve This?

To PROVE essential: Show that for every B with 0 < d_s(B) < 1,
adding {2^m · 3^n} to B strictly increases density. This likely requires
understanding the additive structure of 3-smooth numbers in residue classes.

To DISPROVE essential: Exhibit a specific B with 0 < d_s(B) < 1 such that
d_s({2^m · 3^n} + B) = d_s(B).

Key difficulty: The (log N)² growth rate is right at Ruzsa's threshold,
so neither growth-based arguments nor sparsity arguments can resolve this.
New techniques are needed.
-/

/-
## Generalization: k-Smooth Numbers

For k primes p₁, ..., pₖ, the set {p₁^{a₁} · ... · pₖ^{aₖ}} has
counting function ~ C · (log N)^k. For k = 1 (powers of a single prime),
the set is lacunary and NOT essential. For k ≥ 2, the question is open.
-/

/-- The set of k-smooth numbers for a given set of primes. -/
def smoothNumbers (primes : Finset ℕ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ primes}

/-- For a single prime p, the set {p^n} is lacunary and hence not essential. -/
theorem single_prime_not_essential (p : ℕ) (hp : p.Prime) :
    ¬ IsEssentialComponent {n : ℕ | ∃ k : ℕ, n = p^k} := by
  have h_lac : IsLacunarySet {n : ℕ | ∃ k : ℕ, n = p^k} := by
    use fun k => p^k, p
    refine ⟨?_, ?_, ?_⟩
    · intro m n hmn
      exact Nat.pow_lt_pow_right hp.one_lt hmn
    · constructor
      · exact_mod_cast hp.one_lt
      · intro n; simp [pow_succ]; ring_nf; norm_cast
    · ext n; simp [Set.mem_range]
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
      · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  exact erdos_37_disproved _ h_lac

end Erdos1146
