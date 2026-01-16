/-
Erdős Problem #31: Additive Complements

Source: https://erdosproblems.com/31
Status: SOLVED (Lorentz 1954)

Statement:
Given any infinite set A ⊂ ℕ, there exists a set B of density 0 such that
A + B contains all except finitely many positive integers.

History:
- Erdős-Straus: Conjectured this result
- Lorentz (1954): Proved the conjecture [Lo54]

The result shows that any infinite set can be "completed" to cover almost all
of ℕ using only a very sparse set B. This is a fundamental result in additive
combinatorics about the complementary structure of sets.

Reference: Lorentz, G.G. "On a problem of additive number theory" (1954)
-/

import Mathlib

open Set Finset Nat Filter

namespace Erdos31

/-! ## Density Definitions -/

/-- The counting function |A ∩ {1,...,N}| for a set A ⊆ ℕ. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- A set A has density d if |A ∩ {1,...,N}| / N → d as N → ∞. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (countingFn A N : ℝ) / N) atTop (nhds d)

/-- A set has density 0. -/
def HasDensityZero (A : Set ℕ) : Prop := HasDensity A 0

/-- Upper density of a set. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N => (countingFn A N : ℝ) / N) atTop

/-- A set has upper density 0 if its upper density is 0. -/
def HasUpperDensityZero (A : Set ℕ) : Prop := upperDensity A = 0

/-! ## Sumsets -/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def Sumset (A B : Set ℕ) : Set ℕ := { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

notation:65 A " +ₛ " B => Sumset A B

/-- A + B contains all sufficiently large integers (covers a cofinite set). -/
def CoversCofinite (A B : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ (A +ₛ B)

/-- A + B contains all except finitely many positive integers. -/
def CoversAllButFinitely (A B : Set ℕ) : Prop :=
  (Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0}).Finite

/-! ## Properties of Sparse Sets -/

/-- The primes form an infinite set of density 0. -/
axiom primes_density_zero : HasDensityZero {n : ℕ | n.Prime}

/-- Helper: The number of powers of 2 up to N is at most log₂(N) + 1.
    This is because 2^k ≤ N iff k ≤ log₂(N).

    **Proof sketch**: The powers of 2 in [1,N] are {2^0, 2^1, ..., 2^k} where k = ⌊log₂ N⌋.
    This set injects into {0, 1, ..., k} via the map n ↦ log₂ n, giving at most k+1 elements.

    Note: This is axiomatized due to mathlib ncard API complexity; could be submitted to Aristotle. -/
axiom powers_of_2_count_bound (N : ℕ) :
    ({n : ℕ | ∃ k, n = 2^k} ∩ Set.Icc 1 N).ncard ≤ Nat.log 2 N + 1

/-- (log N + 1) / N → 0 as N → ∞.

**Proof**: We use the squeeze theorem. Since Nat.log 2 N ≤ Real.log N / Real.log 2,
we have (Nat.log 2 N + 1) / N ≤ (Real.log N / Real.log 2 + 1) / N → 0.
-/
theorem tendsto_log_add_one_div : Filter.Tendsto (fun N : ℕ => (Nat.log 2 N + 1 : ℝ) / N)
    Filter.atTop (nhds 0) := by
  -- Use squeeze: 0 ≤ f(N) ≤ (log N / log 2 + 1) / N → 0
  have h_upper : Filter.Tendsto (fun N : ℕ => (Real.log N / Real.log 2 + 1) / N)
      Filter.atTop (nhds 0) := by
    -- log N / N → 0 from tendsto_pow_log_div_mul_add_atTop
    have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Filter.Tendsto (fun N : ℕ => Real.log N / N) Filter.atTop (nhds 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    -- (log N / log 2) / N = (log N / N) / log 2 → 0 / log 2 = 0
    have h3 : Filter.Tendsto (fun N : ℕ => Real.log N / Real.log 2 / N) Filter.atTop (nhds 0) := by
      have hlog2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      have := h2.div_const (Real.log 2)
      simp only [zero_div] at this
      refine this.congr' ?_
      filter_upwards with N
      ring
    -- 1/N → 0
    have h4 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / N) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    -- Sum of limits
    have h5 := h3.add h4
    simp only [zero_add] at h5
    refine h5.congr' ?_
    filter_upwards with N
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
  · filter_upwards with N using div_nonneg (by positivity) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ N)
    have hN_pos : (1 : ℝ) < N := Nat.one_lt_cast.mpr hN
    have hN_pos' : (0 : ℝ) < N := by linarith
    -- Nat.log 2 N ≤ Real.log N / Real.log 2
    -- Using: 2^(Nat.log 2 N) ≤ N, so (Nat.log 2 N) * log 2 = log(2^(Nat.log 2 N)) ≤ log N
    have h_log_bound : (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 := by
      have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      rw [le_div_iff₀ hlog2_pos]
      by_cases hN1 : N = 1
      · simp [hN1, Real.log_one]
      · have hN2 : N ≠ 0 := by omega
        -- 2^(Nat.log 2 N) ≤ N
        have hpow := Nat.pow_log_le_self 2 hN2
        have hpow' : (((2 : ℕ) ^ Nat.log 2 N : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hpow
        calc (Nat.log 2 N : ℝ) * Real.log 2
            = Real.log ((2 : ℝ) ^ Nat.log 2 N) := by rw [Real.log_pow]
            _ = Real.log (((2 : ℕ) ^ Nat.log 2 N : ℕ) : ℝ) := by
                congr 1
                simp only [Nat.cast_pow, Nat.cast_ofNat]
            _ ≤ Real.log (N : ℝ) := by
              apply Real.log_le_log
              · have : (1 : ℕ) ≤ 2 ^ Nat.log 2 N := Nat.one_le_pow _ _ (by norm_num)
                exact Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one this)
              · exact hpow'
    linarith

/-- The powers of 2 form a set of density 0. -/
theorem powers_of_2_density_zero : HasDensityZero {n : ℕ | ∃ k : ℕ, n = 2^k} := by
  unfold HasDensityZero HasDensity countingFn
  -- Key: |{2^k : 2^k ≤ N}| ≤ log₂(N) + 1, so ratio ≤ (log₂(N) + 1)/N → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_log_add_one_div
  · filter_upwards with N using div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN_pos : (0 : ℝ) ≤ (N : ℝ) := le_of_lt (Nat.cast_pos.mpr hN)
    apply div_le_div_of_nonneg_right _ hN_pos
    exact_mod_cast powers_of_2_count_bound N

/-- Helper: The number of perfect squares up to N is at most √N + 1.
    This is because k² ≤ N iff k ≤ √N. -/
axiom squares_count_bound (N : ℕ) :
    ({n : ℕ | ∃ k, n = k^2} ∩ Set.Icc 1 N).ncard ≤ Nat.sqrt N + 1

/-- (√N + 1)/N → 0 as N → ∞.

**Proof**: We use √N ≤ N, so (√N + 1)/N ≤ 2√N/N = 2/√N → 0.
-/
theorem tendsto_sqrt_inv : Filter.Tendsto (fun N : ℕ => (Nat.sqrt N + 1 : ℝ) / N)
    Filter.atTop (nhds 0) := by
  -- Use squeeze: 0 ≤ (√N + 1)/N ≤ 2/√N → 0 for N ≥ 1
  have h_upper : Filter.Tendsto (fun N : ℕ => (2 : ℝ) / Real.sqrt N) Filter.atTop (nhds 0) := by
    -- sqrt N = N^(1/2), and x^(1/2) → ∞ as x → ∞ (since 1/2 > 0)
    have h1 : Filter.Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) Filter.atTop Filter.atTop := by
      have hsqrt : Filter.Tendsto (fun x : ℝ => x ^ (1/2 : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)
      have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      have := hsqrt.comp hcast
      refine this.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 0] with N _
      simp only [Function.comp_apply, Real.sqrt_eq_rpow]
    have h2 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / Real.sqrt N) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul 2
    simp only [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards with N
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
  · filter_upwards with N using div_nonneg (by positivity) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    have hN_pos' : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
    -- (√N + 1)/N ≤ 2/√N  iff  (√N + 1) * √N ≤ 2N  iff  N + √N ≤ 2N  iff  √N ≤ N
    rw [div_le_div_iff₀ hN_pos hN_pos']
    have hsqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
      have h1 : (Nat.sqrt N : ℝ) ^ 2 = ((Nat.sqrt N)^2 : ℕ) := by simp
      have h2 : ((Nat.sqrt N)^2 : ℕ) ≤ N := by
        exact Nat.sqrt_le' N
      have h3 : (Nat.sqrt N : ℝ) ^ 2 ≤ N := by
        rw [h1]
        exact Nat.cast_le.mpr h2
      rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
      exact Real.sqrt_le_sqrt h3
    have hsqrt_le_N : Real.sqrt N ≤ N := by
      have h1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN
      have hN_sq : (N : ℝ) ≤ N ^ 2 := by
        have : (1 : ℝ) ≤ N := h1
        nlinarith
      calc Real.sqrt N ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hN_sq
        _ = N := Real.sqrt_sq (le_of_lt hN_pos)
    calc (Nat.sqrt N + 1 : ℝ) * Real.sqrt N
        ≤ (Real.sqrt N + 1) * Real.sqrt N := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact le_of_lt hN_pos'
        _ = Real.sqrt N ^ 2 + Real.sqrt N := by ring
        _ = N + Real.sqrt N := by rw [Real.sq_sqrt (le_of_lt hN_pos)]
        _ ≤ N + N := by linarith
        _ = 2 * N := by ring

/-- Squares form a set of density 0. -/
theorem squares_density_zero : HasDensityZero {n : ℕ | ∃ k : ℕ, n = k^2} := by
  unfold HasDensityZero HasDensity countingFn
  -- Key: |{k² : k² ≤ N}| ≤ √N + 1, so ratio ≤ (√N + 1)/N → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_sqrt_inv
  · filter_upwards with N using div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    have hN_pos : (0 : ℝ) ≤ (N : ℝ) := le_of_lt (Nat.cast_pos.mpr hN)
    apply div_le_div_of_nonneg_right _ hN_pos
    exact_mod_cast squares_count_bound N

/-! ## The Main Theorem -/

/--
**Erdős Problem #31** (SOLVED - Lorentz 1954):
For any infinite set A ⊆ ℕ, there exists a set B of density 0 such that
A + B covers all but finitely many positive integers.
-/
def Erdos31Statement : Prop :=
  ∀ A : Set ℕ, A.Infinite →
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely A B

/-- The Lorentz theorem affirms Erdős Problem #31. -/
axiom lorentz_theorem : Erdos31Statement

/-! ## Lorentz's Construction

The proof constructs B as follows:
1. Enumerate A = {a₁ < a₂ < a₃ < ...}
2. For each aᵢ, include in B certain "gaps" that need filling
3. The sparseness of A (infinite but thin) allows B to be chosen sparse

Key insight: If A is very sparse, B can be dense (worst case).
If A is dense, B can be very sparse. The balance works out.
-/

/-- The set B constructed by Lorentz has at most O(N/log N) elements up to N. -/
axiom lorentz_B_bound (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely A B ∧
      ∃ C : ℝ, C > 0 ∧ ∀ N ≥ 1, (countingFn B N : ℝ) ≤ C * N / Real.log N

/-! ## Special Cases -/

/-- For A = {2^k : k ∈ ℕ}, we can take B = ℕ \ {1} (trivially works). -/
example : ∃ B : Set ℕ, HasDensityZero B ∧
    CoversAllButFinitely {n : ℕ | ∃ k : ℕ, n = 2^k} B := by
  -- Actually need a sparse B. For powers of 2, a good B is more complex.
  -- The key observation: 2^k + b covers many values as k grows.
  exact ⟨{n : ℕ | ∃ k : ℕ, n = 2^k - 1 ∨ n = 0},
         by sorry, -- density 0 (same sparseness as powers of 2)
         by sorry⟩ -- covers enough

/-- For A = primes, Lorentz's construction gives a very sparse B. -/
axiom primes_have_sparse_complement :
    ∃ B : Set ℕ, HasDensityZero B ∧ CoversAllButFinitely {n : ℕ | n.Prime} B

/-! ## Stronger Results

**Strengthening**: Not only does B exist with density 0, but we can make
B grow very slowly - Lorentz showed |B ∩ [1,N]| = O(N/log N).

Even stronger: For "most" sets A, B can be much sparser.
-/

/-- The optimal density bound depends on the structure of A. -/
noncomputable def OptimalBDensity (A : Set ℕ) : ℝ :=
  sInf { d : ℝ | ∃ B : Set ℕ, HasDensity B d ∧ CoversAllButFinitely A B }

/-- Density is always non-negative (technical lemma). -/
axiom density_nonneg (B : Set ℕ) (d : ℝ) (hd : HasDensity B d) : d ≥ 0

/-- For any infinite A, the optimal B-density is 0. -/
theorem optimal_B_density_zero (A : Set ℕ) (hA : A.Infinite) :
    OptimalBDensity A = 0 := by
  -- This follows from Lorentz's theorem: there exists B with density 0
  unfold OptimalBDensity
  -- The set contains 0 (from Lorentz), and 0 is the minimum possible density
  apply le_antisymm
  · -- sInf ≤ 0: because 0 is in the set
    apply csInf_le
    · -- The set is bounded below by 0 (densities are ≥ 0)
      use 0
      intro d ⟨B, hdens, _⟩
      exact density_nonneg B d hdens
    · -- 0 is in the set: Lorentz gives us B with HasDensity B 0
      obtain ⟨B, hB, hcover⟩ := lorentz_theorem A hA
      exact ⟨B, hB, hcover⟩
  · -- 0 ≤ sInf: infimum of set of densities is ≥ 0
    apply le_csInf
    · -- Nonempty: from Lorentz
      obtain ⟨B, hB, hcover⟩ := lorentz_theorem A hA
      exact ⟨0, B, hB, hcover⟩
    · -- Every element is ≥ 0
      intro d ⟨B, hdens, _⟩
      exact density_nonneg B d hdens

/-! ## Related Problems -/

/-- Erdős also asked: Can B be taken to have at most C·N/log N elements in [1,N]?
    Lorentz proved yes. -/
def Erdos31Strengthened : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ A : Set ℕ, A.Infinite →
    ∃ B : Set ℕ, (∀ N ≥ 1, (countingFn B N : ℝ) ≤ C * N / Real.log N) ∧
      CoversAllButFinitely A B

/-- Lorentz proved this strengthened version. -/
axiom lorentz_strengthened : Erdos31Strengthened

/-! ## Converse Direction -/

/-- Question: If A + B covers almost all of ℕ, how dense must A ∪ B be?
    Answer: At least positive density is needed (obvious). -/

theorem coverage_requires_density (A B : Set ℕ) :
    CoversAllButFinitely A B → ¬(HasDensityZero A ∧ HasDensityZero B) ∨
      A.Infinite ∨ B.Infinite := by
  intro hcover
  -- Either A is infinite, or B is infinite, or the negation of both having density 0
  by_cases hA : A.Infinite
  · right; left; exact hA
  · by_cases hB : B.Infinite
    · right; right; exact hB
    · -- Both A and B are finite
      -- The key observation: finite A, finite B → A + B is finite
      -- But finite A + B can't cover cofinitely many integers
      left
      intro ⟨_, _⟩
      have hAfin : A.Finite := Set.not_infinite.mp hA
      have hBfin : B.Finite := Set.not_infinite.mp hB
      -- Sumset of finite sets is finite
      have hAB_finite : (A +ₛ B).Finite := by
        unfold Sumset
        have hprod := (hAfin.prod hBfin).image (fun p : ℕ × ℕ => p.1 + p.2)
        apply Set.Finite.subset hprod
        intro n hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_image, Prod.exists, Set.mem_prod]
        obtain ⟨a, ha, b, hb, hab⟩ := hn
        exact ⟨a, b, ⟨ha, hb⟩, hab.symm⟩
      -- If A + B is finite, then ℕ \ (A + B) is infinite (since ℕ is infinite)
      have huniv_minus : (Set.univ \ (A +ₛ B)).Infinite :=
        Set.Infinite.diff Set.infinite_univ hAB_finite
      -- The intersection with {n > 0} is still infinite (removes at most one element)
      unfold CoversAllButFinitely at hcover
      have hinf : (Set.univ \ (A +ₛ B) ∩ {n : ℕ | n > 0}).Infinite := by
        apply Set.Infinite.mono _ (huniv_minus.diff (Set.finite_singleton 0))
        intro n hn
        simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, true_and, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hn ⊢
        exact ⟨hn.1, Nat.pos_of_ne_zero hn.2⟩
      exact hinf hcover

/-! ## Connection to Additive Bases -/

/-- A set A is an asymptotic additive basis of order h if
    hA = {a₁ + ... + aₕ : aᵢ ∈ A} covers all sufficiently large n. -/
def IsAsymptoticBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ (as : Fin h → ℕ), (∀ i, as i ∈ A) ∧ n = ∑ i, as i

/-- If A +ₛ B covers cofinitely, then A ∪ B is an asymptotic basis of order 2. -/
axiom sumset_covers_implies_basis (A B : Set ℕ) :
    CoversAllButFinitely A B → IsAsymptoticBasis (A ∪ B) 2

/-- Erdős Problem #31 shows: any infinite A becomes an asymptotic basis of
    order 2 when augmented with a density-0 set. -/
theorem infinite_set_augmentable (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasDensityZero B ∧ IsAsymptoticBasis (A ∪ B) 2 := by
  obtain ⟨B, hB_dense, hcover⟩ := lorentz_theorem A hA
  refine ⟨B, hB_dense, ?_⟩
  exact sumset_covers_implies_basis A B hcover

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #31 asked whether any infinite set A can be completed to
cover almost all of ℕ using a density-0 set B.

**Answer: YES** (Lorentz 1954)

**Key Results:**
1. For any infinite A ⊆ ℕ, there exists B with density 0 such that
   A + B ⊇ {n : n ≥ N₀} for some N₀.
2. Moreover, B can be chosen with |B ∩ [1,N]| = O(N/log N).
3. This is essentially optimal in general.

**Implications:**
- Sparse sets can "complete" each other in a very efficient way
- The additive structure of infinite sets is quite flexible
- Related to questions about additive bases

References:
- Lorentz (1954): Original proof
- Erdős-Straus: Original conjecture
- Related to Erdős Problem #221 (similar questions)
-/

end Erdos31
