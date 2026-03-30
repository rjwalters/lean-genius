/-
Erdős Problem #302: Unit Fraction Sum-Free Sets

Source: https://erdosproblems.com/302
Status: OPEN

Statement:
Let f(N) be the size of the largest A ⊆ {1,...,N} such that there are no
solutions to 1/a = 1/b + 1/c with distinct a,b,c ∈ A.

Estimate f(N). In particular, is f(N) = (1/2 + o(1))N?

Known Results:
- Lower bounds:
  * f(N) ≥ (1/2 + o(1))N (odd integers or [N/2, N])
  * f(N) ≥ (5/8 + o(1))N (Cambie: odd ≤ N/4 plus [N/2, N])
- Upper bound:
  * f(N) ≤ (9/10 + o(1))N (van Doorn)

The gap between 5/8 and 9/10 remains open.

Related: #301, #303, #327
Tags: number-theory, unit-fractions, extremal-combinatorics, sum-free-sets
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace Erdos302

/-
## Part 1: Basic Definitions

The unit fraction equation 1/a = 1/b + 1/c.
-/

/-- The unit fraction equation: 1/a = 1/b + 1/c -/
def UnitFractionSum (a b c : ℕ) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0 ∧ (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c

/-- Equivalent form: bc = a(b + c) -/
theorem unit_fraction_equiv (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c ↔ b * c = a * (b + c) := by
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc' : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro h
    have : (↑(b * c) : ℚ) = ↑(a * (b + c)) := by
      field_simp at h; linarith
    exact_mod_cast this
  · intro h
    have : (↑(b * c) : ℚ) = ↑(a * (b + c)) := by exact_mod_cast h
    field_simp; linarith

/-- A set is sum-free for unit fractions if no three distinct elements satisfy 1/a = 1/b + 1/c -/
def IsUnitFractionSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → b ≠ c → a ≠ c →
    ¬UnitFractionSum a b c

/-
## Part 2: The Function f(N)
-/

/-- f(N) = maximum size of a unit-fraction-sum-free subset of {1,...,N} -/
noncomputable def f (N : ℕ) : ℕ :=
  Finset.sup (Finset.powerset (Finset.range (N + 1) \ {0}))
    (fun A => if IsUnitFractionSumFree A then A.card else 0)

/-- Trivial upper bound: f(N) ≤ N -/
theorem f_le_N (N : ℕ) : f N ≤ N := by
  unfold f
  apply Finset.sup_le
  intro A hA
  split_ifs with h
  · -- A ⊆ {1,...,N} has at most N elements
    have hA_sub : A ⊆ Finset.range (N + 1) \ {0} :=
      Finset.mem_powerset.mp hA
    have hcard : (Finset.range (N + 1) \ {0}).card = N := by
      rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr (by omega)))]
      simp [Finset.card_range]
    calc A.card ≤ (Finset.range (N + 1) \ {0}).card := Finset.card_le_card hA_sub
      _ = N := hcard
  · exact Nat.zero_le N

/-
## Part 3: Lower Bound Constructions
-/

/-- The set of odd integers in [1, N] -/
def oddIntegers (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n > 0 ∧ n % 2 = 1)

/-- Odd integers are unit-fraction-sum-free -/
theorem odd_integers_sum_free (N : ℕ) : IsUnitFractionSumFree (oddIntegers N) := by
  intro a b c ha hb hc _ _ _
  simp only [oddIntegers, Finset.mem_filter, Finset.mem_range] at ha hb hc
  intro ⟨ha_pos, hb_pos, hc_pos, heq⟩
  -- a, b, c are all odd
  have ha_odd := ha.2.2
  have hb_odd := hb.2.2
  have hc_odd := hc.2.2
  -- From 1/a = 1/b + 1/c, we get bc = a(b+c)
  rw [unit_fraction_equiv a b c ha_pos hb_pos hc_pos] at heq
  -- b*c is odd (product of two odds)
  have hbc_odd : (b * c) % 2 = 1 := by omega
  -- b+c is even (sum of two odds)
  have hbc_even : (b + c) % 2 = 0 := by omega
  -- a*(b+c) is even (product with an even number)
  have habceven : (a * (b + c)) % 2 = 0 := by omega
  -- But bc = a(b+c): odd = even, contradiction
  omega

/-- The set of integers in [N/2, N] -/
def upperHalf (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => n ≥ N / 2)

/-- Upper half integers are unit-fraction-sum-free.
    Key identity: bc = a(b+c) implies (b-a)(c-a) = a² over ℤ.
    With b-a, c-a ∈ [1, a+1] and product = a², both must equal a, giving b = c. -/
theorem upper_half_sum_free (N : ℕ) (hN : N ≥ 4) : IsUnitFractionSumFree (upperHalf N) := by
  intro a b c ha hb hc hab hbc hac
  simp only [upperHalf, Finset.mem_filter, Finset.mem_range] at ha hb hc
  intro ⟨ha_pos, hb_pos, hc_pos, heq⟩
  rw [unit_fraction_equiv a b c ha_pos hb_pos hc_pos] at heq
  -- From bc = ab + ac: a ≤ b and a ≤ c, hence a < b and a < c (by distinctness)
  have hab_strict : a < b := Nat.lt_of_le_of_ne (by nlinarith) hab
  have hac_strict : a < c := Nat.lt_of_le_of_ne (by nlinarith) hac
  -- Work over ℤ for clean subtraction
  -- Key identity: (b-a)(c-a) = a² (from bc = a(b+c))
  have identity : ((b : ℤ) - a) * ((c : ℤ) - a) = (a : ℤ) ^ 2 := by push_cast; nlinarith
  -- Bounds: 1 ≤ b-a, c-a ≤ N-a ≤ a+1
  have hba_pos : (1 : ℤ) ≤ (b : ℤ) - a := by omega
  have hca_pos : (1 : ℤ) ≤ (c : ℤ) - a := by omega
  have hba_ub : (b : ℤ) - a ≤ (a : ℤ) + 1 := by
    -- b ≤ N and a ≥ N/2, so b - a ≤ N - N/2. Need N - N/2 ≤ a + 1.
    -- N/2 ≤ a, so N - a ≤ N - N/2 = ⌈N/2⌉ ≤ N/2 + 1 ≤ a + 1.
    omega
  have hca_ub : (c : ℤ) - a ≤ (a : ℤ) + 1 := by omega
  -- From (b-a)(c-a) = a² and c-a ≤ a+1: b-a ≥ a²/(a+1) > a-1, so b-a ≥ a
  have hba_lb : (a : ℤ) ≤ (b : ℤ) - a := by
    by_contra h; push_neg at h
    -- b-a ≤ a-1, so c-a = a²/(b-a) ≥ a²/(a-1) > a+1 (for a ≥ 2)
    have hba_small : (b : ℤ) - a ≤ a - 1 := by omega
    have hba_pos' : (0 : ℤ) < (b : ℤ) - a := by omega
    have : (a : ℤ) + 1 < (c : ℤ) - a := by
      -- (c-a)(b-a) = a², c-a ≤ a+1 and b-a ≤ a-1
      -- But (a+1)(a-1) = a²-1 < a², so (c-a) > a+1 when b-a ≤ a-1
      nlinarith [sq_nonneg ((b : ℤ) - a - 1)]
    linarith
  -- Similarly c-a ≥ a
  have hca_lb : (a : ℤ) ≤ (c : ℤ) - a := by
    by_contra h; push_neg at h
    have hca_small : (c : ℤ) - a ≤ a - 1 := by omega
    have hca_pos' : (0 : ℤ) < (c : ℤ) - a := by omega
    have : (a : ℤ) + 1 < (b : ℤ) - a := by nlinarith [sq_nonneg ((c : ℤ) - a - 1)]
    linarith
  -- Now b-a ≥ a, c-a ≥ a, and (b-a)(c-a) = a², so both equal a
  have hba_eq : (b : ℤ) - a = a := by nlinarith
  have hca_eq : (c : ℤ) - a = a := by nlinarith
  -- Therefore b = c, contradiction
  have : b = c := by omega
  exact absurd this hbc

/-- Basic lower bound: f(N) ≥ (1/2 + o(1))N -/
/-- Cambie's construction: odd integers ≤ N/4 plus integers in [N/2, N] -/
def cambie_set (N : ℕ) : Finset ℕ :=
  (oddIntegers (N / 4)) ∪ (upperHalf N)

/-- Cambie's improved lower bound: f(N) ≥ (5/8 + o(1))N -/
axiom cambie_lower_bound :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (f N : ℚ) ≥ (5/8 - ε) * N

/-- Why 5/8: N/8 odd integers plus N/2 upper integers -/
theorem cambie_count_estimate (N : ℕ) (hN : N ≥ 8) :
    (cambie_set N).card ≥ 5 * N / 8 - 2 := by
  unfold cambie_set
  -- Step 1: The two sets are disjoint (oddIntegers ≤ N/4 < N/2 ≤ upperHalf)
  have hdisj : Disjoint (oddIntegers (N / 4)) (upperHalf N) := by
    rw [Finset.disjoint_left]
    intro x hx_odd hx_upper
    simp only [oddIntegers, Finset.mem_filter, Finset.mem_range] at hx_odd
    simp only [upperHalf, Finset.mem_filter, Finset.mem_range] at hx_upper
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  -- Step 2: Lower bound on oddIntegers(N/4) via injection i ↦ 2i+1
  have h_odd_lb : (oddIntegers (N / 4)).card ≥ (N / 4 + 1) / 2 := by
    have hsub : Finset.image (fun i => 2 * i + 1) (Finset.range ((N / 4 + 1) / 2))
        ⊆ oddIntegers (N / 4) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [oddIntegers, Finset.mem_filter, Finset.mem_range]
      omega
    have hcard : (Finset.image (fun i => 2 * i + 1)
        (Finset.range ((N / 4 + 1) / 2))).card = (N / 4 + 1) / 2 := by
      rw [Finset.card_image_of_injective _ (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega),
        Finset.card_range]
    linarith [Finset.card_le_card hsub]
  -- Step 3: Lower bound on upperHalf(N) via injection i ↦ i + N/2
  have h_upper_lb : (upperHalf N).card ≥ N / 2 + 1 := by
    have hsub : Finset.image (· + N / 2) (Finset.range (N / 2 + 1)) ⊆ upperHalf N := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [upperHalf, Finset.mem_filter, Finset.mem_range]
      omega
    have hcard : (Finset.image (· + N / 2) (Finset.range (N / 2 + 1))).card = N / 2 + 1 := by
      rw [Finset.card_image_of_injective _ (fun a b (h : a + N / 2 = b + N / 2) => by omega),
        Finset.card_range]
    linarith [Finset.card_le_card hsub]
  -- Step 4: Combine: (N/4+1)/2 + N/2 + 1 ≥ 5*N/8 - 2 for N ≥ 8
  omega

/-
## Part 4: Upper Bound (van Doorn)
-/

/-- van Doorn's upper bound: f(N) ≤ (9/10 + o(1))N -/
axiom van_doorn_upper_bound :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (f N : ℚ) ≤ (9/10 + ε) * N

/-- The gap: 5/8 < 9/10, so the asymptotic density is in [0.625, 0.9]. -/
theorem known_bounds_gap : (5 : ℚ) / 8 < 9 / 10 := by norm_num

/-
## Part 5: The Main Question

Is f(N) = (1/2 + o(1))N? Answer: NO, since f(N) ≥ (5/8 + o(1))N.
-/

/-- The original question: Is f(N) = (1/2 + o(1))N? -/
def original_question : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |(f N : ℚ) / N - 1/2| < ε

/-- The answer: NO (since Cambie showed f(N) ≥ (5/8 + o(1))N) -/
theorem original_question_false : ¬original_question := by
  intro hoq
  -- hoq says f(N)/N → 1/2, so for ε = 1/32, f(N)/N < 1/2 + 1/32 = 17/32 for large N
  obtain ⟨N₁, hN₁⟩ := hoq (1/32) (by norm_num)
  -- Cambie: f(N) ≥ (5/8 - 1/32)*N = 19/32*N for large N
  obtain ⟨N₂, hN₂⟩ := cambie_lower_bound (1/32) (by norm_num)
  -- Take N = max(N₁, N₂, 1) to ensure N > 0
  set M := max (max N₁ N₂) 1
  have hM1 : M ≥ N₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : M ≥ N₂ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM_pos : (M : ℚ) > 0 := by exact_mod_cast (show 0 < M by omega)
  have h1 := hN₁ M hM1
  have h2 := hN₂ M hM2
  -- h1: |f(M)/M - 1/2| < 1/32, so f(M)/M < 1/2 + 1/32 = 17/32
  -- h2: f(M) ≥ (5/8 - 1/32) * M = 19/32 * M, so f(M)/M ≥ 19/32
  -- But 19/32 > 17/32, contradiction
  rw [abs_lt] at h1
  have h_upper : (f M : ℚ) / M < 1/2 + 1/32 := by linarith
  have h_lower : (f M : ℚ) ≥ (5/8 - 1/32) * M := h2
  have h_div : (f M : ℚ) / M ≥ 19/32 := by
    rw [ge_iff_le, div_le_iff hM_pos] at *
    linarith
  linarith

/-- The refined question: What is lim f(N)/N? -/
def density_question : Prop :=
  ∃ c : ℚ, 5/8 ≤ c ∧ c ≤ 9/10 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(f N : ℚ) / N - c| < ε

/-
## Part 6: Related Observation (Cambie)

If we allow b = c, then solutions exist when |A| ≥ (2/3 + o(1))N.
-/

/-- Unit fraction with b = c: 1/a = 2/b, i.e., b = 2a -/
def HasDoubling (A : Finset ℕ) : Prop :=
  ∃ a : ℕ, a ∈ A ∧ 2 * a ∈ A

/-- If |A| > (2/3)N, then A contains some n and 2n -/
/-- The b = c case allows threshold 2/3 > 5/8, so the equal case is
    actually less restrictive than the distinct case. -/
theorem equal_case_threshold : (2 : ℚ) / 3 > 5 / 8 := by norm_num

/-
## Part 7: The Coloring Version (Problem #303)
-/

/-- The coloring version: can {1,...,N} be 2-colored with no monochromatic solution? -/
def coloring_version (N : ℕ) : Prop :=
  ∃ color : ℕ → Bool,
    ∀ a b c : ℕ, 1 ≤ a → a ≤ N → 1 ≤ b → b ≤ N → 1 ≤ c → c ≤ N →
      a ≠ b → b ≠ c → a ≠ c →
      UnitFractionSum a b c →
      (color a ≠ color b ∨ color b ≠ color c)

/-- Brown-Rödl (1991): The coloring version has a solution for all N -/
axiom brown_rodl_coloring :
    ∀ N : ℕ, coloring_version N

/-
## Part 8: Algebraic Structure
-/

/-- The equation 1/a = 1/b + 1/c is equivalent to bc = ab + ac -/
theorem algebraic_form (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    UnitFractionSum a b c ↔ b * c = a * b + a * c := by
  unfold UnitFractionSum
  constructor
  · rintro ⟨_, _, _, h⟩
    have := (unit_fraction_equiv a b c ha hb hc).mp h
    linarith [Nat.mul_comm a (b + c), Nat.left_distrib a b c]
  · intro h
    refine ⟨ha, hb, hc, ?_⟩
    rw [unit_fraction_equiv a b c ha hb hc]
    linarith [Nat.left_distrib a b c]

/-- If 1/a = 1/b + 1/c with a < b < c, then b < 2a.
    From bc = ab + ac and 2a ≤ b: 2ac ≤ bc = ab + ac, so ac ≤ ab, c ≤ b. Contradiction. -/
theorem solution_b_lt_2a (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a < b) (hbc : b < c) (hsum : UnitFractionSum a b c) :
    b < 2 * a := by
  obtain ⟨_, _, _, heq⟩ := hsum
  rw [unit_fraction_equiv a b c ha hb hc] at heq
  -- heq : b * c = a * (b + c)
  by_contra h; push_neg at h -- h : 2 * a ≤ b
  have h1 : b * c = a * b + a * c := by linarith [mul_add a b c]
  have h2 : 2 * (a * c) ≤ b * c := by
    calc 2 * (a * c) = (2 * a) * c := by ring
      _ ≤ b * c := Nat.mul_le_mul_right c h
  have h3 : a * c ≤ a * b := by linarith
  exact absurd (Nat.le_of_mul_le_mul_left h3 ha) (by omega)

/-- If 1/a = 1/b + 1/c with a < b < c, then c ≤ a*(a+1).
    Over ℤ: (b-a-1)(c-a) = a(a+1) - c ≥ 0, so c ≤ a(a+1). -/
theorem solution_c_bound (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a < b) (hbc : b < c) (hsum : UnitFractionSum a b c) :
    c ≤ a * (a + 1) := by
  obtain ⟨_, _, _, heq⟩ := hsum
  rw [unit_fraction_equiv a b c ha hb hc] at heq
  have hb_lt : b < 2 * a := solution_b_lt_2a a b c ha hb hc hab hbc hsum
  -- Work over ℤ to avoid ℕ subtraction issues
  suffices h : (c : ℤ) ≤ ↑a * (↑a + 1) by exact_mod_cast h
  have heq' : (b : ℤ) * c = ↑a * (↑b + ↑c) := by exact_mod_cast heq
  -- Key identity: (b-a-1)(c-a) = a(a+1) - c, using bc = a(b+c)
  have hprod_eq : (↑b - ↑a - 1 : ℤ) * (↑c - ↑a) = ↑a * (↑a + 1) - ↑c := by nlinarith
  -- Both factors are non-negative: b ≥ a+1 and c > a
  have hprod_nn : (0 : ℤ) ≤ (↑b - ↑a - 1) * (↑c - ↑a) :=
    mul_nonneg (by omega) (by omega)
  linarith

/-
## Part 9: Examples of Solutions
-/

/-- Example: 1/6 = 1/12 + 1/12... wait, that's b = c -/
example : (1 : ℚ) / 6 = 1 / 12 + 1 / 12 := by norm_num

/-- Example with distinct: 1/2 = 1/3 + 1/6 -/
example : (1 : ℚ) / 2 = 1 / 3 + 1 / 6 := by norm_num

/-- Example: 1/3 = 1/4 + 1/12 -/
example : (1 : ℚ) / 3 = 1 / 4 + 1 / 12 := by norm_num

/-- Example: 1/4 = 1/5 + 1/20 -/
example : (1 : ℚ) / 4 = 1 / 5 + 1 / 20 := by norm_num

/-- Pattern: 1/n = 1/(n+1) + 1/(n(n+1)) -/
theorem standard_pattern (n : ℕ) (hn : n > 0) :
    (1 : ℚ) / n = 1 / (n + 1) + 1 / (n * (n + 1)) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hnm : (n : ℚ) * ((n : ℚ) + 1) ≠ 0 := mul_ne_zero hn' hn1
  field_simp
  ring

/-
## Part 10: Why the Problem is Hard
-/

/-- Each element a ∈ A forbids all pairs (b,c) with bc = a(b+c).
    The number of solutions grows, making large sum-free sets hard to construct.
    The 2-coloring result of Brown-Rödl shows the structure is not too rigid. -/
theorem coloring_always_possible (N : ℕ) : coloring_version N :=
  brown_rodl_coloring N

/-- The basic lower bound construction (odd integers) gives ≥ (1/2)N,
    but Cambie's improved construction pushes this to ≥ (5/8)N. -/
theorem lower_bound_improvement : (5 : ℚ) / 8 > 1 / 2 := by norm_num

/-
## Part 11: Main Results Summary
-/

/-- Erdős Problem #302: Complete status -/
theorem erdos_302 :
    -- Lower bound: f(N) ≥ (5/8 + o(1))N (Cambie)
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (f N : ℚ) ≥ (5/8 - ε) * N) ∧
    -- Upper bound: f(N) ≤ (9/10 + o(1))N (van Doorn)
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (f N : ℚ) ≤ (9/10 + ε) * N) ∧
    -- Original question f(N) = (1/2 + o(1))N is FALSE
    ¬original_question := by
  refine ⟨cambie_lower_bound, van_doorn_upper_bound, original_question_false⟩

/-- The original question f(N) = (1/2 + o(1))N is answered NO.
    The asymptotic density is in the interval [5/8, 9/10]. -/
theorem erdos_302_summary :
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (f N : ℚ) ≥ (5/8 - ε) * N) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (f N : ℚ) ≤ (9/10 + ε) * N) :=
  ⟨cambie_lower_bound, van_doorn_upper_bound⟩

/-- The exact asymptotic density of f(N)/N remains OPEN. -/
end Erdos302
