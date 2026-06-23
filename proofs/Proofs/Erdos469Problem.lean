/-
Erdős Problem #469: Primitive Pseudoperfect Numbers

A positive integer n is pseudoperfect (also called semiperfect) if it can be
written as a sum of distinct proper divisors. It is primitive pseudoperfect
if n is pseudoperfect but no proper divisor m | n (m < n) is pseudoperfect.

Let A be the set of primitive pseudoperfect numbers (OEIS A006036).
Does Σ_{n ∈ A} 1/n converge?

Known members of A include: 6, 20, 28, 88, 104, 272, 304, 350, ...

Status: OPEN.

Reference: https://erdosproblems.com/469
-/

import Mathlib

namespace Erdos469

-- ## Definitions

/-- n is pseudoperfect (semiperfect): n can be written as a sum of
    distinct proper divisors of n. -/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ S.sum id = n

/-- n is primitive pseudoperfect: n is pseudoperfect, but no proper
    divisor of n (less than n) is pseudoperfect. -/
def IsPrimitivePseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ IsPseudoperfect n ∧
  ∀ m : ℕ, m < n → m ∣ n → ¬IsPseudoperfect m

/-- The set A of primitive pseudoperfect numbers. -/
def primitivePseudoperfectSet : Set ℕ :=
  {n : ℕ | IsPrimitivePseudoperfect n}

-- ## Perfect Numbers are Pseudoperfect

/-- Every perfect number is pseudoperfect: if the proper divisors sum to n,
    then using all proper divisors gives a representation n = d₁ + ... + dₖ. -/
theorem perfect_is_pseudoperfect (n : ℕ) (hn : 0 < n)
    (hperf : n.properDivisors.sum id = n) : IsPseudoperfect n :=
  ⟨n.properDivisors, le_refl _, hperf⟩

-- ## Verified Pseudoperfect Numbers via Explicit Witnesses

/-- 6 is pseudoperfect: 6 = 1 + 2 + 3, using divisors {1, 2, 3} -/
theorem pseudoperfect_6 : IsPseudoperfect 6 :=
  ⟨{1, 2, 3}, by decide, by decide⟩

/-- 12 is pseudoperfect: 12 = 1 + 2 + 3 + 6 -/
theorem pseudoperfect_12 : IsPseudoperfect 12 :=
  ⟨{1, 2, 3, 6}, by decide, by decide⟩

/-- 20 is pseudoperfect: 20 = 1 + 4 + 5 + 10 -/
theorem pseudoperfect_20 : IsPseudoperfect 20 :=
  ⟨{1, 4, 5, 10}, by decide, by decide⟩

-- ## Non-pseudoperfect: deficiency argument
--
-- For n ≤ 5, the sum of ALL proper divisors is < n, so no subset can reach n.

/-- Helper: subset sum bounded by total sum -/
private theorem subset_sum_le_total (n : ℕ) (S : Finset ℕ) (hS : S ⊆ n.properDivisors) :
    S.sum id ≤ n.properDivisors.sum id :=
  Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)

theorem not_pseudoperfect_0 : ¬IsPseudoperfect 0 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 0 S hS_sub
  have : (0 : ℕ).properDivisors.sum id = 0 := by decide
  omega

theorem not_pseudoperfect_1 : ¬IsPseudoperfect 1 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 1 S hS_sub
  have : (1 : ℕ).properDivisors.sum id = 0 := by decide
  omega

theorem not_pseudoperfect_2 : ¬IsPseudoperfect 2 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 2 S hS_sub
  have : (2 : ℕ).properDivisors.sum id = 1 := by decide
  omega

theorem not_pseudoperfect_3 : ¬IsPseudoperfect 3 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 3 S hS_sub
  have : (3 : ℕ).properDivisors.sum id = 1 := by decide
  omega

theorem not_pseudoperfect_4 : ¬IsPseudoperfect 4 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 4 S hS_sub
  have : (4 : ℕ).properDivisors.sum id = 3 := by decide
  omega

theorem not_pseudoperfect_5 : ¬IsPseudoperfect 5 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 5 S hS_sub
  have : (5 : ℕ).properDivisors.sum id = 1 := by decide
  omega

/-- 28 is pseudoperfect: 28 = 1 + 2 + 4 + 7 + 14 (perfect number) -/
theorem pseudoperfect_28 : IsPseudoperfect 28 :=
  ⟨{1, 2, 4, 7, 14}, by decide, by decide⟩

-- ## Non-pseudoperfect: additional cases needed for primitivity proofs

theorem not_pseudoperfect_7 : ¬IsPseudoperfect 7 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 7 S hS_sub
  have : (7 : ℕ).properDivisors.sum id = 1 := by decide
  omega

theorem not_pseudoperfect_10 : ¬IsPseudoperfect 10 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 10 S hS_sub
  have : (10 : ℕ).properDivisors.sum id = 8 := by decide
  omega

theorem not_pseudoperfect_14 : ¬IsPseudoperfect 14 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 14 S hS_sub
  have : (14 : ℕ).properDivisors.sum id = 10 := by decide
  omega

-- Non-pseudoperfect: proper divisors of 88

theorem not_pseudoperfect_8 : ¬IsPseudoperfect 8 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 8 S hS_sub
  have : (8 : ℕ).properDivisors.sum id = 7 := by decide
  omega

theorem not_pseudoperfect_11 : ¬IsPseudoperfect 11 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 11 S hS_sub
  have : (11 : ℕ).properDivisors.sum id = 1 := by decide
  omega

theorem not_pseudoperfect_22 : ¬IsPseudoperfect 22 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 22 S hS_sub
  have : (22 : ℕ).properDivisors.sum id = 14 := by decide
  omega

theorem not_pseudoperfect_44 : ¬IsPseudoperfect 44 := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total 44 S hS_sub
  have : (44 : ℕ).properDivisors.sum id = 40 := by decide
  omega

-- ## Key Structural Results

/-- The smallest pseudoperfect number is 6 -/
theorem pseudoperfect_ge_six (n : ℕ) (h : IsPseudoperfect n) : n ≥ 6 := by
  by_contra hlt
  push_neg at hlt
  interval_cases n
  · exact not_pseudoperfect_0 h
  · exact not_pseudoperfect_1 h
  · exact not_pseudoperfect_2 h
  · exact not_pseudoperfect_3 h
  · exact not_pseudoperfect_4 h
  · exact not_pseudoperfect_5 h

-- ## Verified Primitive Pseudoperfect Numbers (OEIS A006036)

/-- 6 is the smallest primitive pseudoperfect number:
    6 = 1 + 2 + 3 (pseudoperfect), and no proper divisor {1,2,3} is pseudoperfect
    since the smallest pseudoperfect number is 6 itself. -/
theorem primitive_pseudoperfect_6 : IsPrimitivePseudoperfect 6 := by
  refine ⟨by norm_num, pseudoperfect_6, ?_⟩
  intro m hm _ hps
  exact absurd (pseudoperfect_ge_six m hps) (by omega)

/-- 20 is the second primitive pseudoperfect number (A006036):
    20 = 1 + 4 + 5 + 10, and no proper divisor of 20 is pseudoperfect.
    Proper divisors: {1, 2, 4, 5, 10}. Values 1-5 are not pseudoperfect
    (below the minimum 6). Value 10 has σ₀(10) = 8 < 10, so is deficient. -/
theorem primitive_pseudoperfect_20 : IsPrimitivePseudoperfect 20 := by
  refine ⟨by norm_num, pseudoperfect_20, ?_⟩
  intro m hm hdvd hps
  have hge := pseudoperfect_ge_six m hps
  -- m ≥ 6, m < 20, m ∣ 20 → m = 10
  interval_cases m <;>
    first
    | exact absurd hps not_pseudoperfect_10
    | exact absurd hdvd (by decide)

/-- 28 is the third primitive pseudoperfect number (A006036):
    28 = 1 + 2 + 4 + 7 + 14 (perfect number). No proper divisor is pseudoperfect.
    Proper divisors: {1, 2, 4, 7, 14}. Values 1-5 not pseudoperfect (below minimum 6).
    7 has σ₀(7) = 1 < 7, 14 has σ₀(14) = 10 < 14 — both deficient. -/
theorem primitive_pseudoperfect_28 : IsPrimitivePseudoperfect 28 := by
  refine ⟨by norm_num, pseudoperfect_28, ?_⟩
  intro m hm hdvd hps
  have hge := pseudoperfect_ge_six m hps
  -- m ≥ 6, m < 28, m ∣ 28 → m ∈ {7, 14}
  interval_cases m <;>
    first
    | exact absurd hps not_pseudoperfect_7
    | exact absurd hps not_pseudoperfect_14
    | exact absurd hdvd (by decide)

/-- 88 is pseudoperfect: 88 = 1 + 2 + 8 + 11 + 22 + 44 -/
theorem pseudoperfect_88 : IsPseudoperfect 88 :=
  ⟨{1, 2, 8, 11, 22, 44}, by decide, by decide⟩

/-- 88 is the fourth primitive pseudoperfect number (A006036):
    88 = 2³ × 11. Proper divisors: {1, 2, 4, 8, 11, 22, 44}, all deficient.
    σ₀(8) = 7, σ₀(11) = 1, σ₀(22) = 14, σ₀(44) = 40 — all less than the number. -/
theorem primitive_pseudoperfect_88 : IsPrimitivePseudoperfect 88 := by
  refine ⟨by norm_num, pseudoperfect_88, ?_⟩
  intro m hm hdvd hps
  have hge := pseudoperfect_ge_six m hps
  -- m ≥ 6, m < 88, m ∣ 88 → m ∈ {8, 11, 22, 44}, all deficient
  interval_cases m <;>
    first
    | exact absurd hps not_pseudoperfect_8
    | exact absurd hps not_pseudoperfect_11
    | exact absurd hps not_pseudoperfect_22
    | exact absurd hps not_pseudoperfect_44
    | exact absurd hdvd (by decide)

-- ## Structural Theorems

/-- n is pseudoperfect iff it's the sum of some subset of its proper divisors -/
theorem isPseudoperfect_iff (n : ℕ) :
    IsPseudoperfect n ↔ ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ S.sum id = n :=
  Iff.rfl

/-- If n is primitive pseudoperfect, then n > 0 -/
theorem primitive_pos (n : ℕ) (h : IsPrimitivePseudoperfect n) : 0 < n :=
  h.1

/-- If n is primitive pseudoperfect, then n is pseudoperfect -/
theorem primitive_is_pseudoperfect (n : ℕ) (h : IsPrimitivePseudoperfect n) :
    IsPseudoperfect n :=
  h.2.1

/-- If n is primitive pseudoperfect, no proper divisor of n is pseudoperfect -/
theorem primitive_no_divisor_pseudoperfect (n : ℕ) (h : IsPrimitivePseudoperfect n)
    (m : ℕ) (hm : m < n) (hdvd : m ∣ n) : ¬IsPseudoperfect m :=
  h.2.2 m hm hdvd

/-- Every primitive pseudoperfect number is ≥ 6 -/
theorem primitive_pseudoperfect_ge_six (n : ℕ) (h : IsPrimitivePseudoperfect n) :
    n ≥ 6 :=
  pseudoperfect_ge_six n h.2.1

-- ## Abundance and Pseudoperfection
--
-- A number n is abundant if σ(n) > 2n, i.e., the sum of all divisors exceeds 2n.
-- Equivalently, the sum of proper divisors exceeds n.

/-- Sum of proper divisors of n -/
noncomputable def sigma0 (n : ℕ) : ℕ := n.properDivisors.sum id

/-- n is abundant if its proper divisors sum to more than n -/
def IsAbundant (n : ℕ) : Prop := sigma0 n > n

/-- n is deficient if its proper divisors sum to less than n -/
def IsDeficient (n : ℕ) : Prop := sigma0 n < n

/-- n is perfect if its proper divisors sum to exactly n -/
def IsPerfect' (n : ℕ) : Prop := sigma0 n = n

/-- Deficient numbers are not pseudoperfect:
    if σ₀(n) < n, then no subset of proper divisors can sum to n. -/
theorem deficient_not_pseudoperfect (n : ℕ) (hdef : IsDeficient n) :
    ¬IsPseudoperfect n := by
  intro ⟨S, hS_sub, hS_sum⟩
  have := subset_sum_le_total n S hS_sub
  unfold IsDeficient sigma0 at hdef
  omega

-- ## Weird Numbers
--
-- A weird number is abundant but not pseudoperfect.
-- The smallest weird number is 70.

/-- n is weird if it is abundant but not pseudoperfect -/
def IsWeird (n : ℕ) : Prop := IsAbundant n ∧ ¬IsPseudoperfect n

-- ## The Open Questions (OPEN)
--
-- The core of Erdős #469 remains open.

/-- **Erdős Problem #469 (OPEN)**: Does the sum of reciprocals of primitive
    pseudoperfect numbers converge?
    Σ_{n ∈ A} 1/n where A = {6, 20, 28, 88, 104, 272, ...}
    This is stated as a Prop definition (NOT axiom) since it is open. -/
def erdos469_conjecture : Prop :=
  Summable (fun n : ℕ => if IsPrimitivePseudoperfect n then (1 : ℝ) / n else 0)

/-- There are infinitely many primitive pseudoperfect numbers.
    Known: every even perfect number is primitive pseudoperfect (verified for 6, 28).
    This is also open, stated as a Prop definition. -/
def infinitely_many_primitive : Prop :=
  Set.Infinite primitivePseudoperfectSet

/-- Every multiple of a pseudoperfect number is pseudoperfect.
    Proof: if n = d₁ + ⋯ + dₖ with dᵢ proper divisors of n, then
    n·m = d₁·m + ⋯ + dₖ·m, and each dᵢ·m is a proper divisor of n·m. -/
theorem multiple_of_pseudoperfect (n m : ℕ) (hn : IsPseudoperfect n)
    (hm : 0 < m) : IsPseudoperfect (n * m) := by
  obtain ⟨S, hS_sub, hS_sum⟩ := hn
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a * m = b * m → a = b := by
    intro a _ b _ h; omega
  refine ⟨S.image (· * m), ?_, ?_⟩
  · -- Each d*m is a proper divisor of n*m
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd_mem, rfl⟩ := hx
    have hd := hS_sub hd_mem
    rw [Nat.mem_properDivisors] at hd ⊢
    exact ⟨mul_dvd_mul_right hd.1 m, Nat.mul_lt_mul_of_pos_right hd.2 hm⟩
  · -- Sum of {d*m : d ∈ S} = n*m
    rw [Finset.sum_image hinj]
    simp only [id] at hS_sum ⊢
    rw [← Finset.sum_mul, hS_sum]

end Erdos469
