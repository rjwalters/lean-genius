/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 814a190f-8a5d-4624-a56d-ccc10ab964ee

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem erdos_402_ratio_bound (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) :
    ∃ a ∈ A, ∃ b ∈ A, (Nat.gcd a b : ℚ) / a ≤ 1 / A.card

- theorem erdos_402_range (n : ℕ) (hn : n ≥ 1) :
    ∃ a ∈ Finset.range (n + 1) \ {0}, ∃ b ∈ Finset.range (n + 1) \ {0},
    Nat.gcd a b ≤ a / (Finset.range (n + 1) \ {0}).card

The following was negated by Aristotle:

- theorem erdos_402_equality_cases (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) (hprim : HasNoCommonDivisor A)
    (heq : ∀ a ∈ A, ∀ b ∈ A, Nat.gcd a b ≥ a / A.card) :
    IsGrahamEqualityCase A

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
  Erdős Problem #402: Graham's GCD Conjecture

  Source: https://erdosproblems.com/402
  Status: SOLVED (Balasubramanian-Soundararajan 1996)

  Statement:
  For any finite set A ⊂ ℕ, there exist a, b ∈ A such that
  gcd(a, b) ≤ a / |A|.

  Answer: TRUE

  History:
  - Graham (1970): Conjectured the result
  - Szegedy (1986): Proved for all sufficiently large sets
  - Zaharescu (1987): Independent proof for large sets
  - Balasubramanian & Soundararajan (1996): Completed proof for all finite sets

  Graham's Additional Conjecture:
  If A has no common divisor (gcd of all elements is 1), then equality
  gcd(a,b) = a/|A| is achieved only when:
  - A = {1, 2, ..., n}, or
  - A = {L/1, L/2, ..., L/n} where L = lcm(1, ..., n), or
  - A = {2, 3, 4, 6}

  Reference: Graham (1970), Balasubramanian-Soundararajan (1996)
-/

import Mathlib


namespace Erdos402

open Nat Finset

/-! ## Main Statement -/

/- Aristotle failed to find a proof. -/
/--
**Graham's GCD Conjecture (Erdős #402)**:
For any finite set A ⊂ ℕ with |A| ≥ 1, there exist elements a, b ∈ A
such that gcd(a, b) ≤ a / |A|.
-/
theorem erdos_402_graham_conjecture (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) :
    ∃ a ∈ A, ∃ b ∈ A, Nat.gcd a b ≤ a / A.card := by
  -- Proved by Balasubramanian and Soundararajan (1996)
  sorry

/-! ## Equivalent Formulation -/

/--
Alternative formulation: The minimum gcd ratio is at most 1/|A|.
-/
def MinGcdRatio (A : Finset ℕ) : ℚ :=
  if h : A.Nonempty ∧ ∀ x ∈ A, x > 0 then
    A.inf' h.1 fun a =>
      A.inf' h.1 fun b =>
        (Nat.gcd a b : ℚ) / a
  else 1

theorem erdos_402_ratio_bound (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) :
    ∃ a ∈ A, ∃ b ∈ A, (Nat.gcd a b : ℚ) / a ≤ 1 / A.card := by
  -- By the Erdős–Graham conjecture, there exist elements $a$ and $b$ in $A$ such that $\gcd(a, b) \leq \frac{a}{|A|}$.
  obtain ⟨a, haA, b, hbA, hab⟩ : ∃ a ∈ A, ∃ b ∈ A, Nat.gcd a b ≤ a / A.card := by
    -- Apply the Erdős–Graham conjecture to the set A.
    apply erdos_402_graham_conjecture A hA hpos;
  field_simp;
  -- By multiplying both sides of the inequality gcd(a, b) ≤ a / |A| by |A|, we get gcd(a, b) * |A| ≤ a.
  have h_mul : (Nat.gcd a b : ℕ) * A.card ≤ a := by
    exact le_trans ( Nat.mul_le_mul_right _ hab ) ( Nat.div_mul_le_self _ _ );
  -- Since $a$ is positive, dividing both sides of $gcd(a, b) * |A| ≤ a$ by $a$ preserves the inequality.
  use a, haA, b, hbA
  have h_div : (Nat.gcd a b : ℚ) * A.card / a ≤ 1 := by
    exact div_le_one_of_le₀ ( mod_cast h_mul ) ( Nat.cast_nonneg _ )
  exact h_div

/-! ## Special Cases -/

/-- For singleton sets, the result is trivial: gcd(a,a) = a ≤ a/1 = a. -/
theorem erdos_402_singleton (a : ℕ) (_ : a > 0) :
    ∃ x ∈ ({a} : Finset ℕ), ∃ y ∈ ({a} : Finset ℕ),
    Nat.gcd x y ≤ x / ({a} : Finset ℕ).card := by
  use a, mem_singleton_self a, a, mem_singleton_self a
  simp [Nat.gcd_self]

/-- For {1, 2, ..., n}, we have gcd(1,1) = 1 ≤ 1/n for n = 1. -/
theorem erdos_402_range (n : ℕ) (hn : n ≥ 1) :
    ∃ a ∈ Finset.range (n + 1) \ {0}, ∃ b ∈ Finset.range (n + 1) \ {0},
    Nat.gcd a b ≤ a / (Finset.range (n + 1) \ {0}).card := by
  -- Use a = n, b = n: gcd(n,n) = n, and n/n = 1, so n ≤ 1 only for n = 1
  -- Better: use a = 1, b = 1 for n = 1; otherwise need different approach
  -- For this formalization, we use sorry for the general case
  rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Finset.card_sdiff ];
  refine' ⟨ n + 2, ⟨ le_rfl, Nat.succ_ne_zero _ ⟩, 1, ⟨ Nat.le_add_left _ _, Nat.one_ne_zero ⟩, _ ⟩ ; norm_num [ Nat.div_eq_of_lt ]

/-! ## The {2, 3, 4, 6} Example -/

/-- The special set {2, 3, 4, 6} mentioned by Graham. -/
def GrahamSpecialSet : Finset ℕ := {2, 3, 4, 6}

theorem graham_special_card : GrahamSpecialSet.card = 4 := by native_decide

/-- In {2, 3, 4, 6}, gcd(4, 3) = 1 and 4/4 = 1, so 1 ≤ 1 ✓ -/
theorem graham_special_example :
    ∃ a ∈ GrahamSpecialSet, ∃ b ∈ GrahamSpecialSet,
    Nat.gcd a b ≤ a / GrahamSpecialSet.card := by
  -- Use a = 4, b = 3: gcd(4, 3) = 1, and 4/4 = 1, so 1 ≤ 1 ✓
  use 4
  constructor
  · decide
  use 3
  constructor
  · decide
  -- gcd(4, 3) = 1, 4/4 = 1
  native_decide

/-! ## Graham's Equality Characterization -/

/--
A set A has no common divisor if gcd of all elements is 1.
-/
def HasNoCommonDivisor (A : Finset ℕ) : Prop :=
  A.gcd id = 1

/--
Graham's characterization of equality cases.
When A has no common divisor, equality gcd(a,b) = a/|A| for the optimal pair
is achieved only for:
1. A = {1, ..., n}
2. A = {lcm(1,...,n)/1, ..., lcm(1,...,n)/n}
3. A = {2, 3, 4, 6}
-/
def IsGrahamEqualityCase (A : Finset ℕ) : Prop :=
  (∃ n : ℕ, n ≥ 1 ∧ A = Finset.range (n + 1) \ {0}) ∨
  (∃ n : ℕ, n ≥ 1 ∧ ∃ L : ℕ, L = (Finset.range (n + 1) \ {0}).lcm id ∧
    A = (Finset.range (n + 1) \ {0}).image fun k => L / k) ∨
  A = GrahamSpecialSet

/-! ## Equality Characterization: DISPROVED

Graham conjectured that the only primitive sets achieving equality in the
GCD bound are {1,...,n}, {L/1,...,L/n}, and {2,3,4,6}. However, when
formalized as "all pairs satisfy gcd(a,b) ≥ a/|A|", the set {1,2,4}
is a counterexample: it's primitive, satisfies the condition, but is
not one of the three families.

The counterexample was discovered by Aristotle (automated proof search).
-/

/-- {1,2,4} satisfies gcd(a,b) ≥ a/|A| for all pairs. -/
theorem counterexample_124_satisfies (a : ℕ) (ha : a ∈ ({1, 2, 4} : Finset ℕ))
    (b : ℕ) (hb : b ∈ ({1, 2, 4} : Finset ℕ)) :
    Nat.gcd a b ≥ a / ({1, 2, 4} : Finset ℕ).card := by
  fin_cases ha <;> fin_cases hb <;> simp_all +decide

/-- {1,2,4} is primitive (gcd of all elements is 1). -/
theorem counterexample_124_primitive : HasNoCommonDivisor {1, 2, 4} := by
  simp [HasNoCommonDivisor]

/-- {1,2,4} is NOT one of the three Graham equality cases.

  Case 1: 3 ∉ {1,2,4} but 3 ∈ {1,...,n} for n ≥ 4, and card differs for n ≤ 3.
  Case 2: L/1 = L ∈ {1,2,4} so 3 ∤ L, but 3 | lcm(1,...,n) for n ≥ 3, so n ≤ 2,
          and then image card ≤ 2 < 3.
  Case 3: {1,2,4} ≠ {2,3,4,6} by decide.
-/
theorem counterexample_124_not_equality_case :
    ¬IsGrahamEqualityCase ({1, 2, 4} : Finset ℕ) := by
  intro h
  rcases h with ⟨n, hn, heq⟩ | ⟨n, hn, L, hL, heq⟩ | heq
  · -- Case 1: {1,2,4} = {1,...,n}. Use "3 is missing" argument.
    have h3 : (3 : ℕ) ∉ ({1, 2, 4} : Finset ℕ) := by decide
    have h4 : (4 : ℕ) ∈ ({1, 2, 4} : Finset ℕ) := by decide
    rw [heq] at h3 h4
    simp [Finset.mem_sdiff, Finset.mem_range] at h3 h4
    omega
  · -- Case 2: {1,2,4} = image of (fun k => L / k) over {1,...,n} where L = lcm.
    -- Step 1: L/1 = L is in the image = {1,2,4}, so L ∈ {1,2,4}
    have h1_mem : (1 : ℕ) ∈ Finset.range (n + 1) \ {0} := by
      simp [Finset.mem_sdiff, Finset.mem_range]; omega
    have hL_in_img : L / 1 ∈ (Finset.range (n + 1) \ {0}).image (fun k => L / k) :=
      Finset.mem_image_of_mem _ h1_mem
    rw [Nat.div_one] at hL_in_img
    rw [← heq] at hL_in_img
    -- Step 2: L ∈ {1,2,4} means 3 ∤ L
    have h3_ndvd : ¬(3 ∣ L) := by fin_cases hL_in_img <;> omega
    -- Step 3: If n ≥ 3 then 3 ∈ {1,...,n}, so 3 | lcm = L. Contradiction.
    have hn2 : n ≤ 2 := by
      by_contra h_gt; push_neg at h_gt
      have h3_mem : (3 : ℕ) ∈ Finset.range (n + 1) \ {0} := by
        simp [Finset.mem_sdiff, Finset.mem_range]; omega
      exact h3_ndvd (hL ▸ Finset.dvd_lcm h3_mem)
    -- Step 4: For n ≤ 2, image card ≤ n ≤ 2 < 3 = card({1,2,4}). Contradiction.
    have hcard : ({1, 2, 4} : Finset ℕ).card = 3 := by decide
    rw [heq] at hcard
    have hle : ((Finset.range (n + 1) \ {0}).image (fun k => L / k)).card ≤
        (Finset.range (n + 1) \ {0}).card := Finset.card_image_le
    simp [Finset.card_sdiff, Finset.card_range,
          Finset.singleton_subset_iff, Finset.mem_range] at hle
    omega
  · -- Case 3: {1,2,4} = {2,3,4,6}
    exact absurd heq (by decide)

/-! ## Key Lemmas -/

/-- For coprime elements, gcd(a,b) = 1 ≤ a/|A| when |A| ≤ a. -/
theorem gcd_one_suffices (A : Finset ℕ) (a b : ℕ)
    (hcop : Nat.Coprime a b) (hcard : A.card ≤ a) (hApos : A.card > 0) :
    Nat.gcd a b ≤ a / A.card := by
  rw [Nat.Coprime] at hcop
  rw [hcop]
  exact Nat.one_le_div_iff hApos |>.mpr hcard

/-- If A = {1} (singleton containing 1), gcd(1,1) = 1 ≤ 1/1 = 1 works. -/
theorem one_in_singleton_set :
    ∃ a ∈ ({1} : Finset ℕ), ∃ b ∈ ({1} : Finset ℕ), Nat.gcd a b ≤ a / ({1} : Finset ℕ).card := by
  use 1, mem_singleton_self 1, 1, mem_singleton_self 1
  simp [Nat.gcd_self]

/-- A proper divisor of a positive number is at most half that number.
    If d ∣ n and d < n, then n = d·k with k ≥ 2, so d·2 ≤ n, hence d ≤ n/2. -/
theorem dvd_lt_imp_le_half {d n : ℕ} (hd : d ∣ n) (hlt : d < n) : d ≤ n / 2 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hlt
    · simp at hlt
    · omega
  calc d = d * 2 / 2 := by omega
    _ ≤ d * k / 2 := Nat.div_le_div_right (Nat.mul_le_mul_left d hk)

/-- Graham's conjecture for two-element sets. For distinct positive naturals,
    gcd is a proper divisor of the larger, hence ≤ max/2 = max/|{a,b}|. -/
theorem erdos_402_pair (a b : ℕ) (ha : a > 0) (hb : b > 0) (hab : a ≠ b) :
    ∃ x ∈ ({a, b} : Finset ℕ), ∃ y ∈ ({a, b} : Finset ℕ),
    Nat.gcd x y ≤ x / ({a, b} : Finset ℕ).card := by
  have hcard : ({a, b} : Finset ℕ).card = 2 := Finset.card_pair hab
  rcases le_or_lt a b with h | h
  · -- a ≤ b, a ≠ b ⟹ a < b. Use x = b, y = a.
    have hlt : a < b := lt_of_le_of_ne h hab
    refine ⟨b, by simp, a, by simp, ?_⟩
    rw [hcard]
    exact dvd_lt_imp_le_half (Nat.gcd_dvd_left b a)
      (lt_of_le_of_lt (Nat.le_of_dvd ha (Nat.gcd_dvd_right b a)) hlt)
  · -- b < a. Use x = a, y = b.
    refine ⟨a, by simp, b, by simp, ?_⟩
    rw [hcard]
    exact dvd_lt_imp_le_half (Nat.gcd_dvd_left a b)
      (lt_of_le_of_lt (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) h)

/-- The maximum of a nonempty Finset of positive naturals is at least its cardinality.
    Proof: A injects into {1, ..., max(A)}, which has exactly max(A) elements. -/
theorem max_ge_card_of_pos (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) : A.card ≤ A.max' hA := by
  have hsub : A ⊆ Finset.range (A.max' hA + 1) \ {0} := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
    exact ⟨Nat.lt_succ_of_le (Finset.le_max' A x hx), Nat.pos_iff_ne_zero.mp (hpos x hx)⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr (by omega))),
      Finset.card_range, Finset.card_singleton] at hle
  omega

/-- Graham's conjecture holds when 1 ∈ A: gcd(max, 1) = 1 ≤ max/|A|
    since max(A) ≥ |A| for any nonempty set of positive naturals. -/
theorem erdos_402_contains_one (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) (h1 : (1 : ℕ) ∈ A) :
    ∃ a ∈ A, ∃ b ∈ A, Nat.gcd a b ≤ a / A.card := by
  refine ⟨A.max' hA, Finset.max'_mem A hA, 1, h1, ?_⟩
  rw [Nat.gcd_one_right]
  have := Nat.div_pos (max_ge_card_of_pos A hA hpos) (Finset.card_pos.mpr hA)
  omega

/-! ## Three-Element Case Infrastructure -/

/-- A proper divisor of n exceeding n/3 must be exactly n/2 (forcing n even).
    If d | n and d < n, then n = d·k with k ≥ 2. If also n/3 < d, then k < 3, so k = 2. -/
theorem proper_divisor_gt_third {d n : ℕ} (hd : d ∣ n) (hdn : d < n) (hgt : n / 3 < d) :
    2 * d = n := by
  obtain ⟨k, rfl⟩ := hd
  suffices k = 2 by subst this; ring
  have hd_pos : 0 < d := by
    rcases d with _ | d
    · simp at hgt
    · omega
  have : k ≥ 2 := by
    rcases k with _ | _ | k
    · simp at hdn
    · simp at hdn
    · omega
  have : k ≤ 2 := by
    by_contra hk3
    push_neg at hk3
    have h1 : d * 3 ≤ d * k := Nat.mul_le_mul_left d hk3
    have h2 : d * 3 / 3 ≤ d * k / 3 := Nat.div_le_div_right h1
    rw [Nat.mul_div_cancel d (by omega : (0 : ℕ) < 3)] at h2
    omega
  omega

/-- Unique multiple in range: if m > 0 divides y with 0 < y < 2·m, then y = m. -/
theorem eq_of_dvd_of_lt_twice {m y : ℕ} (hm : m > 0) (hdvd : m ∣ y)
    (hy_pos : y > 0) (hy_lt : y < 2 * m) : y = m := by
  obtain ⟨k, rfl⟩ := hdvd
  suffices k = 1 by subst this; ring
  have : k ≥ 1 := by
    rcases k with _ | k
    · simp at hy_pos; omega
    · omega
  have : k ≤ 1 := by
    by_contra hk
    push_neg at hk
    have : m * k < m * 2 := by linarith
    exact absurd ((mul_lt_mul_left hm).mp this) (by omega)
  omega

/-- Among two distinct positive naturals below x, at least one has gcd(x, ·) ≤ x/3.
    Both gcd(x, yᵢ) are proper divisors of x. A proper divisor > x/3 must equal x/2,
    forcing yᵢ = x/2. Two such yᵢ would be equal, contradicting distinctness. -/
theorem gcd_le_third_of_two_lt {x y1 y2 : ℕ} (hx : x > 0)
    (hy1_pos : y1 > 0) (hy2_pos : y2 > 0)
    (hy1_lt : y1 < x) (hy2_lt : y2 < x) (hne : y1 ≠ y2) :
    Nat.gcd x y1 ≤ x / 3 ∨ Nat.gcd x y2 ≤ x / 3 := by
  by_contra hall
  push_neg at hall
  obtain ⟨h1, h2⟩ := hall
  have hg1_lt : Nat.gcd x y1 < x :=
    lt_of_le_of_lt (Nat.le_of_dvd hy1_pos (Nat.gcd_dvd_right x y1)) hy1_lt
  have hg2_lt : Nat.gcd x y2 < x :=
    lt_of_le_of_lt (Nat.le_of_dvd hy2_pos (Nat.gcd_dvd_right x y2)) hy2_lt
  have heq1 : 2 * Nat.gcd x y1 = x :=
    proper_divisor_gt_third (Nat.gcd_dvd_left x y1) hg1_lt h1
  have heq2 : 2 * Nat.gcd x y2 = x :=
    proper_divisor_gt_third (Nat.gcd_dvd_left x y2) hg2_lt h2
  have hy1_eq : y1 = Nat.gcd x y1 :=
    eq_of_dvd_of_lt_twice (by omega) (Nat.gcd_dvd_right x y1) hy1_pos (by omega)
  have hy2_eq : y2 = Nat.gcd x y2 :=
    eq_of_dvd_of_lt_twice (by omega) (Nat.gcd_dvd_right x y2) hy2_pos (by omega)
  exact hne (by omega)

/-! ## Three-Element Case -/

/-- Graham's conjecture for three-element sets.
    Take x = max{a,b,c}. The other two elements are distinct and < x.
    By `gcd_le_third_of_two_lt`, at least one has gcd ≤ x/3 with the max. -/
theorem erdos_402_triple (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ x ∈ ({a, b, c} : Finset ℕ), ∃ y ∈ ({a, b, c} : Finset ℕ),
    Nat.gcd x y ≤ x / ({a, b, c} : Finset ℕ).card := by
  set A : Finset ℕ := {a, b, c}
  have ha_not : a ∉ ({b, c} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hab, hac⟩
  have hb_not : b ∉ ({c} : Finset ℕ) := Finset.not_mem_singleton.mpr hbc
  have hcard : A.card = 3 := by
    simp only [A, Finset.card_insert_of_not_mem ha_not, Finset.card_insert_of_not_mem hb_not,
               Finset.card_singleton]
  simp_rw [hcard]
  have hne : A.Nonempty := ⟨a, by simp [A]⟩
  have hpos : ∀ x ∈ A, x > 0 := by
    intro x hx; simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  set m := A.max' hne
  have hm_mem : m ∈ A := Finset.max'_mem A hne
  have hm_pos : m > 0 := hpos m hm_mem
  have herase_card : (A.erase m).card = 2 := by
    rw [Finset.card_erase_of_mem hm_mem, hcard]
  obtain ⟨y1, y2, hne12, herase_eq⟩ := Finset.card_eq_two.mp herase_card
  have hy1_er : y1 ∈ A.erase m := herase_eq ▸ by simp
  have hy2_er : y2 ∈ A.erase m := herase_eq ▸ by simp
  have hy1_mem : y1 ∈ A := Finset.mem_of_mem_erase hy1_er
  have hy2_mem : y2 ∈ A := Finset.mem_of_mem_erase hy2_er
  have hy1_lt : y1 < m :=
    lt_of_le_of_ne (Finset.le_max' A y1 hy1_mem) (Finset.ne_of_mem_erase hy1_er)
  have hy2_lt : y2 < m :=
    lt_of_le_of_ne (Finset.le_max' A y2 hy2_mem) (Finset.ne_of_mem_erase hy2_er)
  rcases gcd_le_third_of_two_lt hm_pos (hpos y1 hy1_mem) (hpos y2 hy2_mem)
      hy1_lt hy2_lt hne12 with h | h
  · exact ⟨m, hm_mem, y1, hy1_mem, h⟩
  · exact ⟨m, hm_mem, y2, hy2_mem, h⟩

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #402 (Graham's Conjecture) asks: for any finite set A ⊂ ℕ,
do there exist a, b ∈ A with gcd(a,b) ≤ a/|A|?

**Answer: YES**

The problem was progressively solved:
- Szegedy (1986) and Zaharescu (1987) proved it for large sets
- Balasubramanian & Soundararajan (1996) completed the proof for all sets

**Graham's Additional Conjecture** characterizes when equality holds:
only for {1,...,n}, {L/1,...,L/n}, or {2,3,4,6} (when A is primitive).

**References**:
- Graham, R. L. (1970): Original conjecture
- Balasubramanian, R. & Soundararajan, K. (1996): Complete proof
-/

end Erdos402