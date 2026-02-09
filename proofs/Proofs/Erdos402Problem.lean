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

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
Definition of the condition that for all pairs (a,b) in A, gcd(a,b) >= a / |A|.
-/
open Nat Finset

def SatisfiesGrahamCondition (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, Nat.gcd a b ≥ a / A.card

/-
The set {1, 2, 4} satisfies the Graham condition gcd(a,b) >= a/|A|.
-/
theorem counterexample_124_satisfies :
    SatisfiesGrahamCondition {1, 2, 4} := by
      intro a ha b hb; fin_cases ha <;> fin_cases hb <;> trivial;

/-
The set {1, 2, 4} has gcd 1.
-/
theorem counterexample_124_primitive :
    Erdos402.HasNoCommonDivisor {1, 2, 4} := by
      -- Since 1 is in the set, the gcd must divide 1, so it must be 1. Therefore, the gcd is 1.
      simp [Erdos402.HasNoCommonDivisor]

/-
The set {1, 2, 4} is not one of the Graham equality cases.
-/
theorem counterexample_124_not_case :
    ¬ Erdos402.IsGrahamEqualityCase {1, 2, 4} := by
      rintro ⟨ n, hn, h ⟩;
      · rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ Finset.ext_iff ];
        exact absurd ( h 3 ) ( by norm_num );
      · rename_i h;
        rcases h with ( ⟨ n, hn, L, rfl, h ⟩ | h ) <;> simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
        rcases h with ⟨ ⟨ ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ b, ⟨ hb₁, hb₂ ⟩, hb₃ ⟩, ⟨ c, ⟨ hc₁, hc₂ ⟩, hc₃ ⟩ ⟩, h ⟩ ; have := @h ( ( Finset.range ( n + 1 ) \ { 0 } ).lcm id / 1 ) 1 ; simp_all +decide ;
        rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide [ Finset.range_add_one ];
        · interval_cases b <;> contradiction;
        · interval_cases c <;> contradiction;
        · rcases this with h | h | h <;> simp_all +decide [ Nat.lcm_assoc ];
          · rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> rcases c with ( _ | _ | c ) <;> simp_all +arith +decide [ Nat.div_eq_of_lt ];
          · exact absurd hc₃ ( Nat.ne_of_lt ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.pos_of_ne_zero hc₂ ] ) );
          · have := h ▸ Finset.dvd_lcm ( show n + 5 ∈ _ from by simp +decide ) ; simp_all +decide [ Nat.dvd_prime ] ;
            linarith [ Nat.le_of_dvd ( by norm_num ) this ]

/-
The Graham equality conjecture is false, witnessed by {1, 2, 4}.
-/
theorem erdos_402_equality_cases_false :
    ¬ (∀ A : Finset ℕ, A.Nonempty → (∀ x ∈ A, x > 0) → Erdos402.HasNoCommonDivisor A →
       (∀ a ∈ A, ∀ b ∈ A, Nat.gcd a b ≥ a / A.card) → Erdos402.IsGrahamEqualityCase A) := by
         push_neg;
         -- Consider the set $A = \{1, 2, 4\}$.
         use {1, 2, 4};
         simp +zetaDelta at *;
         refine' ⟨ _, _ ⟩;
         · exact?;
         · exact?

end AristotleLemmas

/-
**Graham's Equality Conjecture**: The only primitive sets achieving equality
in the GCD bound are the three families described above.
-/
theorem erdos_402_equality_cases (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) (hprim : HasNoCommonDivisor A)
    (heq : ∀ a ∈ A, ∀ b ∈ A, Nat.gcd a b ≥ a / A.card) :
    IsGrahamEqualityCase A := by
  -- Proved by Szegedy for large sets
  by_contra! h_contra2_equality_cases_false;
  apply_rules [ erdos_402_equality_cases_false ];
  apply Classical.byContradiction
  intro h_contra2_equality_cases_false_2;
  apply h_contra2_equality_cases_false_2;
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Consider the set $A = \{1, 2, 4\}$.
  use {1, 2, 4};
  -- Check that the set {1, 2, 4} is nonempty.
  simp [Erdos402.HasNoCommonDivisor];
  -- Show that {1, 2, 4} is not one of the Graham equality cases by checking each case.
  apply counterexample_124_not_case

-/
/--
**Graham's Equality Conjecture**: The only primitive sets achieving equality
in the GCD bound are the three families described above.
-/
theorem erdos_402_equality_cases (A : Finset ℕ) (hA : A.Nonempty)
    (hpos : ∀ x ∈ A, x > 0) (hprim : HasNoCommonDivisor A)
    (heq : ∀ a ∈ A, ∀ b ∈ A, Nat.gcd a b ≥ a / A.card) :
    IsGrahamEqualityCase A := by
  -- Proved by Szegedy for large sets
  sorry

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