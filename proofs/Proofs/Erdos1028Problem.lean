/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ecfa895b-88ce-4432-aa19-9f0b5db1f88c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem H_spec (n : ℕ) (hn : n ≥ 1) :
    ∃ f : SignFunction n, isValidSign f ∧ maxDiscrepancy f = H n

- theorem symmetric_pairSum (f : SignFunction n) (hf : isSymmetric f) (X : Finset (Fin n)) :
    pairSum f X = 2 * X.sum (fun x => (X.filter (· > x)).sum (fun y => f x y))

- theorem discrepancy_as_imbalance (f : SignFunction n) (X : Finset (Fin n)) :
    discrepancy f X = (X.sum (fun x => X.sum (fun y => asSignedGraph f x y))).natAbs

- theorem expected_discrepancy_bound (n k : ℕ) (hk : k ≤ n) :
    expectedDiscrepancy n k ≤ k

- theorem homogeneous_small_discrepancy (f : SignFunction n) (X : Finset (Fin n))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x y = 1) :
    discrepancy f X = X.card * (X.card - 1)

The following was negated by Aristotle:

- theorem erdos_lower (n : ℕ) (hn : n ≥ 4) :
    H n ≥ n / 4

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
Erdős Problem #1028: Discrepancy of Sign Functions

Let H(n) = min_f max_{X ⊆ {1,...,n}} |∑_{x≠y∈X} f(x,y)|, where f ranges over
all functions f: X² → {-1, 1}. Estimate H(n).

**Status**: SOLVED
**Answer**: H(n) = Θ(n^(3/2))

Reference: https://erdosproblems.com/1028
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic


open Finset

namespace Erdos1028

/-
## Sign Functions

A sign function assigns ±1 to each ordered pair.
-/

/-- A sign function on pairs. -/
abbrev SignFunction (n : ℕ) := Fin n → Fin n → Int

/-- A valid sign function maps to {-1, 1}. -/
def isValidSign (f : SignFunction n) : Prop :=
  ∀ x y : Fin n, f x y = 1 ∨ f x y = -1

/-- The set of valid sign functions. -/
def validSignFunctions (n : ℕ) : Set (SignFunction n) :=
  { f | isValidSign f }

/-
## Discrepancy

The discrepancy of a subset is the absolute value of the sum of f over pairs.
-/

/-- Sum of f(x,y) over distinct pairs in X. -/
def pairSum (f : SignFunction n) (X : Finset (Fin n)) : Int :=
  X.sum (fun x => X.sum (fun y => if x ≠ y then f x y else 0))

/-- The discrepancy of X under f. -/
def discrepancy (f : SignFunction n) (X : Finset (Fin n)) : ℕ :=
  (pairSum f X).natAbs

/-- Maximum discrepancy over all subsets. -/
noncomputable def maxDiscrepancy (f : SignFunction n) : ℕ :=
  sSup { discrepancy f X | X : Finset (Fin n) }

/-
## The Function H(n)

H(n) = min over valid f of max discrepancy.
-/

/-- H(n): minimum over sign functions of maximum discrepancy. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { maxDiscrepancy f | f ∈ validSignFunctions n }

/-- H(n) is well-defined (exists optimal f). -/
theorem H_spec (n : ℕ) (hn : n ≥ 1) :
    ∃ f : SignFunction n, isValidSign f ∧ maxDiscrepancy f = H n := by
  have h_exists : ∃ f ∈ validSignFunctions n, ∀ g ∈ validSignFunctions n, maxDiscrepancy f ≤ maxDiscrepancy g := by
    apply_rules [ Set.exists_min_image ];
    · exact Set.Finite.subset ( Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.toFinite { 1, -1 } ) fun f hf => by aesop;
    · exact ⟨ fun _ _ => 1, fun _ _ => Or.inl rfl ⟩;
  obtain ⟨ f, hf₁, hf₂ ⟩ := h_exists;
  exact ⟨ f, hf₁, le_antisymm ( le_csInf ⟨ Erdos1028.maxDiscrepancy f, ⟨ f, hf₁, rfl ⟩ ⟩ fun g hg => by aesop ) ( csInf_le ⟨ 0, by rintro x ⟨ g, hg₁, rfl ⟩ ; exact Nat.zero_le _ ⟩ ⟨ f, hf₁, rfl ⟩ ) ⟩

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
## Erdős's Bounds (1963)

Erdős proved n/4 ≤ H(n) ≪ n^(3/2).

Erdős lower bound: H(n) ≥ n/4.
-/
theorem erdos_lower (n : ℕ) (hn : n ≥ 4) :
    H n ≥ n / 4 := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose $n = 8$.
  use 8;
  -- By definition of $H$, we know that $H(8) \leq 1$.
  have h_le : (Erdos1028.H 8) ≤ 1 := by
    -- Let's choose any sign function $f$ on $\{0, 1, 2, 3, 4, 5, 6, 7\}$.
    obtain ⟨f, hf⟩ : ∃ f : Erdos1028.SignFunction 8, Erdos1028.isValidSign f ∧ Erdos1028.maxDiscrepancy f ≤ 1 := by
      -- Define the sign function $f$ such that $f(x, y) = 1$ if $x < y$ and $f(x, y) = -1$ if $x > y$.
      use fun x y => if x.val < y.val then 1 else -1;
      unfold Erdos1028.isValidSign Erdos1028.maxDiscrepancy;
      simp +zetaDelta at *;
      exact ⟨ fun x y => lt_or_ge _ _, csSup_le' fun x hx => by rcases hx with ⟨ X, rfl ⟩ ; exact by { revert X; native_decide } ⟩;
    exact le_trans ( csInf_le ⟨ 0, by rintro x ⟨ g, hg, rfl ⟩ ; exact Nat.zero_le _ ⟩ ⟨ f, hf.1, rfl ⟩ ) hf.2;
  exact ⟨ by norm_num, lt_of_le_of_lt h_le ( by norm_num ) ⟩

-/
/-
## Erdős's Bounds (1963)

Erdős proved n/4 ≤ H(n) ≪ n^(3/2).
-/

/-- Erdős lower bound: H(n) ≥ n/4. -/
theorem erdos_lower (n : ℕ) (hn : n ≥ 4) :
    H n ≥ n / 4 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.22

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- Erdős upper bound: H(n) ≤ C · n^(3/2). -/
axiom erdos_upper : ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N,
  (H n : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.31

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Unknown identifier `erdos_upper`
Tactic `rcases` failed: `x✝ : Prop` is not an inductive datatype-/
/-- Erdős's bounds combined. -/
theorem erdos_bounds : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * n ≤ H n ∧ (H n : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  obtain ⟨C, hC, N, hN⟩ := erdos_upper
  use 1/4, C, by norm_num, hC, max 4 N
  intro n hn
  constructor
  · have h4 : n ≥ 4 := le_of_max_le_left hn
    have := erdos_lower n h4
    calc (1/4 : ℝ) * n = n / 4 := by ring
      _ ≤ (n / 4 : ℕ) := by sorry
      _ ≤ H n := this
  · exact hN n (le_of_max_le_right hn)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.22

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-
## Erdős-Spencer Improvement (1971)

They proved H(n) ≫ n^(3/2), matching the upper bound.
-/

/-- Erdős-Spencer (1971): H(n) ≥ c · n^(3/2). -/
axiom erdos_spencer_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (H n : ℝ) ≥ c * (n : ℝ) ^ (3/2 : ℝ)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.15

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- The Erdős-Spencer bound improves Erdős's linear lower bound. -/
theorem erdos_spencer_improves (n : ℕ) (hn : n ≥ 2) :
    (n : ℝ) ≤ (n : ℝ) ^ (3/2 : ℝ) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.25

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  HPow ℝ ℝ ?m.37

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-
## The Main Result: H(n) = Θ(n^(3/2))

Combining bounds gives the exact order of magnitude.
-/

/-- H(n) = Θ(n^(3/2)). -/
theorem H_asymptotic : ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c * (n : ℝ) ^ (3/2 : ℝ) ≤ H n ∧ (H n : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  obtain ⟨c, hc, N₁, hN₁⟩ := erdos_spencer_lower
  obtain ⟨C, hC, N₂, hN₂⟩ := erdos_upper
  use c, C, hc, hC, max N₁ N₂
  intro n hn
  constructor
  · exact hN₁ n (le_of_max_le_left hn)
  · exact hN₂ n (le_of_max_le_right hn)

/-
## The Main Question Answered

The answer is H(n) = Θ(n^(3/2)).
-/

/-- The main question: estimate H(n). -/
def erdos_1028_question : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ h : ℕ → ℝ, ∃ N : ℕ, ∀ n ≥ N,
    c * h n ≤ H n ∧ (H n : ℝ) ≤ C * h n

/-- The answer: H(n) = Θ(n^(3/2)). -/
theorem erdos_1028_solved : erdos_1028_question := by
  obtain ⟨c, C, hc, hC, N, hN⟩ := H_asymptotic
  use c, C, hc, hC, fun n => (n : ℝ) ^ (3/2 : ℝ), N
  exact hN

/-
## Symmetric Functions

Often we consider symmetric f with f(x,y) = f(y,x).
-/

/-- A symmetric sign function. -/
def isSymmetric (f : SignFunction n) : Prop :=
  ∀ x y : Fin n, f x y = f y x

/-- For symmetric f, pairSum counts each pair twice. -/
theorem symmetric_pairSum (f : SignFunction n) (hf : isSymmetric f) (X : Finset (Fin n)) :
    pairSum f X = 2 * X.sum (fun x => (X.filter (· > x)).sum (fun y => f x y)) := by
  -- By definition of sum over a set, we can split the sum into two parts: one where x < y and one where x > y.
  have h_split : ∑ x ∈ X, ∑ y ∈ X, (if x ≠ y then f x y else 0) = ∑ x ∈ X, ∑ y ∈ X, (if x < y then f x y else 0) + ∑ x ∈ X, ∑ y ∈ X, (if x > y then f x y else 0) := by
    simp +decide only [← sum_add_distrib];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
    grind;
  -- Since $f$ is symmetric, we have $\sum_{x \in X} \sum_{y \in X} (if x > y then f x y else 0) = \sum_{x \in X} \sum_{y \in X} (if x < y then f x y else 0)$.
  have h_symm : ∑ x ∈ X, ∑ y ∈ X, (if x > y then f x y else 0) = ∑ x ∈ X, ∑ y ∈ X, (if x < y then f x y else 0) := by
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => by aesop;
  unfold Erdos1028.pairSum; simp_all +decide [ two_mul, Finset.sum_ite ] ;

/-
## Graph Interpretation

f defines a signed complete graph on n vertices.
-/

/-- View f as edge signs on complete graph. -/
def asSignedGraph (f : SignFunction n) : Fin n → Fin n → Int :=
  fun x y => if x ≠ y then f x y else 0

/-- Discrepancy = imbalance of induced subgraph. -/
theorem discrepancy_as_imbalance (f : SignFunction n) (X : Finset (Fin n)) :
    discrepancy f X = (X.sum (fun x => X.sum (fun y => asSignedGraph f x y))).natAbs := by
  unfold Erdos1028.discrepancy; aesop;

/-
## Probabilistic Intuition

Random sign functions achieve near-optimal discrepancy.
-/

/-- Expected discrepancy of a random subset under random f. -/
noncomputable def expectedDiscrepancy (n k : ℕ) : ℝ :=
  Real.sqrt (k * (k - 1) : ℝ)

/-- For subset of size k, expected discrepancy is O(k). -/
theorem expected_discrepancy_bound (n k : ℕ) (hk : k ≤ n) :
    expectedDiscrepancy n k ≤ k := by
  exact Real.sqrt_le_iff.mpr ⟨ by positivity, by cases k <;> norm_num at * ; nlinarith ⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.20

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-
## The Upper Bound Construction

Erdős's upper bound uses probabilistic method.
-/

/-- Random sign functions have max discrepancy O(n^(3/2)). -/
axiom random_upper (n : ℕ) (hn : n ≥ 1) :
  ∃ f : SignFunction n, isValidSign f ∧
    (maxDiscrepancy f : ℝ) ≤ 10 * (n : ℝ) ^ (3/2 : ℝ)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  HPow ℝ ℝ ?m.21

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-
## The Lower Bound Technique

Erdős-Spencer used entropy or counting arguments.
-/

/-- Any sign function has some subset with large discrepancy. -/
theorem large_discrepancy_exists (f : SignFunction n) (hf : isValidSign f) (hn : n ≥ 10) :
    ∃ X : Finset (Fin n), (discrepancy f X : ℝ) ≥ (n : ℝ) ^ (3/2 : ℝ) / 100 := by
  sorry

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/-
## Special Cases

Small cases and explicit computations.
-/

/-- H(2) = 2 (trivial case). -/
theorem H_two : H 2 = 2 := by
  sorry

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/-- H(3) = 4. -/
theorem H_three : H 3 = 4 := by
  sorry

/-
## Connection to Ramsey Theory

The problem connects to Ramsey-type questions.
-/

/-- Large homogeneous subsets have small discrepancy. -/
theorem homogeneous_small_discrepancy (f : SignFunction n) (X : Finset (Fin n))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x y = 1) :
    discrepancy f X = X.card * (X.card - 1) := by
  unfold Erdos1028.discrepancy;
  -- Since all pairs in X have the same sign, the sum of f(x,y) over X is simply the number of pairs in X.
  have h_sum : pairSum f X = X.sum (fun x => X.sum (fun y => if x ≠ y then 1 else 0)) := by
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by by_cases h : x = y <;> aesop;
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
  norm_cast

/-
## Summary

This file formalizes Erdős Problem #1028 on discrepancy of sign functions.

**Status**: SOLVED

**The Question**: Estimate H(n) = min_f max_X |∑_{x≠y∈X} f(x,y)|.

**The Answer**: H(n) = Θ(n^(3/2)).

**Key Results**:
- Erdős (1963): n/4 ≤ H(n) ≪ n^(3/2)
- Erdős-Spencer (1971): H(n) ≫ n^(3/2)

**Related Topics**:
- Discrepancy theory
- Signed graphs
- Ramsey theory
- Probabilistic method
-/

end Erdos1028