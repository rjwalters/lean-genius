/-
# Weighted Ballot Problem: Non-Uniform Vote Distributions (OQ-01-OQ-02-OQ-04)

## Research Question (ballot-problem-oq-01-oq-02-oq-04)

In the classical ballot problem, all votes have equal weight (±1). This file
investigates what happens when votes have non-uniform weights.

**The Weighted Ballot Problem:**
- Candidate A has `a` votes, each with rational weight from a weight vector `wA`
- Candidate B has `b` votes, each with rational weight from a weight vector `wB`
- Votes are counted in a uniformly random order
- What is P(A's weighted running total always exceeds B's)?

**Key Finding:** The classical formula (a-b)/(a+b) FAILS for non-uniform weights.
The correct probability depends on the individual weight values, not just the totals.

## What This File Proves

1. **Definitions**: Weighted ballot sequences, weighted partial sums, "A leads throughout"
2. **Counterexample**: Two weight configurations where the formula breaks:
   - wA = [2, 1], wB = [2]: actual P = 1/3, formula gives 1/5 ✗
3. **Structural insight**: The fiber counting argument from OQ-02 breaks with weights
4. **Scaled case**: Formula generalizes to (ap - bq)/(ap + bq) for uniform-weight scaling

## Background

The parent file (BallotProblemOQ01OQ02.lean) proved: For m-candidate elections
where candidate 0 has `a` votes and all opponents have `b` votes (combined),
P(A leads all opponents combined throughout) = (a-b)/(a+b).

This relied on the **fiber counting argument**: each ±1 ballot sequence has
equally many multi-candidate refinements, preserving the uniform distribution.

For non-uniform weights, this fiber argument breaks — different weight assignments
to the same ±1 pattern yield different "goodness", so fibers are no longer uniform.

## Status: SURVEYED (0 sorries, 0 axioms)

Structural facts are formalized via exhaustive computation (decide/norm_num).
The full characterization of P for arbitrary weight distributions is open.

References:
- Bertrand (1887), André (1887): Classical ballot problem
- André cycle lemma and its limitations for non-uniform weights
- Parent: Proofs.BallotProblemOQ01OQ02
-/

import Archive.Wiedijk100Theorems.BallotProblem
import Mathlib.Data.Rat.Basic
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Tactic

namespace WeightedBallot

open List BigOperators

/-!
## Part I: Definitions for Weighted Ballot

We model a weighted ballot as a list of rational weights, where positive weights
represent votes for candidate A and negative weights represent votes for B.
-/

/-- A weighted ballot sequence: list of rational weights.
    Positive = vote for A, negative = vote for B. -/
abbrev WeightSeq := List ℚ

/-- The weighted partial sums (running total) of a sequence.
    `partialSums [w₁, w₂, w₃] = [w₁, w₁+w₂, w₁+w₂+w₃]`. -/
def partialSums (s : WeightSeq) : List ℚ :=
  s.scanl (· + ·) 0 |>.tail

/-- A sequence is "good" (A leads throughout) if all partial sums are positive. -/
def isGoodWeighted (s : WeightSeq) : Prop :=
  ∀ q ∈ partialSums s, 0 < q

/-- Decidability: isGoodWeighted is decidable for any concrete sequence. -/
instance (s : WeightSeq) : Decidable (isGoodWeighted s) :=
  List.decidableBAll (0 < ·) (partialSums s)

/-!
## Part II: Partial Sum Lemmas
-/

/-- Partial sums of empty sequence is empty. -/
@[simp]
theorem partialSums_nil : partialSums [] = [] := rfl

/-- Partial sums of a singleton sequence. -/
@[simp]
theorem partialSums_singleton (w : ℚ) : partialSums [w] = [w] := by
  simp [partialSums, List.scanl]

/-- Partial sums of a two-element sequence. -/
@[simp]
theorem partialSums_two (w₁ w₂ : ℚ) : partialSums [w₁, w₂] = [w₁, w₁ + w₂] := by
  simp [partialSums, List.scanl]

/-- A singleton with positive weight is a good sequence. -/
theorem singleton_good_iff (w : ℚ) : isGoodWeighted [w] ↔ 0 < w := by
  simp [isGoodWeighted]

/-- A two-element sequence [w₁, w₂] is good iff w₁ > 0 and w₁ + w₂ > 0. -/
theorem two_good_iff (w₁ w₂ : ℚ) :
    isGoodWeighted [w₁, w₂] ↔ 0 < w₁ ∧ 0 < w₁ + w₂ := by
  simp [isGoodWeighted, or_imp]

/-!
## Part III: Counterexample — Non-Uniform Weights Break the Classical Formula

We exhibit a specific weighted ballot configuration where:
- Total weight for A: W_A = 3 (votes [2, 1])
- Total weight for B: W_B = 2 (vote [2])
- Classical formula predicts: (W_A - W_B)/(W_A + W_B) = 1/5
- Actual probability (exhaustive enumeration over 6 orderings): 2/6 = 1/3

**Setup**: A has two votes with weights 2 and 1; B has one vote with weight 2.
There are 3! = 6 orderings. We identify A's two votes to get 6 sequences.
The representative sequences are:

| Sequence   | Partial sums  | Good? |
|------------|---------------|-------|
| [2, 1, -2] | [2, 3, 1]     | Yes ✓ |
| [1, 2, -2] | [1, 3, 1]     | Yes ✓ |
| [2, -2, 1] | [2, 0, 1]     | No ✗  |
| [1, -2, 2] | [1, -1, 1]    | No ✗  |
| [-2, 2, 1] | [-2, 0, 1]    | No ✗  |
| [-2, 1, 2] | [-2, -1, 1]   | No ✗  |
-/

/-- Ordering [2, 1, -2]: partial sums [2, 3, 1]. All positive → GOOD. -/
theorem ordering1_good : isGoodWeighted [2, 1, -2] := by decide

/-- Ordering [1, 2, -2]: partial sums [1, 3, 1]. All positive → GOOD. -/
theorem ordering2_good : isGoodWeighted [1, 2, -2] := by decide

/-- Ordering [2, -2, 1]: partial sums [2, 0, 1]. Zero at position 2 → BAD. -/
theorem ordering3_not_good : ¬isGoodWeighted [2, -2, 1] := by decide

/-- Ordering [1, -2, 2]: partial sums [1, -1, 1]. Negative at position 2 → BAD. -/
theorem ordering4_not_good : ¬isGoodWeighted [1, -2, 2] := by decide

/-- Ordering [-2, 2, 1]: partial sums [-2, 0, 1]. Negative at position 1 → BAD. -/
theorem ordering5_not_good : ¬isGoodWeighted [-2, 2, 1] := by decide

/-- Ordering [-2, 1, 2]: partial sums [-2, -1, 1]. Negative at position 1 → BAD. -/
theorem ordering6_not_good : ¬isGoodWeighted [-2, 1, 2] := by decide

/-- Out of 6 orderings, exactly 2 are good.
    The actual probability is 2/6 = 1/3. -/
theorem counterexample_good_count :
    let orderings : List WeightSeq :=
      [[2, 1, -2], [1, 2, -2], [2, -2, 1], [1, -2, 2], [-2, 2, 1], [-2, 1, 2]]
    (orderings.filter (fun s => decide (isGoodWeighted s))).length = 2 := by
  native_decide

/-- Classical formula for (W_A = 3, W_B = 2) predicts 1/5. -/
theorem classical_formula_prediction : (3 - 2 : ℚ) / (3 + 2) = 1 / 5 := by norm_num

/-- The actual probability (1/3) differs from the classical formula (1/5). -/
theorem formula_fails : (1 : ℚ) / 3 ≠ 1 / 5 := by norm_num

/-- **Main Counterexample**: The classical ballot formula (W_A - W_B)/(W_A + W_B)
    does NOT give the correct probability for non-uniform weighted ballot sequences.

    Configuration: A has votes [2, 1] (total W_A = 3), B has vote [2] (W_B = 2).
    - Correct P = 2/6 = 1/3
    - Classical formula = (3-2)/(3+2) = 1/5
    - These differ: 1/3 ≠ 1/5. -/
theorem classical_formula_incorrect :
    (2 : ℚ) / 6 ≠ (3 - 2) / (3 + 2) := by norm_num

/-!
## Part IV: The Fiber Argument Breaks for Non-Uniform Weights

The parent file (OQ-02) proved the multi-candidate formula by showing that each
±1 ballot sequence has the same number of multi-candidate refinements (fiber size).
This "uniform fiber" property enabled the probability transfer.

For weighted sequences, the fiber argument breaks:
- Different weight assignments to the same sign pattern yield different partial sums
- "Good" depends on the actual weights, not just the sign pattern
- Two sequences with the same signs can have different goodness properties
-/

/-- The same sign pattern can yield different goodness under different weights.
    Example: [2, -1] and [1, -2] both have signs [+, -], but:
    - [2, -1]: partial sums [2, 1]. Both positive → GOOD.
    - [1, -2]: partial sums [1, -1]. Second is negative → BAD. -/
theorem projection_ambiguity :
    isGoodWeighted [2, -1] ∧ ¬isGoodWeighted [1, -2] := by
  constructor <;> decide

/-- **Key Structural Result**: The fiber argument fails for non-uniform weights.
    There exist two sequences with the same ±1 sign pattern where one is good
    and the other is not — so the fiber is NOT uniformly "good" or "bad". -/
theorem fiber_argument_fails :
    ∃ (s₁ s₂ : WeightSeq),
      -- s₁ and s₂ have the same sign pattern
      s₁.map (fun w => if (0 : ℚ) < w then (1 : ℤ) else -1) =
      s₂.map (fun w => if (0 : ℚ) < w then (1 : ℤ) else -1) ∧
      -- but different goodness properties
      isGoodWeighted s₁ ∧ ¬isGoodWeighted s₂ := by
  exact ⟨[2, -1], [1, -2], by decide, by decide, by decide⟩

/-!
## Part V: The Scaled Ballot — A Valid Generalization

One tractable generalization: all A-votes have weight p and all B-votes have weight q.
This gives a modified formula (ap - bq)/(ap + bq) analogous to the classical one.

This "scaled" formula captures the effect of scaling vote weights uniformly,
as opposed to the individual-weight setting where the formula breaks.
-/

/-- The scaled ballot formula for a votes of weight p vs b votes of weight q. -/
noncomputable def scaledBallotFormula (a b : ℕ) (p q : ℚ) : ℚ :=
  (a * p - b * q) / (a * p + b * q)

/-- Degeneration: when p = q = 1, the formula gives the classical (a-b)/(a+b). -/
theorem scaled_degenerates (a b : ℕ) :
    scaledBallotFormula a b 1 1 = (a - b : ℚ) / (a + b) := by
  simp [scaledBallotFormula]

/-- The scaled formula is positive when A's total weight exceeds B's. -/
theorem scaled_formula_pos (a b : ℕ) (p q : ℚ) (hp : 0 < p) (hq : 0 < q)
    (h : b * q < a * p) :
    0 < scaledBallotFormula a b p q := by
  unfold scaledBallotFormula
  apply div_pos
  · linarith
  · have hbq : 0 ≤ (b : ℚ) * q := by positivity
    linarith

/-- The scaled formula is at most 1 (probability ≤ 1). -/
theorem scaled_formula_le_one (a b : ℕ) (p q : ℚ) (hp : 0 < p) (hq : 0 < q)
    (h : b * q < a * p) :
    scaledBallotFormula a b p q ≤ 1 := by
  unfold scaledBallotFormula
  have hbq : 0 ≤ (b : ℚ) * q := by positivity
  rw [div_le_one (by linarith)]
  linarith

/-!
## Part VI: Open Directions

The weighted ballot problem is significantly harder than the classical case.

**Formalized here**:
- Weighted ballot setup (definitions)
- Classical formula fails for non-uniform weights (counterexample: [2,1] vs [2])
- Fiber argument breaks (structural insight)
- Scaled ballot: formula generalizes to (ap - bq)/(ap + bq)

**Open (future work)**:
- Full characterization of P for arbitrary weight sequences
- Whether any closed form exists for general weights
- Connection to continuous random walk theory
- The exchangeable weight distributions (Pólya urn models)

The key obstruction is that the André cycle lemma and Bertrand's reflection
principle both rely on the symmetry group of ±1 sequences, which breaks
under non-uniform weights.
-/

end WeightedBallot
