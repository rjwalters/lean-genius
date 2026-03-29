/-
  Aristotle targets for Erdos Problem #362 (Subset Sum Concentration)
  Routine supporting lemmas for automated proof search.
  See Erdos362Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjectures (S-S bound, Halasz bound, Stanley extremal)
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axiom declarations
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Erdos362Aristotle

open Finset BigOperators

/-- The sum of elements in a finite set. -/
def setSum (A : Finset ℤ) : ℤ := ∑ x ∈ A, x

/-- Count of subsets summing to target t. -/
def countSubsetsWithSum (A : Finset ℤ) (t : ℤ) : ℕ :=
  (A.powerset.filter (fun S => setSum S = t)).card

/-- The generating function for subset sums.
    Uses zpow for correct integer exponentiation. -/
noncomputable def subsetSumGF (A : Finset ℤ) (z : ℂ) : ℂ :=
  ∏ a ∈ A, (1 + z ^ a)

-- TARGET 1: Trivial upper bound on subset sum count
theorem subset_count_le_pow (A : Finset ℤ) (t : ℤ) :
    countSubsetsWithSum A t ≤ 2 ^ A.card := by
  unfold countSubsetsWithSum
  calc (A.powerset.filter (fun S => setSum S = t)).card
      ≤ A.powerset.card := card_filter_le _ _
    _ = 2 ^ A.card := card_powerset A

-- TARGET 2: GF at z=1 equals 2^|A| (counts all subsets)
theorem gf_at_one (A : Finset ℤ) :
    subsetSumGF A 1 = (2 : ℂ) ^ A.card := by
  unfold subsetSumGF
  have h : ∀ a ∈ A, (1 : ℂ) + (1 : ℂ) ^ a = 2 := by
    intros a _; simp [one_zpow]
  rw [prod_congr rfl h, prod_const]

-- TARGET 3: zpow distributes over finset sum (for nonzero base)
theorem zpow_finset_sum (S : Finset ℤ) (z : ℂ) (hz : z ≠ 0) :
    ∏ a ∈ S, z ^ a = z ^ (∑ a ∈ S, a) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [prod_cons, sum_cons, zpow_add₀ hz, ih]

-- TARGET 4: GF factors over disjoint union
theorem gf_disjoint_union (B C : Finset ℤ) (z : ℂ) (h : Disjoint B C) :
    subsetSumGF (B ∪ C) z = subsetSumGF B z * subsetSumGF C z := by
  unfold subsetSumGF
  exact prod_union h

-- TARGET 5: Product expansion of GF as sum over powerset
theorem gf_expansion (A : Finset ℤ) (z : ℂ) (hz : z ≠ 0) :
    subsetSumGF A z = ∑ S ∈ A.powerset, z ^ (setSum S) := by sorry

end Erdos362Aristotle
