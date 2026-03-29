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
import Mathlib

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
    intros a _; simp [one_zpow]; norm_num
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

/-
PROBLEM
TARGET 5: Product expansion of GF as sum over powerset

PROVIDED SOLUTION
By induction on A using Finset.cons_induction.

Base case (A = ∅): Both sides equal 1 (empty product = 1, only subset is ∅ with setSum = 0, z^0 = 1).

Inductive step (A = {a} ∪ S, a ∉ S):
subsetSumGF ({a} ∪ S) z = (1 + z^a) * subsetSumGF S z (by prod_cons)
= (1 + z^a) * ∑ T ∈ S.powerset, z^(setSum T)  (by IH)
= ∑ T ∈ S.powerset, z^(setSum T) + ∑ T ∈ S.powerset, z^a * z^(setSum T)

The RHS is ∑ T ∈ ({a} ∪ S).powerset, z^(setSum T). Use Finset.powerset_cons to split ({a} ∪ S).powerset into subsets not containing a (= S.powerset) and subsets containing a (= S.powerset.map (cons embedding)). The sum over the first part gives ∑ T ∈ S.powerset, z^(setSum T). The sum over the second part: for each T in S.powerset, the corresponding subset is {a} ∪ T with setSum = a + setSum T, so the sum is ∑ T ∈ S.powerset, z^(a + setSum T) = ∑ T, z^a * z^(setSum T). Combine using add_mul or mul_add.
-/
theorem gf_expansion (A : Finset ℤ) (z : ℂ) (hz : z ≠ 0) :
    subsetSumGF A z = ∑ S ∈ A.powerset, z ^ (setSum S) := by
  simp only [subsetSumGF, setSum]
  rw [Finset.prod_one_add]
  exact Finset.sum_congr rfl fun S _ => zpow_finset_sum S z hz

end Erdos362Aristotle