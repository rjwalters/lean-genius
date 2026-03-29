/-
  Aristotle targets for Erdős Problem #1105 (Anti-Ramsey Numbers)
  Routine supporting lemmas for automated proof search.
  See Erdos1105Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (combinatorial identities, cardinality)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

open Finset BigOperators Classical

namespace Erdos1105Aristotle

/-
PROBLEM
Target 1: Number of strict order pairs equals binomial coefficient.
  |{(i,j) : Fin n × Fin n | i < j}| = C(n,2)

  Proof strategy (for human reference):
  - Partition Fin n × Fin n into {i < j}, {i = j}, {i > j}
  - |{i = j}| = n (diagonal), |{i < j}| = |{i > j}| (swap bijection)
  - n² = 2*|{i < j}| + n, hence |{i < j}| = n(n-1)/2 = C(n,2)

  Alternative strategy:
  - Group by second coordinate: |{(i,j) | i < j}| = Σ_j |{i | i < j}| = Σ_j j = 0+1+...+(n-1)
  - Apply Gauss sum formula

PROVIDED SOLUTION
Use Finset.card_filter_lt_eq_choose to show this directly, or alternatively use the Gauss sum approach: biject filtered pairs to sum of range, then use sum_range_id and choose_two_right.
-/
theorem card_strict_pairs_eq (n : ℕ) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)).card = n.choose 2 := by
  erw [ Finset.card_filter ];
  erw [ Finset.sum_product ];
  simp +decide [ Nat.choose_two_right, Finset.filter_lt_eq_Ioi ];
  convert Finset.sum_range_id n using 1;
  rw [ ← Finset.sum_range_reflect, Finset.sum_range ]

/-
PROBLEM
Target 2: Diagonal pairs count equals n.
  |{(i,j) : Fin n × Fin n | i = j}| = n

PROVIDED SOLUTION
The diagonal {(i,i) | i : Fin n} bijects with Fin n. Use Finset.card_filter to reduce to showing the fiber has card n, or construct an explicit bijection via the embedding i ↦ (i,i).
-/
theorem card_diag_pairs_eq (n : ℕ) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 = e.2)).card = n := by
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun i : Fin n => ( i, i ) ) from fun i j hij => by simpa using hij ) using 1;
  any_goals exact Finset.univ;
  · congr with x ; aesop;
  · norm_num [ Finset.card_univ ]

/-
PROBLEM
Target 3: Gauss sum for Fin values.
  Σ_{j : Fin n} j = C(n, 2)

PROVIDED SOLUTION
Rewrite the sum over Fin n as sum over range n using Finset.sum_fin_eq_sum_range, simplify the coercion, then use Finset.sum_range_id_eq_sum_range_pred or similar, and finally Nat.choose_two_right to conclude.
-/
theorem sum_fin_val_eq_choose (n : ℕ) :
    ∑ j : Fin n, (j : ℕ) = n.choose 2 := by
  rw [ Nat.choose_two_right ];
  convert Finset.sum_range_id n using 1 ; rw [ Finset.sum_range ]

end Erdos1105Aristotle