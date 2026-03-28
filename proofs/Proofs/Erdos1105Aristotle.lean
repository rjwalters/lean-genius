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
  Target 1: Number of strict order pairs equals binomial coefficient.
  |{(i,j) : Fin n × Fin n | i < j}| = C(n,2)

  Proof strategy (for human reference):
  - Partition Fin n × Fin n into {i < j}, {i = j}, {i > j}
  - |{i = j}| = n (diagonal), |{i < j}| = |{i > j}| (swap bijection)
  - n² = 2*|{i < j}| + n, hence |{i < j}| = n(n-1)/2 = C(n,2)

  Alternative strategy:
  - Group by second coordinate: |{(i,j) | i < j}| = Σ_j |{i | i < j}| = Σ_j j = 0+1+...+(n-1)
  - Apply Gauss sum formula
-/
theorem card_strict_pairs_eq (n : ℕ) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2)).card = n.choose 2 := by
  sorry

/-
  Target 2: Diagonal pairs count equals n.
  |{(i,j) : Fin n × Fin n | i = j}| = n
-/
theorem card_diag_pairs_eq (n : ℕ) :
    (Finset.univ.filter (fun e : Fin n × Fin n => e.1 = e.2)).card = n := by
  -- Bijection with Fin n: i ↦ (i, i)
  convert Fintype.card_fin n using 1
  rw [← Finset.card_univ (α := Fin n)]
  apply Finset.card_nbij (fun i _ => (i, i))
  · intro i _; simp
  · intro i _ j _ h; exact Prod.mk.inj h |>.1
  · intro ⟨i, j⟩ h; simp at h; exact ⟨i, Finset.mem_univ _, by rw [h]⟩

/-
  Target 3: Gauss sum for Fin values.
  Σ_{j : Fin n} j = C(n, 2)
-/
theorem sum_fin_val_eq_choose (n : ℕ) :
    ∑ j : Fin n, (j : ℕ) = n.choose 2 := by
  simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_id]
  rw [Nat.choose_two_right]

end Erdos1105Aristotle
