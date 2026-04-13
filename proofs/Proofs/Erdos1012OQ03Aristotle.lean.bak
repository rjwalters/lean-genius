/-
  Aristotle targets for erdos-1012-oq-03 (Directed Hamiltonian Threshold)
  Routine supporting lemmas for automated proof search.
  See Erdos1012OQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjectures (ghouila_houri, directed_hamiltonian_threshold)
  - A known combinatorial counting result with a clear proof sketch

  Main target: perm_arc_bad_card_le — bound on permutations with a given consecutive pair

  Proof strategy:
  - For each position i ∈ Fin n (n choices), fix σ(i) = a, σ((i+1)%n) = b.
  - The n-2 remaining values can be placed freely: (n-2)! permutations each.
  - Positions are disjoint (σ injective → σ(i)=a uniquely determines i).
  - Total count ≤ n * (n-2)! by summing over all n positions.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

-- Key combinatorial bound: the number of permutations σ : Perm(Fin n) such that
-- a directed arc (a → b) appears at some consecutive position in the cycle given by σ
-- is at most n * (n-2)!.
-- Proof sketch: for each position i (n choices), fixing σ(i)=a, σ((i+1)%n)=b leaves
-- (n-2)! permutations of the remaining n-2 values. Positions are disjoint (σ injective).
theorem perm_arc_bad_card_le {n : ℕ} (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ i : Fin n, σ i = a ∧
        σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ = b)).card ≤
    n * (n - 2).factorial := by
  sorry
