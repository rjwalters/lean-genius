import Proofs.Erdos85Relabel

/-!
# Vertex deletion and one-sided variation of the Erdős 85 threshold

Deleting one vertex from a finite simple graph lowers the degree of every
remaining vertex by at most one.  Applied to a `C₄`-free extremal witness, this
shows that the threshold can increase by at most one when the order increases.

This argument is deliberately one-sided: deletion gives no lower bound on
`minDegreeForC4 (n + 1)` in terms of `minDegreeForC4 n`.
-/

open SimpleGraph

namespace Erdos85

/-- After deleting a vertex, every surviving degree is at least its old degree
minus one. -/
theorem degree_sub_one_le_induce_compl_singleton
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) (v : {y // y ≠ x}) :
    G.degree v - 1 ≤ (G.induce {y | y ≠ x}).degree v := by
  let T : Finset V := G.neighborFinset v
  have himage := G.map_neighborFinset_induce (s := {y | y ≠ x}) v
  have hinter : G.neighborFinset v ∩ {y | y ≠ x}.toFinset = T.erase x := by
    ext y
    simp [T, and_comm]
  have hcard : (G.induce {y | y ≠ x}).degree v = (T.erase x).card := by
    rw [degree, ← Finset.card_map]
    rw [himage, hinter]
  rw [hcard]
  change T.card - 1 ≤ (T.erase x).card
  by_cases hx : x ∈ T
  · rw [Finset.card_erase_of_mem hx]
  · rw [Finset.erase_eq_of_notMem hx]
    omega

/-- Deleting any vertex from a `C₄`-free minimum-degree witness loses at most
one unit of minimum degree. -/
theorem c4FreeMinDegreeWitness_delete_vertex {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) {n d : ℕ} (hcard : Fintype.card V = n + 1) (hn : 1 ≤ n)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G) :
    C4FreeMinDegreeWitness n (d - 1) := by
  let S := {y : V | y ≠ x}
  let H := G.induce S
  have hcardS : Fintype.card S = n := by
    change Fintype.card {y : V // y ≠ x} = n
    simp [hcard]
  letI : Nonempty S := Fintype.card_pos_iff.mp (hcardS.trans_gt (by omega))
  apply c4FreeMinDegreeWitness_of_card_eq H hcardS
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    exact (Nat.sub_le_sub_right (hmin.trans (G.minDegree_le_degree v)) 1).trans
      (degree_sub_one_le_induce_compl_singleton G x v)
  · intro hC4
    rcases hC4 with ⟨f, hf, hadj⟩
    exact hfree ⟨fun i ↦ f i, Subtype.val_injective.comp hf,
      fun i j hij ↦ hadj i j hij⟩

/-- The Erdős 85 threshold can increase by at most one in a single step. -/
theorem minDegreeForC4_succ_le_add_one {n : ℕ} (hn : 4 ≤ n) :
    minDegreeForC4 (n + 1) ≤ minDegreeForC4 n + 1 := by
  by_contra h
  have hlt : minDegreeForC4 n + 1 < minDegreeForC4 (n + 1) := Nat.lt_of_not_ge h
  have hw : C4FreeMinDegreeWitness (n + 1) (minDegreeForC4 n + 1) :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).2 hlt
  rcases hw with ⟨G, hdec, hmin, hfree⟩
  letI : DecidableRel G.Adj := hdec
  let x : Fin (n + 1) := ⟨0, by omega⟩
  have hw' := c4FreeMinDegreeWitness_delete_vertex G x (n := n)
    (d := minDegreeForC4 n + 1) (by simp) (by omega) hmin hfree
  have hbelow := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).1 hw'
  simp only [Nat.add_sub_cancel] at hbelow
  exact (Nat.lt_irrefl _) hbelow

end Erdos85
