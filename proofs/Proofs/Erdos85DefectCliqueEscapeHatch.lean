import Proofs.Erdos85RepairSet

/-!
# The defect-clique escape hatch

A pairwise no-common-neighbor set of size `d - 1` ("defect clique") that
avoids the closed neighborhood of some vertex `u` and sends no edge into
`N(u)` licenses the delete-one/add-pair surgery: delete `u`, attach one
new vertex to the manufactured clique `N(u)` and a second new vertex to
the defect clique.  The result is a `C4`-free graph one vertex larger
with the same minimum-degree threshold.

Contrapositive: a maximal configuration (no witness one vertex up) can
contain such a defect clique only entangled with every vertex's
neighborhood — for excess `e = d - 4`, where `(d-2)`-regularity of the
defect graph makes `K_{d-1}` defect components conceivable, this is a
distance-three rigidity constraint.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The escape hatch.**  A defect clique of size at least `d - 1`
avoiding `u` and its neighborhood, with no edges into that neighborhood,
upgrades an `(n+1)`-vertex `C4`-free min-degree-`d` graph to a witness
on `n + 2` vertices. -/
theorem c4FreeMinDegreeWitness_of_defectClique_anticomplete
    (G : SimpleGraph V) [DecidableRel G.Adj] {n d : ℕ}
    (hcard : Fintype.card V = n + 1) (hd : 1 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (C : Finset V) (hCcard : d - 1 ≤ C.card)
    (hCsafe : ∀ ⦃a⦄, a ∈ C → ∀ ⦃b⦄, b ∈ C → a ≠ b →
      (G.neighborFinset a ∩ G.neighborFinset b).card = 0)
    (u : V) (huC : u ∉ C)
    (hCN : ∀ ⦃c⦄, c ∈ C → ¬ G.Adj u c)
    (hcross : ∀ ⦃a⦄, a ∈ C → ∀ ⦃b : V⦄, G.Adj b u → ¬ G.Adj a b) :
    C4FreeMinDegreeWitness (n + 2) d := by
  classical
  set R : Finset {y : V // y ≠ u} :=
    C.subtype (fun y ↦ y ≠ u) with hR
  have hmemR : ∀ a : {y : V // y ≠ u}, a ∈ R ↔ a.1 ∈ C := by
    intro a
    simp [hR, Finset.mem_subtype]
  have hRcard : d - 1 ≤ R.card := by
    have hsub : R.card = (C.filter (fun y ↦ y ≠ u)).card := by
      rw [hR, Finset.card_subtype]
    have hfilter : C.filter (fun y ↦ y ≠ u) = C := by
      apply Finset.filter_true_of_mem
      intro c hc
      exact fun hcu ↦ huC (hcu ▸ hc)
    rw [hsub, hfilter]
    exact hCcard
  apply c4FreeMinDegreeWitness_delete_add_pair_of_repairSet G u hcard hd
    hmin hfree R hRcard
  · intro a ha b hb hab
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
    have hzab : G.Adj a.1 z.1 ∧ G.Adj b.1 z.1 := by
      constructor
      · exact hz.1
      · exact hz.2
    have hone := hCsafe ((hmemR a).mp ha) ((hmemR b).mp hb)
      (fun h ↦ hab (Subtype.ext h))
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hone
    exact hone z.1 (by
      rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
      exact hzab)
  · have hempty : R ∩ deletedNeighborhood G u = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      rw [Finset.mem_inter, mem_deletedNeighborhood] at ha
      exact hCN ((hmemR a).mp ha.1) (ha.2.symm)
    rw [hempty]
    simp
  · intro a ha b hb hadj
    rw [mem_deletedNeighborhood] at hb
    have hGadj : G.Adj a.1 b.1 := hadj
    exact hcross ((hmemR a).mp ha) hb hGadj

/-- **Distance-three rigidity under maximality.**  If no `C4`-free
min-degree-`d` witness exists one vertex up, then every defect clique of
size `d - 1` is entangled with every vertex's neighborhood: it meets
`{u} ∪ N(u)` or sends a `G`-edge into `N(u)`. -/
theorem defectClique_entangled_of_no_witness
    (G : SimpleGraph V) [DecidableRel G.Adj] {n d : ℕ}
    (hcard : Fintype.card V = n + 1) (hd : 1 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hnext : ¬ C4FreeMinDegreeWitness (n + 2) d)
    (C : Finset V) (hCcard : d - 1 ≤ C.card)
    (hCsafe : ∀ ⦃a⦄, a ∈ C → ∀ ⦃b⦄, b ∈ C → a ≠ b →
      (G.neighborFinset a ∩ G.neighborFinset b).card = 0)
    (u : V) :
    u ∈ C ∨ (∃ c ∈ C, G.Adj u c) ∨
      (∃ a ∈ C, ∃ b : V, G.Adj b u ∧ G.Adj a b) := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨huC, hCN, hcross⟩ := hnone
  exact hnext (c4FreeMinDegreeWitness_of_defectClique_anticomplete
    G hcard hd hmin hfree C hCcard hCsafe u huC
    (fun c hc ↦ hCN c hc)
    (fun a ha b hb hab ↦ hcross a ha b hb hab))

end

end Erdos85
