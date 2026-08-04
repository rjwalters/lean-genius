import Proofs.Erdos85DeletePair

/-!
# One-set repair after deleting a vertex

In the delete-one/add-an-adjacent-pair surgery, one attachment set can be fixed
canonically as the deleted vertex's old neighbourhood.  It is automatically
safe in the induced graph, has sufficient size, and covers every neighbour
which loses a degree.  Thus only one compatible repair set remains to be found.
-/

open SimpleGraph

namespace Erdos85

/-- The neighbourhood of a deleted vertex, represented inside the remaining
vertex subtype. -/
def deletedNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset {y : V // y ≠ x} :=
  Finset.univ.filter fun y => G.Adj y x

@[simp] theorem mem_deletedNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (y : {y : V // y ≠ x}) :
    y ∈ deletedNeighborhood G x ↔ G.Adj y x := by
  simp [deletedNeighborhood]

theorem card_deletedNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (deletedNeighborhood G x).card = G.degree x := by
  rw [degree]
  have hmap : (deletedNeighborhood G x).map ⟨Subtype.val, Subtype.val_injective⟩ =
      G.neighborFinset x := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      rw [SimpleGraph.mem_neighborFinset]
      exact (mem_deletedNeighborhood G x z).mp hz |>.symm
    · intro hy
      have hyx : y ≠ x := by
        exact (G.ne_of_adj ((G.mem_neighborFinset x y).mp hy)).symm
      rw [Finset.mem_map]
      refine ⟨⟨y, hyx⟩, ?_, rfl⟩
      exact (mem_deletedNeighborhood G x ⟨y, hyx⟩).mpr
        ((G.mem_neighborFinset x y).mp hy).symm
  rw [← hmap, Finset.card_map]

/-- A witness admits the canonical delete/add-pair repair at degree d. -/
def HasRepairSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∃ (x : V) (R : Finset {y : V // y ≠ x}),
    d - 1 ≤ R.card ∧
    CommonNeighborIndependent (G.induce {y | y ≠ x}) R ∧
    (R ∩ deletedNeighborhood G x).card ≤ 1 ∧
    ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ deletedNeighborhood G x →
      ¬ (G.induce {y | y ≠ x}).Adj a b

/-- The deleted vertex's old neighbourhood is automatically safe in the graph
induced on the remaining vertices. -/
theorem commonNeighborIndependent_deletedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (hfree : ¬ containsC4 V G) :
    CommonNeighborIndependent (G.induce {y | y ≠ x}) (deletedNeighborhood G x) := by
  intro a ha b hb hab
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at hz
  have haz : G.Adj a z := hz.1
  have hbz : G.Adj b z := hz.2
  have hax : G.Adj a x := (mem_deletedNeighborhood G x a).mp ha
  have hbx : G.Adj b x := (mem_deletedNeighborhood G x b).mp hb
  exact hfree (containsC4_of_rim (a := a) (b := z) (c := b) (d := x)
    haz hbz.symm hbx hax.symm
    (fun h => hab (Subtype.ext h))
    z.property
    (G.ne_of_adj haz).symm
    (G.ne_of_adj hbz.symm)
    (G.ne_of_adj hax.symm)
    (G.ne_of_adj hbx.symm))

/-- **One-set repair criterion.**  After deleting x, its old neighbourhood is
the canonical second attachment set.  To extend the witness by one vertex it
suffices to find just one set R of size d-1 which is safe, meets that
neighbourhood in at most one vertex, and has no edges to it. -/
theorem c4FreeMinDegreeWitness_delete_add_pair_of_repairSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {n d : ℕ}
    (hcard : Fintype.card V = n + 1) (hd : 1 ≤ d)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (R : Finset {y : V // y ≠ x})
    (hRcard : d - 1 ≤ R.card)
    (hRsafe : CommonNeighborIndependent (G.induce {y | y ≠ x}) R)
    (hinter : (R ∩ deletedNeighborhood G x).card ≤ 1)
    (hcross : ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ deletedNeighborhood G x →
      ¬ (G.induce {y | y ≠ x}).Adj a b) :
    C4FreeMinDegreeWitness (n + 2) d := by
  apply c4FreeMinDegreeWitness_delete_add_pair G x hcard hmin hfree
      R (deletedNeighborhood G x) hRcard
  · rw [card_deletedNeighborhood]
    have hxdeg := hmin.trans (G.minDegree_le_degree x)
    omega
  · exact hd
  · exact ⟨hRsafe, commonNeighborIndependent_deletedNeighborhood G x hfree,
      hinter, hcross⟩
  · intro y hyx _
    exact Finset.mem_union_right R
      ((mem_deletedNeighborhood G x y).mpr hyx)

/-- A uniform one-set repair choice extends every witness at order n. -/
theorem witnessExtension_of_repairSet {n : ℕ} (hn : 1 ≤ n)
    (hrepair : ∀ d (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      1 ≤ d → d ≤ G.minDegree → ¬ containsC4 (Fin n) G →
      ∃ (x : Fin n) (R : Finset {y : Fin n // y ≠ x}),
        d - 1 ≤ R.card ∧
        CommonNeighborIndependent (G.induce {y | y ≠ x}) R ∧
        (R ∩ deletedNeighborhood G x).card ≤ 1 ∧
        (∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ deletedNeighborhood G x →
          ¬ (G.induce {y | y ≠ x}).Adj a b)) :
    C4FreeWitnessExtension n := by
  rintro d ⟨G, hdec, hmin, hfree⟩
  letI : DecidableRel G.Adj := hdec
  by_cases hd0 : d = 0
  · subst d
    refine ⟨⊥, Classical.decRel _, Nat.zero_le _, ?_⟩
    rintro ⟨f, _, hadj⟩
    simpa using hadj 0 1 (by decide)
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    obtain ⟨x, R, hRcard, hRsafe, hinter, hcross⟩ :=
      hrepair d G hdec hd hmin hfree
    have hw := c4FreeMinDegreeWitness_delete_add_pair_of_repairSet
      G x (n := n - 1) (d := d) (by simp [Nat.sub_add_cancel hn]) hd hmin hfree R
      hRcard hRsafe hinter hcross
    convert hw using 1 <;> omega

end Erdos85
