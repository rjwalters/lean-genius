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

/-- Remaining vertices that are anticomplete to the deleted vertex's old
neighborhood.  Every member of a repair set must lie in this reservoir. -/
def repairCandidates {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset {y : V // y ≠ x} :=
  Finset.univ.filter fun a =>
    ∀ b ∈ deletedNeighborhood G x,
      ¬ (G.induce {y | y ≠ x}).Adj a b

/-- Candidate vertices outside the deleted vertex's old neighborhood.  These
are precisely the surviving nonneighbors with no edge into that neighborhood. -/
def externalRepairCandidates {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset {y : V // y ≠ x} :=
  repairCandidates G x \ deletedNeighborhood G x

@[simp] theorem mem_repairCandidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (a : {y : V // y ≠ x}) :
    a ∈ repairCandidates G x ↔
      ∀ b ∈ deletedNeighborhood G x,
        ¬ (G.induce {y | y ≠ x}).Adj a b := by
  simp [repairCandidates]

@[simp] theorem mem_externalRepairCandidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (a : {y : V // y ≠ x}) :
    a ∈ externalRepairCandidates G x ↔
      ¬ G.Adj a x ∧ ∀ b : {y : V // y ≠ x},
        G.Adj b x → ¬ G.Adj a b := by
  rw [externalRepairCandidates, Finset.mem_sdiff,
    mem_repairCandidates, mem_deletedNeighborhood]
  constructor
  · rintro ⟨hcandidate, houtside⟩
    exact ⟨houtside, fun b hb =>
      hcandidate b ((mem_deletedNeighborhood G x b).mpr hb)⟩
  · rintro ⟨houtside, hcandidate⟩
    exact ⟨fun b hb =>
      hcandidate b ((mem_deletedNeighborhood G x b).mp hb), houtside⟩

/-- The cross-anticompleteness clause is exactly containment in the candidate
reservoir. -/
theorem subset_repairCandidates_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (R : Finset {y : V // y ≠ x}) :
    R ⊆ repairCandidates G x ↔
      ∀ ⦃a⦄, a ∈ R → ∀ ⦃b⦄, b ∈ deletedNeighborhood G x →
        ¬ (G.induce {y | y ≠ x}).Adj a b := by
  constructor
  · intro hR a ha b hb
    exact (mem_repairCandidates G x a).mp (hR ha) b hb
  · intro hcross a ha
    exact (mem_repairCandidates G x a).mpr (fun b hb => hcross ha hb)

/-- Candidate-reservoir form of `HasRepairSet`. -/
theorem hasRepairSet_iff_exists_subset_candidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    HasRepairSet G d ↔
      ∃ (x : V) (R : Finset {y : V // y ≠ x}),
        d - 1 ≤ R.card ∧
        CommonNeighborIndependent (G.induce {y | y ≠ x}) R ∧
        (R ∩ deletedNeighborhood G x).card ≤ 1 ∧
        R ⊆ repairCandidates G x := by
  simp only [HasRepairSet]
  apply exists_congr
  intro x
  apply exists_congr
  intro R
  rw [subset_repairCandidates_iff]

/-- A necessary cardinal obstruction for the canonical repair surgery. -/
theorem exists_card_repairCandidates_of_hasRepairSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hrepair : HasRepairSet G d) :
    ∃ x : V, d - 1 ≤ (repairCandidates G x).card := by
  rw [hasRepairSet_iff_exists_subset_candidates] at hrepair
  obtain ⟨x, R, hRcard, _, _, hsub⟩ := hrepair
  exact ⟨x, hRcard.trans (Finset.card_le_card hsub)⟩

/-- Since a repair set uses at most one old neighbor, it requires at least
`d-2` external candidates. -/
theorem exists_card_externalRepairCandidates_of_hasRepairSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hrepair : HasRepairSet G d) :
    ∃ x : V, d - 2 ≤ (externalRepairCandidates G x).card := by
  rw [hasRepairSet_iff_exists_subset_candidates] at hrepair
  obtain ⟨x, R, hRcard, _, hinter, hsub⟩ := hrepair
  have hdiffSub : R \ deletedNeighborhood G x ⊆
      externalRepairCandidates G x := by
    intro a ha
    exact Finset.mem_sdiff.mpr
      ⟨hsub (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp ha).2⟩
  have hpartition := Finset.card_sdiff_add_card_inter R (deletedNeighborhood G x)
  have hdiffCard := Finset.card_le_card hdiffSub
  exact ⟨x, by omega⟩

/-- If every candidate reservoir is too small, no canonical repair set exists. -/
theorem not_hasRepairSet_of_card_repairCandidates_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hsmall : ∀ x : V, (repairCandidates G x).card < d - 1) :
    ¬ HasRepairSet G d := by
  intro hrepair
  obtain ⟨x, hx⟩ := exists_card_repairCandidates_of_hasRepairSet G hrepair
  exact (not_lt_of_ge hx) (hsmall x)

/-- External-reservoir obstruction, often sharper to check in concrete graphs. -/
theorem not_hasRepairSet_of_card_externalRepairCandidates_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hsmall : ∀ x : V, (externalRepairCandidates G x).card < d - 2) :
    ¬ HasRepairSet G d := by
  intro hrepair
  obtain ⟨x, hx⟩ := exists_card_externalRepairCandidates_of_hasRepairSet G hrepair
  exact (not_lt_of_ge hx) (hsmall x)

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
