import Proofs.Erdos85PureEndpointHalfOccupancyCoordinateNormalForm

/-!
# The residual-center block quotient

A finite pairwise-disjoint partition canonically sends each ground element to
its unique block.  At the pure endpoint this turns the residual full centers
into a quotient by the half-occupancy shore row, with fibers of size one or
two.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The block map of a finite pairwise-disjoint partition, including an exact
fiber-cardinality statement. -/
theorem exists_surjective_blockMap_of_pairwiseDisjoint_biUnion_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (ground : Finset β) (f : α → Finset β)
    (hpair : (((s : Finset α) : Set α).PairwiseDisjoint f))
    (hcover : s.biUnion f = ground)
    (hnonempty : ∀ y ∈ s, (f y).Nonempty) :
    ∃ π : {i : β // i ∈ ground} → {y : α // y ∈ s},
      Function.Surjective π ∧
      (∀ i y, π i = y ↔ i.1 ∈ f y.1) ∧
      ∀ y, ((univ : Finset {i : β // i ∈ ground}).filter fun i =>
        π i = y).card = (f y.1).card := by
  classical
  have huniq : ∀ i : {i : β // i ∈ ground},
      ∃! y : {y : α // y ∈ s}, i.1 ∈ f y.1 := by
    intro i
    have hiUnion : i.1 ∈ s.biUnion f := by simpa [hcover] using i.2
    obtain ⟨y, hyS, hiy⟩ := mem_biUnion.mp hiUnion
    refine ⟨⟨y, hyS⟩, hiy, ?_⟩
    intro z hiz
    apply Subtype.ext
    by_contra hyz
    exact (Finset.disjoint_left.mp
      (hpair hyS z.2 (fun h => hyz h.symm)) hiy hiz).elim
  let π : {i : β // i ∈ ground} → {y : α // y ∈ s} :=
    fun i => (huniq i).choose
  have hπ : ∀ i y, π i = y ↔ i.1 ∈ f y.1 := by
    intro i y
    constructor
    · intro h
      rw [← h]
      exact (huniq i).choose_spec.1
    · intro h
      exact (huniq i).unique (huniq i).choose_spec.1 h
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨i, hi⟩ := hnonempty y.1 y.2
    have hiGround : i ∈ ground := by
      rw [← hcover]
      exact mem_biUnion.mpr ⟨y.1, y.2, hi⟩
    let ii : {i : β // i ∈ ground} := ⟨i, hiGround⟩
    exact ⟨ii, (hπ ii y).mpr hi⟩
  refine ⟨π, hsurj, hπ, ?_⟩
  intro y
  let fiber := (univ : Finset {i : β // i ∈ ground}).filter fun i => π i = y
  have himage : fiber.image (fun i => i.1) = f y.1 := by
    ext i
    constructor
    · intro hi
      obtain ⟨ii, hii, rfl⟩ := mem_image.mp hi
      exact (hπ ii y).mp (mem_filter.mp hii).2
    · intro hi
      have hiGround : i ∈ ground := by
        rw [← hcover]
        exact mem_biUnion.mpr ⟨y.1, y.2, hi⟩
      let ii : {i : β // i ∈ ground} := ⟨i, hiGround⟩
      apply mem_image.mpr
      refine ⟨ii, mem_filter.mpr ⟨mem_univ _, (hπ ii y).mpr hi⟩, rfl⟩
  calc
    fiber.card = (fiber.image fun i => i.1).card :=
      (card_image_of_injective _ Subtype.val_injective).symm
    _ = (f y.1).card := congrArg card himage

/-- The forced half-occupancy row is the quotient of the residual full
centers by owner blocks; every fiber has size one or two. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_blockQuotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let owner := fun y => G.neighborFinset y ∩ F
    ∃ w,
      let B := G.neighborFinset w ∩ S
      let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
      B.card = m ∧ 2 ≤ K.card ∧
      ∃ π : {i : V // i ∈ F \ K} → {y : V // y ∈ B},
        Function.Surjective π ∧
        (∀ i y, π i = y ↔ i.1 ∈ owner y.1) ∧
        ∀ y,
          (((univ : Finset {i : V // i ∈ F \ K}).filter fun i =>
            π i = y).card = (owner y.1).card) ∧
          ((owner y.1).card = 1 ∨ (owner y.1).card = 2) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  obtain ⟨w, hBcard, hPtwo, hKcard, _hQplusK, hpair,
      hcover, _hunique, _hQpair, _hQsize, _hQcover⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_coordinateNormalForm
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
  have hKtwo : 2 ≤ K.card := by
    change 2 ≤ ((secondOrderDefectGraph G).neighborFinset w ∩
      fullLineCenters G S q).card
    rw [hKcard]
    exact hPtwo
  have hprofile :=
    (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
  have hnonempty : ∀ y ∈ B, (owner y).Nonempty := by
    intro y hy
    have hyS := (mem_inter.mp hy).2
    rcases (hprofile y).mp hyS with h | h
    · apply card_pos.mp
      change 0 < (G.neighborFinset y ∩ fullLineCenters G S q).card
      omega
    · apply card_pos.mp
      change 0 < (G.neighborFinset y ∩ fullLineCenters G S q).card
      omega
  obtain ⟨π, hπSurj, hπ, hfiber⟩ :=
    exists_surjective_blockMap_of_pairwiseDisjoint_biUnion_eq
      B (F \ K) owner hpair hcover hnonempty
  refine ⟨w, hBcard, hKtwo, π, hπSurj, hπ, ?_⟩
  intro y
  refine ⟨hfiber y, ?_⟩
  exact (hprofile y.1).mp (mem_inter.mp y.2).2

end

end Erdos85

#print axioms Erdos85.exists_surjective_blockMap_of_pairwiseDisjoint_biUnion_eq
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_blockQuotient
