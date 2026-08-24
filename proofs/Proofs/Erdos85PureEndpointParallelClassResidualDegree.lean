import Proofs.Erdos85PureEndpointParallelClassDefectBoundary
import Proofs.Erdos85PureEndpointShoreCoordinateBijection

/-!
# Residual defect degree outside a forced parallel class

The owner label is a genuine coordinate on the shore.  We first record its
injectivity; this is the rigidity needed to see that a pair outside a perfect
matching crosses two distinct matching blocks.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint, two shore points with the same full-center owner
set are equal. -/
theorem c4Free_binarySquare_pureEndpoint_shore_owner_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    Set.InjOn (fun z => G.neighborFinset z ∩ fullLineCenters G S q) S := by
  classical
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let coord : Sum C I → Finset V :=
    Sum.elim (fun i => {i.1}) (fun e => e.1)
  obtain ⟨ψ, hψBij, hcoord⟩ :=
    c4Free_binarySquare_pureEndpoint_shore_coordinate_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hcoordInj : Function.Injective coord := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact singleton_inj.mp (by simpa [coord, C] using hab)
      | inr e =>
        exfalso
        have heCard : e.1.card = 2 := (mem_powersetCard.mp e.2).2
        have hc := congrArg Finset.card hab
        simp [coord, C, I, heCard] at hc
    | inr e =>
      cases b with
      | inl i =>
        exfalso
        have heCard : e.1.card = 2 := (mem_powersetCard.mp e.2).2
        have hc := congrArg Finset.card hab
        simp [coord, C, I, heCard] at hc
      | inr f =>
        apply congrArg Sum.inr
        apply Subtype.ext
        simpa [coord, I] using hab
  intro x hxS y hyS hxy
  obtain ⟨a, ha⟩ := hψBij.2 ⟨x, hxS⟩
  obtain ⟨b, hb⟩ := hψBij.2 ⟨y, hyS⟩
  have habCoord : coord a = coord b := by
    change Sum.elim (fun i : C => {i.1}) (fun e : I => e.1) a =
      Sum.elim (fun i : C => {i.1}) (fun e : I => e.1) b
    rw [← hcoord a, ← hcoord b, ha, hb]
    exact hxy
  have hab : a = b := hcoordInj habCoord
  have hψ : ψ a = ψ b := congrArg ψ hab
  rw [ha, hb] at hψ
  exact congrArg Subtype.val hψ

/-- If `A` and an excluded set `E` are disjoint subsets of `B`, then `A`
has at most the size of the complement of `E` in `B`. -/
theorem card_le_card_sub_of_disjoint_subsets
    {α : Type*} [DecidableEq α] (A B E : Finset α)
    (hAB : A ⊆ B) (hEB : E ⊆ B) (hAE : Disjoint A E) :
    A.card ≤ B.card - E.card := by
  have hUnion : A ∪ E ⊆ B := union_subset hAB hEB
  have hcard := card_le_card hUnion
  rw [card_union_of_disjoint hAE] at hcard
  omega

/-- A perfect-matching exterior row forces residual defect degree outside the
row.  A singleton-owner point has at least `m` such neighbors; a pair-owner
point outside the row has at least one. -/
theorem c4Free_binarySquare_pureEndpoint_exists_parallelClass_residualDegree
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
    ∃ w ∉ F,
      let B := G.neighborFinset w ∩ S
      B.card = m ∧
      ∀ x ∈ S \ B,
        ((owner x).card = 1 →
          m ≤ ((secondOrderDefectGraph G).neighborFinset x ∩ (S \ B)).card) ∧
        ((owner x).card = 2 →
          1 ≤ ((secondOrderDefectGraph G).neighborFinset x ∩ (S \ B)).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let D := secondOrderDefectGraph G
  obtain ⟨w, hwF, hBcard, _hKzero, hpair, hcover, hownerTwo⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_exterior_parallelClass
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  have hownerInj : Set.InjOn owner S := by
    simpa [owner, F] using
      c4Free_binarySquare_pureEndpoint_shore_owner_injective
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hDdisj : ∀ {x y}, D.Adj x y → Disjoint (owner x) (owner y) := by
    intro x y hxy
    simpa [D, owner, F, exceptionalOwnerSet] using
      (c4Free_binarySquare_pureEndpoint_ownerLabel_disjointness_profile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2 hxy
  have hDprofile := c4Free_binarySquare_pureEndpoint_defect_biregular_decomposition
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hm : 4 ≤ m := by omega
  refine ⟨w, hwF, hBcard, ?_⟩
  intro x hxOut
  have hxS : x ∈ S := (mem_sdiff.mp hxOut).1
  have hxNotB : x ∉ B := (mem_sdiff.mp hxOut).2
  have hsplit : D.neighborFinset x ∩ S =
      (D.neighborFinset x ∩ B) ∪ (D.neighborFinset x ∩ (S \ B)) := by
    ext z
    have hBsub : B ⊆ S := inter_subset_right
    simp only [mem_inter, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hzD, hzS⟩
      by_cases hzB : z ∈ B
      · exact Or.inl ⟨hzD, hzB⟩
      · exact Or.inr ⟨hzD, hzS, hzB⟩
    · rintro (⟨hzD, hzB⟩ | ⟨hzD, hzS, _hzNotB⟩)
      · exact ⟨hzD, hBsub hzB⟩
      · exact ⟨hzD, hzS⟩
  have hsplitDisj : Disjoint (D.neighborFinset x ∩ B)
      (D.neighborFinset x ∩ (S \ B)) := by
    rw [Finset.disjoint_left]
    intro z hzB hzOut
    exact (mem_sdiff.mp (mem_inter.mp hzOut).2).2 (mem_inter.mp hzB).2
  have hcardSplit : (D.neighborFinset x ∩ S).card =
      (D.neighborFinset x ∩ B).card +
        (D.neighborFinset x ∩ (S \ B)).card := by
    rw [hsplit, card_union_of_disjoint hsplitDisj]
  constructor
  · intro hxOne
    change m ≤ (D.neighborFinset x ∩ (S \ B)).card
    obtain ⟨i, hiOwner⟩ := card_eq_one.mp hxOne
    have hOwnerSingle : owner x = {i} := by
      simpa [owner, F] using hiOwner
    have hiMem : i ∈ owner x := by simp [hOwnerSingle]
    have hiF : i ∈ F := (mem_inter.mp hiMem).2
    have hiUnion : i ∈ B.biUnion owner := by simpa [B, owner, F, hcover] using hiF
    obtain ⟨y, hyB, hiy⟩ := mem_biUnion.mp hiUnion
    have hyExcluded : y ∉ D.neighborFinset x := by
      intro hyD
      have hd := hDdisj ((D.mem_neighborFinset x y).mp hyD)
      exact (Finset.disjoint_left.mp hd hiMem hiy)
    have hbound : (D.neighborFinset x ∩ B).card ≤ m - 1 := by
      have hle := card_le_card_sub_of_disjoint_subsets
        (D.neighborFinset x ∩ B) B {y}
        inter_subset_right (by simpa using hyB) (by
          rw [Finset.disjoint_left]
          intro z hzA hzY
          have hzy : z = y := by simpa using hzY
          subst z
          exact hyExcluded (mem_inter.mp hzA).1)
      have hBc : B.card = m := by simpa [B] using hBcard
      rw [hBc] at hle
      simpa using hle
    have htotal : (D.neighborFinset x ∩ S).card = q - 1 := by
      simpa [D] using (hDprofile x).1 hxOne
    have hsum : (D.neighborFinset x ∩ B).card +
        (D.neighborFinset x ∩ (S \ B)).card = q - 1 :=
      hcardSplit.symm.trans htotal
    omega
  · intro hxTwo
    change 1 ≤ (D.neighborFinset x ∩ (S \ B)).card
    obtain ⟨i, j, hij, hijOwner⟩ := card_eq_two.mp hxTwo
    have hOwnerPair : owner x = {i, j} := by
      simpa [owner, F] using hijOwner
    have hiMem : i ∈ owner x := by simp [hOwnerPair]
    have hjMem : j ∈ owner x := by simp [hOwnerPair]
    have hiUnion : i ∈ B.biUnion owner := by
      rw [hcover]
      exact (mem_inter.mp hiMem).2
    have hjUnion : j ∈ B.biUnion owner := by
      rw [hcover]
      exact (mem_inter.mp hjMem).2
    obtain ⟨yi, hyiB, hii⟩ := mem_biUnion.mp hiUnion
    obtain ⟨yj, hyjB, hjj⟩ := mem_biUnion.mp hjUnion
    have hyij : yi ≠ yj := by
      intro heq
      subst yj
      have hsub : owner x ⊆ owner yi := by
        rw [hOwnerPair]
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hii
        · exact hjj
      have hyCard : (owner yi).card = 2 := by
        exact hownerTwo yi (by simpa [B] using hyiB)
      have hxOwnerCard : (owner x).card = 2 := by
        simpa [owner, F] using hxTwo
      have hOwnerEq : owner x = owner yi :=
        eq_of_subset_of_card_le hsub (by
          change (owner yi).card ≤ (owner x).card
          rw [hyCard, hxOwnerCard])
      have hxy : x = yi := hownerInj hxS (mem_inter.mp hyiB).2 hOwnerEq
      exact hxNotB (hxy ▸ hyiB)
    have hiExcluded : yi ∉ D.neighborFinset x := by
      intro hiD
      exact Finset.disjoint_left.mp
        (hDdisj ((D.mem_neighborFinset x yi).mp hiD)) hiMem hii
    have hjExcluded : yj ∉ D.neighborFinset x := by
      intro hjD
      exact Finset.disjoint_left.mp
        (hDdisj ((D.mem_neighborFinset x yj).mp hjD)) hjMem hjj
    have hbound : (D.neighborFinset x ∩ B).card ≤ m - 2 := by
      have hle := card_le_card_sub_of_disjoint_subsets
        (D.neighborFinset x ∩ B) B {yi, yj}
        inter_subset_right (by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hyiB
          · exact hyjB) (by
          rw [Finset.disjoint_left]
          intro z hzA hzPair
          simp only [mem_insert, mem_singleton] at hzPair
          rcases hzPair with rfl | rfl
          · exact hiExcluded (mem_inter.mp hzA).1
          · exact hjExcluded (mem_inter.mp hzA).1)
      have hBc : B.card = m := by simpa [B] using hBcard
      rw [hBc, card_pair hyij] at hle
      exact hle
    have htotal : (D.neighborFinset x ∩ S).card = m - 1 := by
      simpa [D] using (hDprofile x).2.1 hxTwo
    have hsum : (D.neighborFinset x ∩ B).card +
        (D.neighborFinset x ∩ (S \ B)).card = m - 1 :=
      hcardSplit.symm.trans htotal
    omega

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_shore_owner_injective
#print axioms Erdos85.card_le_card_sub_of_disjoint_subsets
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_parallelClass_residualDegree
