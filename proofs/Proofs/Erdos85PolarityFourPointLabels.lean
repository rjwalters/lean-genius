import Proofs.Erdos85FiveSelectorPacking
import Proofs.Erdos85PolarityOddSecantCount

/-!
# Deleted-absolute labels for four-point polarity gadgets
-/

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable (K : Type u) [Field K] [Finite K] [DecidableEq K]

private noncomputable abbrev P := ℙ K (Fin 3 → K)

/-- The deleted absolute neighbours of a surviving point, represented in the
finite type of deleted centres. -/
noncomputable def deletedAbsoluteLabel (D : Finset (P K))
    (x : {v : P K // v ∉ D}) : Finset {a : P K // a ∈ D} := by
  classical
  exact Finset.univ.filter fun a => (graph K).Adj x.1 a.1

@[simp] theorem mem_deletedAbsoluteLabel (D : Finset (P K))
    (x : {v : P K // v ∉ D}) (a : {a : P K // a ∈ D}) :
    a ∈ deletedAbsoluteLabel K D x ↔ (graph K).Adj x.1 a.1 := by
  classical
  simp [deletedAbsoluteLabel]

theorem card_deletedAbsoluteLabel_eq (D : Finset (P K))
    (x : {v : P K // v ∉ D}) :
    (deletedAbsoluteLabel K D x).card =
      ((graph K).neighborFinset x.1 ∩ D).card := by
  classical
  apply Finset.card_bij (fun a _ => a.1)
  · intro a ha
    rw [Finset.mem_inter]
    exact ⟨by
      rw [SimpleGraph.mem_neighborFinset]
      exact (mem_deletedAbsoluteLabel K D x a).mp ha, a.2⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro y hy
    refine ⟨⟨y, (Finset.mem_inter.mp hy).2⟩, ?_, rfl⟩
    apply (mem_deletedAbsoluteLabel K D x _).mpr
    exact ((graph K).mem_neighborFinset x.1 y).mp (Finset.mem_inter.mp hy).1

/-- A nonabsolute survivor has at most two deleted-absolute labels. -/
theorem card_deletedAbsoluteLabel_le_two
    (h2 : (2 : K) ≠ 0) (D : Finset (P K))
    (hDabs : ∀ a ∈ D, Projectivization.orthogonal a a)
    (x : {v : P K // v ∉ D})
    (hxnon : ¬ Projectivization.orthogonal x.1 x.1) :
    (deletedAbsoluteLabel K D x).card ≤ 2 := by
  rw [card_deletedAbsoluteLabel_eq]
  exact card_neighborFinset_inter_le_two_of_subset_absolute
    K (absoluteTwoSecant_of_two_ne_zero K h2) D hDabs x.1 hxnon

/-- Two nonabsolute survivors with the same two deleted-absolute labels are
the same projective point. -/
theorem eq_of_deletedAbsoluteLabel_eq_of_card_two
    (D : Finset (P K))
    (hDabs : ∀ a ∈ D, Projectivization.orthogonal a a)
    (x y : {v : P K // v ∉ D})
    (hxnon : ¬ Projectivization.orthogonal x.1 x.1)
    (hynon : ¬ Projectivization.orthogonal y.1 y.1)
    (hxcard : (deletedAbsoluteLabel K D x).card = 2)
    (hxylabel : deletedAbsoluteLabel K D x =
      deletedAbsoluteLabel K D y) :
    x = y := by
  classical
  obtain ⟨a, b, hab, hlabel⟩ := Finset.card_eq_two.mp hxcard
  have hax : (graph K).Adj a.1 x.1 := by
    rw [← (graph K).adj_comm]
    apply (mem_deletedAbsoluteLabel K D x a).mp
    rw [hlabel]
    simp
  have hbx : (graph K).Adj b.1 x.1 := by
    rw [← (graph K).adj_comm]
    apply (mem_deletedAbsoluteLabel K D x b).mp
    rw [hlabel]
    simp
  have hay : (graph K).Adj a.1 y.1 := by
    rw [← (graph K).adj_comm]
    apply (mem_deletedAbsoluteLabel K D y a).mp
    rw [← hxylabel, hlabel]
    simp
  have hby : (graph K).Adj b.1 y.1 := by
    rw [← (graph K).adj_comm]
    apply (mem_deletedAbsoluteLabel K D y b).mp
    rw [← hxylabel, hlabel]
    simp
  have hu := existsUnique_nonabsolute_commonNeighbor_of_absolute K
    (hDabs a.1 a.2) (hDabs b.1 b.2)
    (fun h => hab (Subtype.ext h))
  apply Subtype.ext
  exact hu.unique ⟨hax, hbx, hxnon⟩ ⟨hay, hby, hynon⟩

/-- Distinct nonabsolute members of a safe selector in the graph obtained by
deleting `D` share a deleted label.  Their unique projective common point
would otherwise survive and violate common-neighbour independence. -/
theorem deletedAbsoluteLabel_inter_nonempty_of_safe
    (D : Finset (P K))
    (S : Finset {v : P K // v ∉ D})
    (hsafe : CommonNeighborIndependent (deleteVertexSetGraph (graph K) D) S)
    (x y : {v : P K // v ∉ D}) (hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : x ≠ y)
    (hxnon : ¬ Projectivization.orthogonal x.1 x.1)
    (hynon : ¬ Projectivization.orthogonal y.1 y.1) :
    (deletedAbsoluteLabel K D x ∩ deletedAbsoluteLabel K D y).Nonempty := by
  classical
  obtain ⟨z, hzx, hzy⟩ :=
    Configuration.HasPoints.existsUnique_point
      (Projectivization K (Fin 3 → K))
      (Projectivization K (Fin 3 → K)) x.1 y.1
      (fun h => hxy (Subtype.ext h)) |>.exists
  have hzxo : Projectivization.orthogonal z x.1 :=
    (Configuration.ofField.mem_iff z x.1).mp hzx
  have hzyo : Projectivization.orthogonal z y.1 :=
    (Configuration.ofField.mem_iff z y.1).mp hzy
  have hzxne : z ≠ x.1 := by
    intro h
    apply hxnon
    simpa [h] using hzxo
  have hzyne : z ≠ y.1 := by
    intro h
    apply hynon
    simpa [h] using hzyo
  have hxz : (graph K).Adj x.1 z := (graph_adj_iff x.1 z).mpr
    ⟨Ne.symm hzxne, Projectivization.orthogonal_comm.mp hzxo⟩
  have hyz : (graph K).Adj y.1 z := (graph_adj_iff y.1 z).mpr
    ⟨Ne.symm hzyne, Projectivization.orthogonal_comm.mp hzyo⟩
  have hzD : z ∈ D := by
    by_contra hzD
    let zs : {v : P K // v ∉ D} := ⟨z, hzD⟩
    have hzmem : zs ∈
        (deleteVertexSetGraph (graph K) D).neighborFinset x ∩
        (deleteVertexSetGraph (graph K) D).neighborFinset y := by
      apply Finset.mem_inter.mpr
      constructor
      · rw [SimpleGraph.mem_neighborFinset]
        exact hxz
      · rw [SimpleGraph.mem_neighborFinset]
        exact hyz
    have hzero := hsafe hxS hyS hxy
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hzmem
    simpa using hzmem
  refine ⟨⟨z, hzD⟩, ?_⟩
  rw [Finset.mem_inter]
  constructor
  · apply (mem_deletedAbsoluteLabel K D x _).mpr
    exact hxz
  · apply (mem_deletedAbsoluteLabel K D y _).mpr
    exact hyz

/-- If a safe selector contains a surviving absolute point, every other
selected point is adjacent to it. -/
theorem adj_absolute_of_mem_safe
    (D : Finset (P K))
    (hDabs : ∀ z ∈ D, Projectivization.orthogonal z z)
    (S : Finset {v : P K // v ∉ D})
    (hsafe : CommonNeighborIndependent (deleteVertexSetGraph (graph K) D) S)
    (x y : {v : P K // v ∉ D}) (hxS : x ∈ S) (hyS : y ∈ S)
    (hxy : x ≠ y) (hxabs : Projectivization.orthogonal x.1 x.1) :
    (graph K).Adj x.1 y.1 := by
  classical
  by_contra hnxy
  obtain ⟨z, hzx, hzy⟩ :=
    Configuration.HasPoints.existsUnique_point
      (Projectivization K (Fin 3 → K))
      (Projectivization K (Fin 3 → K)) x.1 y.1
      (fun h => hxy (Subtype.ext h)) |>.exists
  have hzxo : Projectivization.orthogonal z x.1 :=
    (Configuration.ofField.mem_iff z x.1).mp hzx
  have hzyo : Projectivization.orthogonal z y.1 :=
    (Configuration.ofField.mem_iff z y.1).mp hzy
  have hzxne : z ≠ x.1 := by
    intro h
    apply hnxy
    apply (graph_adj_iff x.1 y.1).mpr
    exact ⟨fun hyx => hxy (Subtype.ext hyx), by
      simpa [h] using hzyo⟩
  have hzyne : z ≠ y.1 := by
    intro h
    apply hnxy
    apply (graph_adj_iff x.1 y.1).mpr
    exact ⟨fun hyx => hxy (Subtype.ext hyx), by
      simpa [h] using Projectivization.orthogonal_comm.mp hzxo⟩
  have hxz : (graph K).Adj x.1 z := (graph_adj_iff x.1 z).mpr
    ⟨Ne.symm hzxne, Projectivization.orthogonal_comm.mp hzxo⟩
  have hyz : (graph K).Adj y.1 z := (graph_adj_iff y.1 z).mpr
    ⟨Ne.symm hzyne, Projectivization.orthogonal_comm.mp hzyo⟩
  have hzD : z ∈ D := by
    by_contra hzD
    let zs : {v : P K // v ∉ D} := ⟨z, hzD⟩
    have hzmem : zs ∈
        (deleteVertexSetGraph (graph K) D).neighborFinset x ∩
        (deleteVertexSetGraph (graph K) D).neighborFinset y := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hxz, hyz⟩
    have hzero := hsafe hxS hyS hxy
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hzmem
    simpa using hzmem
  exact (not_selfOrthogonal_of_adj_selfOrthogonal hxz hxabs)
    (hDabs z hzD)

/-- Consequently a safe selector containing an absolute survivor has at most
two points. -/
theorem card_safe_le_two_of_contains_absolute
    (D : Finset (P K))
    (hDabs : ∀ z ∈ D, Projectivization.orthogonal z z)
    (S : Finset {v : P K // v ∉ D})
    (hsafe : CommonNeighborIndependent (deleteVertexSetGraph (graph K) D) S)
    (x : {v : P K // v ∉ D}) (hxS : x ∈ S)
    (hxabs : Projectivization.orthogonal x.1 x.1) :
    S.card ≤ 2 := by
  classical
  by_contra hcard
  have herase : 1 < (S.erase x).card := by
    rw [Finset.card_erase_of_mem hxS]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp herase
  have hyS := Finset.mem_of_mem_erase hy
  have hzS := Finset.mem_of_mem_erase hz
  have hyx : y ≠ x := Finset.ne_of_mem_erase hy
  have hzx : z ≠ x := Finset.ne_of_mem_erase hz
  have hxy := adj_absolute_of_mem_safe K D hDabs S hsafe x y hxS hyS
    hyx.symm hxabs
  have hxz := adj_absolute_of_mem_safe K D hDabs S hsafe x z hxS hzS
    hzx.symm hxabs
  have hxmem : x ∈
      (deleteVertexSetGraph (graph K) D).neighborFinset y ∩
      (deleteVertexSetGraph (graph K) D).neighborFinset z := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hxy.symm, hxz.symm⟩
  have hzero := hsafe hyS hzS hyz
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hxmem
  simpa using hxmem

/-- At most `q` surviving points can carry any fixed deleted-absolute
label, since an absolute point has full-graph degree `q`. -/
theorem card_deletedAbsoluteLabel_fiber_le
    (D : Finset (P K)) (hDabs : ∀ z ∈ D, Projectivization.orthogonal z z)
    (a : {a : P K // a ∈ D}) :
    (Finset.univ.filter fun x : {v : P K // v ∉ D} =>
      a ∈ deletedAbsoluteLabel K D x).card ≤ Nat.card K := by
  classical
  let e : {x : {v : P K // v ∉ D} //
      x ∈ Finset.univ.filter fun x => a ∈ deletedAbsoluteLabel K D x} ↪
      {y : P K // y ∈ (graph K).neighborFinset a.1} :=
    ⟨fun x => ⟨x.1.1, by
        rw [SimpleGraph.mem_neighborFinset]
        exact ((graph K).adj_comm a.1 x.1.1).mpr
          ((mem_deletedAbsoluteLabel K D x.1 a).mp
            (by simpa using x.2))⟩,
      fun x y h => by
        have hp : x.1.1 = y.1.1 := congrArg
          (fun z : {y : P K // y ∈ (graph K).neighborFinset a.1} => z.1) h
        exact Subtype.ext (Subtype.ext hp)⟩
  have hc := Fintype.card_le_of_injective e e.injective
  rw [Fintype.card_coe, Fintype.card_coe] at hc
  calc
    (Finset.univ.filter fun x : {v : P K // v ∉ D} =>
        a ∈ deletedAbsoluteLabel K D x).card ≤
        ((graph K).neighborFinset a.1).card := hc
    _ = (graph K).degree a.1 := (graph K).card_neighborFinset_eq_degree a.1
    _ = Nat.card K := degree_eq_card_of_selfOrthogonal (hDabs a.1 a.2)

/-- A four-absolute-point deletion cannot be repaired by a compatible
five-cycle gadget of minimum degree `q ≥ 7` if every selected survivor is
nonabsolute.  This is the polarity realization of the rank-two selector
packing obstruction. -/
theorem fiveCycleAttachment_impossible_of_four_absolute_deletions_nonabsolute
    (h2 : (2 : K) ≠ 0) (hq : 7 ≤ Nat.card K)
    (D : Finset (P K)) (hDcard : D.card = 4)
    (hDabs : ∀ z ∈ D, Projectivization.orthogonal z z)
    (A : Fin 5 → Finset {v : P K // v ∉ D})
    (hcompat : GadgetAttachmentCompatible
      (deleteVertexSetGraph (graph K) D) (cycleGraph 5) A)
    (hnewDegree : ∀ w : Fin 5, Nat.card K ≤
      (attachGadget (deleteVertexSetGraph (graph K) D)
        (cycleGraph 5) A).degree (.inr w))
    (hnonabsolute : ∀ i x, x ∈ A i →
      ¬ Projectivization.orthogonal x.1 x.1) :
    False := by
  classical
  have hlarge : ∀ i, Nat.card K - 2 ≤ (A i).card := by
    intro i
    have hi := hnewDegree i
    rw [attachGadget_degree_new, cycleGraph_degree_three_le] at hi
    omega
  have hfour : ∀ i, 4 ≤ (A i).card := by
    intro i
    have hi := hlarge i
    omega
  have hnonempty : ∀ i x, x ∈ A i →
      (deletedAbsoluteLabel K D x).Nonempty := by
    intro i x hx
    have hex : ∃ y ∈ A i, y ≠ x := by
      by_contra hn
      push_neg at hn
      have hsub : A i ⊆ {x} := by
        intro y hy
        simpa [hn y hy]
      have hc := Finset.card_le_card hsub
      simp at hc
      have := hfour i
      omega
    obtain ⟨y, hy, hyx⟩ := hex
    obtain ⟨a, hax, hay⟩ := Finset.not_disjoint_iff.mp
      (deletedAbsoluteLabel_inter_nonempty_of_safe K D (A i)
        (GadgetAttachmentCompatible.selector_safe _ _ _ hcompat i)
        x y hx hy hyx.symm
        (hnonabsolute i x hx) (hnonabsolute i y hy) |>.not_disjoint)
    exact ⟨a, hax⟩
  apply Erdos85.fiveCycleAttachment_impossible_of_rank_two_labels
    (deleteVertexSetGraph (graph K) D) (Nat.card K) hq A
    (deletedAbsoluteLabel K D) hcompat hnewDegree
  · simpa [Fintype.card_coe, hDcard]
  · exact hnonempty
  · intro i x hx
    exact card_deletedAbsoluteLabel_le_two K h2 D hDabs x
      (hnonabsolute i x hx)
  · intro i x hx y hy
    rw [Finset.not_disjoint_iff]
    by_cases hxy : x = y
    · subst y
      obtain ⟨a, ha⟩ := hnonempty i x hx
      exact ⟨a, ha, ha⟩
    · obtain ⟨a, ha⟩ :=
        deletedAbsoluteLabel_inter_nonempty_of_safe K D (A i)
          (GadgetAttachmentCompatible.selector_safe _ _ _ hcompat i)
          x y hx hy hxy
          (hnonabsolute i x hx) (hnonabsolute i y hy)
      exact ⟨a, (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩
  · intro i x hx y hy hxcard hlabel
    exact eq_of_deletedAbsoluteLabel_eq_of_card_two K D hDabs x y
      (hnonabsolute i x hx) (hnonabsolute i y hy) hxcard hlabel
  · exact card_deletedAbsoluteLabel_fiber_le K D hDabs

/-- The nonabsolute hypothesis above is automatic: a compatible selector
containing a surviving absolute point has size at most two, while degree
`q ≥ 7` forces every five-cycle selector to have at least `q-2 ≥ 5` points.
Thus the four-absolute-deletion/five-cycle repair used at `q=5` cannot scale
to any odd-characteristic field of order at least seven. -/
theorem fiveCycleAttachment_impossible_of_four_absolute_deletions
    (h2 : (2 : K) ≠ 0) (hq : 7 ≤ Nat.card K)
    (D : Finset (P K)) (hDcard : D.card = 4)
    (hDabs : ∀ z ∈ D, Projectivization.orthogonal z z)
    (A : Fin 5 → Finset {v : P K // v ∉ D})
    (hcompat : GadgetAttachmentCompatible
      (deleteVertexSetGraph (graph K) D) (cycleGraph 5) A)
    (hnewDegree : ∀ w : Fin 5, Nat.card K ≤
      (attachGadget (deleteVertexSetGraph (graph K) D)
        (cycleGraph 5) A).degree (.inr w)) :
    False := by
  apply fiveCycleAttachment_impossible_of_four_absolute_deletions_nonabsolute
    K h2 hq D hDcard hDabs A hcompat hnewDegree
  intro i x hx hxabs
  have hlarge : Nat.card K - 2 ≤ (A i).card := by
    have hi := hnewDegree i
    rw [attachGadget_degree_new, cycleGraph_degree_three_le] at hi
    omega
  have hsmall := card_safe_le_two_of_contains_absolute K D hDabs (A i)
    (GadgetAttachmentCompatible.selector_safe _ _ _ hcompat i) x hx hxabs
  omega

/-- Fully general polarity obstruction: after deleting any absolute set `D`,
no compatible two-regular gadget with more vertices than `D` can restore new
degree `q` once `q ≥ 6`. -/
theorem degreeTwoGadgetAttachment_impossible_of_absolute_deletions
    (h2 : (2 : K) ≠ 0) (hq : 6 ≤ Nat.card K)
    (D : Finset (P K))
    (hDabs : ∀ z ∈ D, Projectivization.orthogonal z z)
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : P K // v ∉ D})
    (hcompat : GadgetAttachmentCompatible
      (deleteVertexSetGraph (graph K) D) F A)
    (hFdegree : ∀ w, F.degree w = 2)
    (hnewDegree : ∀ w, Nat.card K ≤
      (attachGadget (deleteVertexSetGraph (graph K) D) F A).degree (.inr w))
    (hmore : D.card < Fintype.card W) :
    False := by
  classical
  have hlarge : ∀ i, Nat.card K - 2 ≤ (A i).card := by
    intro i
    have hi := hnewDegree i
    rw [attachGadget_degree_new, hFdegree] at hi
    omega
  have hfour : ∀ i, 4 ≤ (A i).card := by
    intro i
    have hi := hlarge i
    omega
  have hnonabsolute : ∀ i x, x ∈ A i →
      ¬ Projectivization.orthogonal x.1 x.1 := by
    intro i x hx hxabs
    have hsmall := card_safe_le_two_of_contains_absolute K D hDabs (A i)
      (GadgetAttachmentCompatible.selector_safe _ _ _ hcompat i) x hx hxabs
    have hi := hfour i
    omega
  have hnonempty : ∀ i x, x ∈ A i →
      (deletedAbsoluteLabel K D x).Nonempty := by
    intro i x hx
    have hex : ∃ y ∈ A i, y ≠ x := by
      by_contra hn
      push_neg at hn
      have hsub : A i ⊆ {x} := by
        intro y hy
        simpa [hn y hy]
      have hc := Finset.card_le_card hsub
      simp at hc
      have hi := hfour i
      omega
    obtain ⟨y, hy, hyx⟩ := hex
    obtain ⟨a, ha⟩ := deletedAbsoluteLabel_inter_nonempty_of_safe K D (A i)
      (GadgetAttachmentCompatible.selector_safe _ _ _ hcompat i)
      x y hx hy hyx.symm (hnonabsolute i x hx) (hnonabsolute i y hy)
    exact ⟨a, (Finset.mem_inter.mp ha).1⟩
  apply Erdos85.degreeTwoGadgetAttachment_impossible_of_rank_two_labels
    (deleteVertexSetGraph (graph K) D) F (Nat.card K) hq A
    (deletedAbsoluteLabel K D) hcompat hFdegree hnewDegree
  · simpa [Fintype.card_coe] using hmore
  · exact hnonempty
  · intro i x hx
    exact card_deletedAbsoluteLabel_le_two K h2 D hDabs x
      (hnonabsolute i x hx)
  · intro i x hx y hy
    rw [Finset.not_disjoint_iff]
    by_cases hxy : x = y
    · subst y
      obtain ⟨a, ha⟩ := hnonempty i x hx
      exact ⟨a, ha, ha⟩
    · obtain ⟨a, ha⟩ := deletedAbsoluteLabel_inter_nonempty_of_safe K D (A i)
        (GadgetAttachmentCompatible.selector_safe _ _ _ hcompat i)
        x y hx hy hxy (hnonabsolute i x hx) (hnonabsolute i y hy)
      exact ⟨a, (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩
  · intro i x hx y hy hxcard hlabel
    exact eq_of_deletedAbsoluteLabel_eq_of_card_two K D hDabs x y
      (hnonabsolute i x hx) (hnonabsolute i y hy) hxcard hlabel
  · exact card_deletedAbsoluteLabel_fiber_le K D hDabs

end Erdos85.Polarity
