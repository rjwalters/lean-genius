import Proofs.Erdos85AbstractTraceEscape
import Proofs.Erdos85OneTwentyThreeTraceEscape
import Proofs.Erdos85SymmetricRestrictionSemisimple
import Proofs.Erdos85OneTwentyThreeArithmetic
import Proofs.Erdos85ExteriorCharpolyDivisibility
import Proofs.Erdos85OneTwentyThreeSemisimplePackage
import Proofs.Erdos85OwnerFiberProjectedSquare
import Proofs.Erdos85BoundaryQuotientDivisibility
import Proofs.Erdos85CycleCoverGraph
import Proofs.Erdos85CycleCoverColorRigidity
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85MixedDiagonalDichotomy
import Proofs.Erdos85OrientedFiveMass

/-!
# Scalar-123 residual terminal

The operator theorem below is the final contradiction engine.  The graph
wrapper transports the saturated owner-fiber hard sector into this engine.
-/

open Polynomial
open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restricted cherry counting: if centers in `A` create more two-element
endpoint subsets inside `B` than `B` has pairs, two centers share an endpoint
pair and hence form a four-cycle. -/
theorem containsC4_of_restricted_cherry_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (h : B.card.choose 2 <
      ∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) :
    containsC4 V G := by
  classical
  set C : Finset (Σ _ : V, Finset V) :=
    A.sigma (fun a => (B ∩ G.neighborFinset a).powersetCard 2) with hC
  set T : Finset (Finset V) := B.powersetCard 2 with hT
  have hCcard : C.card =
      ∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2 := by
    rw [hC, Finset.card_sigma]
    simp only [Finset.card_powersetCard]
  have hTcard : T.card = B.card.choose 2 := by
    rw [hT, Finset.card_powersetCard]
  have hmaps : ∀ p ∈ C, p.2 ∈ T := by
    intro p hp
    rw [hC, Finset.mem_sigma] at hp
    rw [hT, Finset.mem_powersetCard]
    have hpData := Finset.mem_powersetCard.mp hp.2
    exact ⟨hpData.1.trans Finset.inter_subset_left, hpData.2⟩
  have hlt : T.card < C.card := by rw [hTcard, hCcard]; exact h
  obtain ⟨p, hp, q, hq, hpq, hfe⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  obtain ⟨v, e⟩ := p
  obtain ⟨v', e'⟩ := q
  simp only at hfe
  subst hfe
  have hvv : v ≠ v' := by
    rintro rfl
    exact hpq rfl
  rw [hC, Finset.mem_sigma] at hp hq
  obtain ⟨-, hpe⟩ := hp
  obtain ⟨-, hqe⟩ := hq
  obtain ⟨hsubv, hecard⟩ := Finset.mem_powersetCard.mp hpe
  obtain ⟨hsubv', -⟩ := Finset.mem_powersetCard.mp hqe
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hecard
  have hxMem : x ∈ ({x, y} : Finset V) := Finset.mem_insert_self x {y}
  have hyMem : y ∈ ({x, y} : Finset V) := by simp
  have hxvData := Finset.mem_inter.mp (hsubv hxMem)
  have hyvData := Finset.mem_inter.mp (hsubv hyMem)
  have hxv'Data := Finset.mem_inter.mp (hsubv' hxMem)
  have hyv'Data := Finset.mem_inter.mp (hsubv' hyMem)
  have avx : G.Adj v x :=
    (G.mem_neighborFinset v x).mp hxvData.2
  have avy : G.Adj v y :=
    (G.mem_neighborFinset v y).mp hyvData.2
  have av'x : G.Adj v' x :=
    (G.mem_neighborFinset v' x).mp hxv'Data.2
  have av'y : G.Adj v' y :=
    (G.mem_neighborFinset v' y).mp hyv'Data.2
  exact containsC4_of_rim avx.symm avy av'y.symm av'x hxy
    hvv
    (G.ne_of_adj avx) (G.ne_of_adj avy)
    (G.ne_of_adj av'x) (G.ne_of_adj av'y)

/- Exact restricted-cherry counting by endpoint pairs.  If every cherry's
endpoint pair is `good`, and every good two-element endpoint set has a unique
center, projection to the endpoint set is a bijection. -/
/-- The two-element cliques of a finite graph are exactly its edges, stated
in the `Finset (Finset V)` representation used by the cherry counts below. -/
theorem card_adjacent_pairs_eq_card_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ((Finset.univ.powersetCard 2).filter (fun e : Finset V =>
      ∀ x ∈ e, ∀ y ∈ e, x ≠ y → H.Adj x y)).card =
      H.edgeFinset.card := by
  classical
  symm
  apply Finset.card_bij (fun e _he => e.toFinset)
  · intro e he
    have hcard : e.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag e (H.not_isDiag_of_mem_edgeFinset he)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    intro x hx y hy hxy
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : H.Adj a b := H.mem_edgeFinset.mp he
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
        Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact hab
      · exact hab.symm
      · exact (hxy rfl).elim
  · intro e he e' he' hfin
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction e' using Sym2.inductionOn with
      | _ c d =>
        simp only [Sym2.toFinset_mk_eq] at hfin
        have hc : c = a ∨ c = b := by
          have : c ∈ ({a, b} : Finset V) := by rw [hfin]; simp
          simpa [eq_comm] using this
        have hd : d = a ∨ d = b := by
          have : d ∈ ({a, b} : Finset V) := by rw [hfin]; simp
          simpa [eq_comm] using this
        have hcd : c ≠ d := (H.mem_edgeFinset.mp he').ne
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · exact (hcd rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hcd rfl).elim
  · intro e he
    have heData := Finset.mem_filter.mp he
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp heData.1).2
    have hne : a ≠ b := by
      intro h
      subst b
      simp at hab
    have hadj : H.Adj a b :=
      heData.2 a (by simp [heq]) b (by simp [heq]) hne
    refine ⟨s(a, b), H.mem_edgeFinset.mpr hadj, ?_⟩
    simpa [heq, Sym2.toFinset_mk_eq]

/-- Restricted two-element cliques in a finite vertex cell are counted by
the edge finset of the induced graph on that cell. -/
theorem card_adjacent_pairs_eq_card_edgeFinset_induce
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    ((B.powersetCard 2).filter (fun e : Finset V =>
      ∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y)).card =
      (G.induce (B : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (B : Set V)
  rw [← card_adjacent_pairs_eq_card_edgeFinset H]
  symm
  apply Finset.card_bij (fun e _he => e.image (fun x => x.1))
  · intro e he
    have heData := Finset.mem_filter.mp he
    have hePow := Finset.mem_powersetCard.mp heData.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨z', hz'e, rfl⟩ := Finset.mem_image.mp hz
      exact z'.2
    · rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hePow.2
    · intro x hx y hy hxy
      obtain ⟨x', hx'e, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy'e, hyval⟩ := Finset.mem_image.mp hy
      subst y
      exact heData.2 x' hx'e y' hy'e
        (fun h => hxy (congrArg Subtype.val h))
  · intro e he e' he' hfin
    exact (Finset.image_injective Subtype.val_injective) hfin
  · intro e he
    have heData := Finset.mem_filter.mp he
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp heData.1).2
    have haB : a ∈ B :=
      (Finset.mem_powersetCard.mp heData.1).1 (by simp [heq])
    have hbB : b ∈ B :=
      (Finset.mem_powersetCard.mp heData.1).1 (by simp [heq])
    let a' : (B : Set V) := ⟨a, haB⟩
    let b' : (B : Set V) := ⟨b, hbB⟩
    let e' : Finset (B : Set V) := {a', b'}
    have hne : a ≠ b := by
      intro h
      subst b
      simp at hab
    have hadj : G.Adj a b :=
      heData.2 a (by simp [heq]) b (by simp [heq]) hne
    refine ⟨e', ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · simp [e', a', b', hne]
      · intro x hx y hy hxy
        simp only [e', Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hxy rfl).elim
        · exact hadj
        · exact hadj.symm
        · exact (hxy rfl).elim
    · ext z
      simp [e', a', b', heq]

/-- Among the two-element subsets of a finite cell, the nonedges are the
complement of the induced edges. -/
theorem card_nonadjacent_pairs_eq_choose_sub_card_edgeFinset_induce
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    ((B.powersetCard 2).filter (fun e : Finset V =>
      ∀ x ∈ e, ∀ y ∈ e, x ≠ y → ¬G.Adj x y)).card =
      B.card.choose 2 - (G.induce (B : Set V)).edgeFinset.card := by
  classical
  let P := B.powersetCard 2
  let adj := fun e : Finset V =>
    ∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y
  let nonadj := fun e : Finset V =>
    ∀ x ∈ e, ∀ y ∈ e, x ≠ y → ¬G.Adj x y
  have hcomplement : P.filter nonadj = P.filter (fun e => ¬adj e) := by
    ext e
    simp only [Finset.mem_filter]
    refine and_congr_right fun heP => ?_
    obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp heP).2
    have hne : a ≠ b := by
      intro h
      subst b
      simp at hab
    simp only [nonadj, adj]
    constructor
    · intro hnadj hadj
      exact hnadj a (by simp [heq]) b (by simp [heq]) hne
        (hadj a (by simp [heq]) b (by simp [heq]) hne)
    · intro hnotadj x hx y hy hxy hxyAdj
      apply hnotadj
      intro q hq q' hq' hqq'
      rw [heq] at hx hy hq hq'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hq hq'
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
        · exact (hqq' rfl).elim
        · exact hxyAdj
        · exact hxyAdj.symm
        · exact (hqq' rfl).elim
      · rcases hq with rfl | rfl <;> rcases hq' with rfl | rfl
        · exact (hqq' rfl).elim
        · exact hxyAdj.symm
        · exact hxyAdj
        · exact (hqq' rfl).elim
      · exact (hxy rfl).elim
  have hpartition := Finset.card_filter_add_card_filter_not (s := P) adj
  have hadj : (P.filter adj).card =
      (G.induce (B : Set V)).edgeFinset.card := by
    exact card_adjacent_pairs_eq_card_edgeFinset_induce G B
  have htotal : P.card = B.card.choose 2 := by
    simp [P]
  change (P.filter nonadj).card = _
  rw [hcomplement]
  rw [hadj, htotal] at hpartition
  omega

/-- In a connected component of a finite two-regular graph there is one
edge per vertex, so its nonadjacent pairs number `choose(n,2) - n`. -/
theorem card_nonadjacent_pairs_component_twoRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hdegree : ∀ z : V, D.degree z = 2)
    (o : D.ConnectedComponent) :
    let B := o.supp.toFinite.toFinset
    ((B.powersetCard 2).filter (fun e : Finset V =>
      ∀ x ∈ e, ∀ y ∈ e, x ≠ y → ¬D.Adj x y)).card =
      B.card.choose 2 - B.card := by
  classical
  dsimp only
  let B := o.supp.toFinite.toFinset
  let H := D.induce (B : Set V)
  have hregH : ∀ z : (B : Set V), H.degree z = 2 := by
    intro z
    have hsubset : D.neighborSet z.1 ⊆ (B : Set V) := by
      intro y hzy
      have hzSupp : z.1 ∈ o.supp := by simpa [B] using z.2
      have hySupp : y ∈ o.supp := by
        rw [ConnectedComponent.mem_supp_iff, ←
          (ConnectedComponent.mem_supp_iff o z.1).mp hzSupp]
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj hzy).symm
      simpa [B] using hySupp
    have hcardN : (H.neighborFinset z).card =
        (D.neighborFinset z.1).card := by
      apply Finset.card_bij (fun y _hy => y.1)
      · intro y hy
        exact (D.mem_neighborFinset z.1 y.1).mpr
          ((H.mem_neighborFinset z y).mp hy)
      · intro y hy y' hy' hyy
        exact Subtype.ext hyy
      · intro y hy
        have hzy : D.Adj z.1 y := (D.mem_neighborFinset z.1 y).mp hy
        let y' : (B : Set V) := ⟨y, hsubset hzy⟩
        refine ⟨y', ?_, rfl⟩
        exact (H.mem_neighborFinset z y').mpr hzy
    rw [← H.card_neighborFinset_eq_degree, hcardN,
      D.card_neighborFinset_eq_degree, hdegree]
  have hedge : H.edgeFinset.card = B.card := by
    have hhandshake : 2 * H.edgeFinset.card = 2 * B.card := by
      calc
        2 * H.edgeFinset.card = ∑ z : (B : Set V), H.degree z :=
          H.sum_degrees_eq_twice_card_edges.symm
        _ = ∑ _z : (B : Set V), 2 := by
          apply Finset.sum_congr rfl
          intro z _hz
          exact hregH z
        _ = 2 * B.card := by simp [Nat.mul_comm]
    omega
  have hnon := card_nonadjacent_pairs_eq_choose_sub_card_edgeFinset_induce D B
  rw [hedge] at hnon
  exact hnon

/-- Exact restricted-cherry counting by endpoint pairs.  If every cherry's
endpoint pair is `good`, and every good two-element endpoint set has a unique
center, projection to the endpoint set is a bijection. -/
theorem sum_choose_inter_neighbor_eq_card_good_pairs_of_unique_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (good : Finset V → Prop) [DecidablePred good]
    (hmaps : ∀ a ∈ A, ∀ e ∈ (B ∩ G.neighborFinset a).powersetCard 2,
      good e)
    (hunique : ∀ e ∈ B.powersetCard 2, good e →
      ∃! a : V, a ∈ A ∧ e ⊆ G.neighborFinset a) :
    (∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) =
      ((B.powersetCard 2).filter good).card := by
  classical
  let C : Finset (Σ _ : V, Finset V) :=
    A.sigma (fun a => (B ∩ G.neighborFinset a).powersetCard 2)
  let T : Finset (Finset V) := (B.powersetCard 2).filter good
  have hcard : C.card = T.card := by
    apply Finset.card_bij (fun p _hp => p.2)
    · intro p hp
      simp only [C, Finset.mem_sigma] at hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr
          ⟨(Finset.mem_powersetCard.mp hp.2).1.trans Finset.inter_subset_left,
            (Finset.mem_powersetCard.mp hp.2).2⟩,
          hmaps p.1 hp.1 p.2 hp.2⟩
    · intro p hp q hq hpq
      simp only [C, Finset.mem_sigma] at hp hq
      have hpT : p.2 ∈ B.powersetCard 2 :=
        Finset.mem_powersetCard.mpr
          ⟨(Finset.mem_powersetCard.mp hp.2).1.trans Finset.inter_subset_left,
            (Finset.mem_powersetCard.mp hp.2).2⟩
      have hpGood : good p.2 := hmaps p.1 hp.1 p.2 hp.2
      obtain ⟨a, ha, hauniq⟩ := hunique p.2 hpT hpGood
      have hpa : p.1 = a := hauniq p.1 ⟨hp.1, fun z hz => by
        have hzInter := (Finset.mem_powersetCard.mp hp.2).1 hz
        exact (Finset.mem_inter.mp hzInter).2⟩
      have hqa : q.1 = a := hauniq q.1 ⟨hq.1, fun z hz => by
        have hzq : z ∈ q.2 := by simpa [hpq] using hz
        have hzInter := (Finset.mem_powersetCard.mp hq.2).1 hzq
        exact (Finset.mem_inter.mp hzInter).2⟩
      cases p
      cases q
      simp only at hpq hpa hqa
      subst_vars
      rfl
    · intro e he
      have heT := Finset.mem_filter.mp he
      obtain ⟨a, ha, _hauniq⟩ := hunique e heT.1 heT.2
      refine ⟨⟨a, e⟩, ?_, rfl⟩
      simp only [C, Finset.mem_sigma]
      refine ⟨ha.1, Finset.mem_powersetCard.mpr ⟨?_, (Finset.mem_powersetCard.mp heT.1).2⟩⟩
      intro z hz
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp heT.1).1 hz, ha.2 hz⟩
  calc
    (∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) = C.card := by
      simp only [C, Finset.card_sigma, Finset.card_powersetCard]
    _ = T.card := hcard
    _ = ((B.powersetCard 2).filter good).card := rfl

/-- Uniform restricted-cherry obstruction for a center set whose vertices
each have exactly four neighbors in the endpoint set. -/
theorem false_of_centers_four_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (A B : Finset V)
    (hcount : B.card.choose 2 < A.card * 6)
    (hdegree : ∀ a ∈ A, (B ∩ G.neighborFinset a).card = 4) : False := by
  apply hfree
  apply containsC4_of_restricted_cherry_count G A B
  have hsum :
      (∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) =
        A.card * 6 := by
    calc
      (∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) =
          ∑ _a ∈ A, 6 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hdegree a ha]
            norm_num [Nat.choose]
      _ = A.card * 6 := by simp
  rw [hsum]
  exact hcount

/-- Uniform restricted-cherry obstruction for a center set whose vertices
each have exactly three neighbors in the endpoint set. -/
theorem false_of_centers_three_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (A B : Finset V)
    (hcount : B.card.choose 2 < A.card * 3)
    (hdegree : ∀ a ∈ A, (B ∩ G.neighborFinset a).card = 3) : False := by
  apply hfree
  apply containsC4_of_restricted_cherry_count G A B
  have hsum :
      (∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) =
        A.card * 3 := by
    calc
      (∑ a ∈ A, ((B ∩ G.neighborFinset a).card).choose 2) =
          ∑ _a ∈ A, 3 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hdegree a ha]
            norm_num [Nat.choose]
      _ = A.card * 3 := by simp
  rw [hsum]
  exact hcount

/-- Six vertices cannot each have three neighbors in the same six-vertex
set in a `C₄`-free graph: the resulting eighteen restricted cherries exceed
the fifteen endpoint pairs. -/
theorem false_of_six_centers_three_neighbors_in_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (A B : Finset V)
    (hAcard : A.card = 6) (hBcard : B.card = 6)
    (hdegree : ∀ a ∈ A, (B ∩ G.neighborFinset a).card = 3) : False := by
  apply false_of_centers_three_neighbors G hfree A B
  · rw [hAcard, hBcard]
    norm_num [Nat.choose]
  · exact hdegree

/-- The small numerical instance first exposed by the rigid `(8,40)`
four-layer transport branch. -/
theorem false_of_six_centers_four_neighbors_in_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (A B : Finset V)
    (hAcard : A.card = 6) (hBcard : B.card = 8)
    (hdegree : ∀ a ∈ A, (B ∩ G.neighborFinset a).card = 4) : False := by
  apply false_of_centers_four_neighbors G hfree A B
  · rw [hAcard, hBcard]
    norm_num [Nat.choose]
  · exact hdegree

/-- An order-12 component cannot send four neighbors per vertex into an
order-12 target: its `72` restricted cherries exceed the target's `66`
pairs.  This removes the degree-four equal-cycle intertwiner sector in the
last symmetric four-orphan branch. -/
theorem false_of_twelve_centers_four_neighbors_in_twelve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (A B : Finset V)
    (hAcard : A.card = 12) (hBcard : B.card = 12)
    (hdegree : ∀ a ∈ A, (B ∩ G.neighborFinset a).card = 4) : False := by
  apply false_of_centers_four_neighbors G hfree A B
  · rw [hAcard, hBcard]
    norm_num [Nat.choose]
  · exact hdegree

/-- Arithmetic certificate for the three weighted row signatures in the
remaining `(12,36)` two-component orphan branch.  Here `S_a` is the total
reduced R-order carried by rows with `a` neighbors in the order-12 orphan
component. -/
theorem twelve_thirtysix_weighted_row_signature
    (S₀ S₁ S₂ S₃ S₄ : ℕ)
    (hmass : S₀ + S₁ + S₂ + S₃ + S₄ = 60)
    (hedges : S₁ + 2 * S₂ + 3 * S₃ + 4 * S₄ = 60)
    (hcherries : S₂ + 3 * S₃ + 6 * S₄ = 18)
    (hthree : S₃ = 0) (hfour : S₄ ≠ 1) :
    (S₀ = 18 ∧ S₁ = 24 ∧ S₂ = 18 ∧ S₃ = 0 ∧ S₄ = 0) ∨
      (S₀ = 12 ∧ S₁ = 40 ∧ S₂ = 6 ∧ S₃ = 0 ∧ S₄ = 2) ∨
      (S₀ = 9 ∧ S₁ = 48 ∧ S₂ = 0 ∧ S₃ = 0 ∧ S₄ = 3) := by
  omega

/-- A positive cycle order cannot both divide `12` and support a
two-neighbor row into an order-`36` component: detailed balance would make
twice that order a multiple of `36`. -/
theorem false_of_six_le_order_dvd_twelve_and_twice_eq_thirtysix_mul
    (r q : ℕ) (hr : 6 ≤ r) (hr12 : r ∣ 12)
    (hbalance : 2 * r = 36 * q) : False := by
  have hrle : r ≤ 12 := Nat.le_of_dvd (by norm_num) hr12
  interval_cases r <;> omega

/-- Once rows of degree two into the order-`12` component are excluded, the
`(12,36)` weighted ledger has only its third signature left. -/
theorem twelve_thirtysix_weighted_row_signature_of_no_two
    (S₀ S₁ S₂ S₃ S₄ : ℕ)
    (hmass : S₀ + S₁ + S₂ + S₃ + S₄ = 60)
    (hedges : S₁ + 2 * S₂ + 3 * S₃ + 4 * S₄ = 60)
    (hcherries : S₂ + 3 * S₃ + 6 * S₄ = 18)
    (hthree : S₃ = 0) (hfour : S₄ ≠ 1) (htwo : S₂ = 0) :
    S₀ = 9 ∧ S₁ = 48 ∧ S₂ = 0 ∧ S₃ = 0 ∧ S₄ = 3 := by
  rcases twelve_thirtysix_weighted_row_signature S₀ S₁ S₂ S₃ S₄
      hmass hedges hcherries hthree hfour with h | h | h
  · omega
  · omega
  · exact h

/-- A finite sum whose nonzero summands are all at least two cannot be one. -/
theorem finset_sum_ne_one_of_eq_zero_or_two_le
    {α : Type*} [DecidableEq α] (C : Finset α) (f : α → ℕ)
    (hf : ∀ c ∈ C, f c = 0 ∨ 2 ≤ f c) :
    ∑ c ∈ C, f c ≠ 1 := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | @insert a C ha ih =>
      rw [Finset.sum_insert ha]
      rcases hf a (by simp) with hzero | htwo
      · simp only [hzero, zero_add]
        exact ih (fun c hc => hf c (by simp [hc]))
      · have hnonneg : 0 ≤ ∑ c ∈ C, f c := Nat.zero_le _
        omega

/-- Generic bookkeeping for a component family whose quotient row values
lie in `{0,1,2,3,4}`.  Stratifying by the row value converts total mass,
edge mass, and cherry mass into the five weighted ledger equations. -/
theorem weighted_quotient_zero_four_stratification
    {α : Type*} [DecidableEq α]
    (C : Finset α) (w q : α → ℕ)
    (hq : ∀ c ∈ C, q c ≤ 4)
    (M E P : ℕ)
    (hmass : ∑ c ∈ C, w c = M)
    (hedges : ∑ c ∈ C, w c * q c = E)
    (hcherries : ∑ c ∈ C, w c * (q c).choose 2 = P) :
    let S := fun a : ℕ => ∑ c ∈ C, if q c = a then w c else 0
    S 0 + S 1 + S 2 + S 3 + S 4 = M ∧
      S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4 = E ∧
      S 2 + 3 * S 3 + 6 * S 4 = P := by
  classical
  dsimp only
  let S := fun a : ℕ => ∑ c ∈ C, if q c = a then w c else 0
  have hmassParts : S 0 + S 1 + S 2 + S 3 + S 4 =
      ∑ c ∈ C, w c := by
    simp only [S, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hcq := hq c hc
    interval_cases hqc : q c <;> simp [hqc, Nat.mul_comm]
  have hedgeParts : S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4 =
      ∑ c ∈ C, w c * q c := by
    simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hcq := hq c hc
    interval_cases hqc : q c <;> simp [hqc, Nat.mul_comm]
  have hcherryParts : S 2 + 3 * S 3 + 6 * S 4 =
      ∑ c ∈ C, w c * (q c).choose 2 := by
    simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hcq := hq c hc
    interval_cases hqc : q c <;> norm_num [hqc, Nat.choose, Nat.mul_comm]
  exact ⟨hmassParts.trans hmass, hedgeParts.trans hedges,
    hcherryParts.trans hcherries⟩

/-- Divide a three-divisible component ledger by three before stratifying
its quotient values.  The reduced total mass is `60`; edge and cherry
equations are retained in denominator-free scaled form. -/
theorem weighted_quotient_zero_four_stratification_div_three
    {α : Type*} [DecidableEq α]
    (C : Finset α) (r q : α → ℕ)
    (hdiv : ∀ c ∈ C, 3 ∣ r c)
    (hq : ∀ c ∈ C, q c ≤ 4)
    (E P : ℕ)
    (hmass : ∑ c ∈ C, r c = 180)
    (hedges : ∑ c ∈ C, r c * q c = E)
    (hcherries : ∑ c ∈ C, r c * (q c).choose 2 = P) :
    let w := fun c ↦ r c / 3
    let S := fun a : ℕ ↦ ∑ c ∈ C, if q c = a then w c else 0
    S 0 + S 1 + S 2 + S 3 + S 4 = 60 ∧
      3 * (S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4) = E ∧
      3 * (S 2 + 3 * S 3 + 6 * S 4) = P := by
  classical
  dsimp only
  let w := fun c ↦ r c / 3
  let S := fun a : ℕ ↦ ∑ c ∈ C, if q c = a then w c else 0
  have hw : ∀ c ∈ C, 3 * w c = r c := by
    intro c hc
    exact Nat.mul_div_cancel' (hdiv c hc)
  have hmassW : ∑ c ∈ C, w c = 60 := by
    have hscaled : 3 * (∑ c ∈ C, w c) = 180 := by
      calc
        3 * (∑ c ∈ C, w c) = ∑ c ∈ C, 3 * w c := by
          rw [Finset.mul_sum]
        _ = ∑ c ∈ C, r c := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hw c hc
        _ = 180 := hmass
    omega
  have hedgeW : 3 * (∑ c ∈ C, w c * q c) = E := by
    calc
      3 * (∑ c ∈ C, w c * q c) =
          ∑ c ∈ C, 3 * (w c * q c) := by rw [Finset.mul_sum]
      _ = ∑ c ∈ C, r c * q c := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← hw c hc]
        ring
      _ = E := hedges
  have hcherryW : 3 * (∑ c ∈ C, w c * (q c).choose 2) = P := by
    calc
      3 * (∑ c ∈ C, w c * (q c).choose 2) =
          ∑ c ∈ C, 3 * (w c * (q c).choose 2) := by
            rw [Finset.mul_sum]
      _ = ∑ c ∈ C, r c * (q c).choose 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← hw c hc]
        ring
      _ = P := hcherries
  obtain ⟨hm, he, hp⟩ := weighted_quotient_zero_four_stratification
    C w q hq 60 (∑ c ∈ C, w c * q c)
      (∑ c ∈ C, w c * (q c).choose 2)
      hmassW rfl rfl
  change S 0 + S 1 + S 2 + S 3 + S 4 = 60 ∧ _
  exact ⟨hm, (congrArg (fun n ↦ 3 * n) he).trans hedgeW,
    (congrArg (fun n ↦ 3 * n) hp).trans hcherryW⟩

/-- Capacity certificate eliminating the five externally enumerated
weighted signatures for the symmetric `(24,24)` branch.  Here `n₁`, `n₃`,
and `n₈₂` count reduced-order-eight rows of types `1`, `3`, and `2`, while
`n₄₂` counts reduced-order-four rows of type `2`.  Cover-target uniqueness
gives `n₄₂ ≤ 1`, and the five owner bins give room for at most five
reduced-order-eight rows in total. -/
theorem false_of_twentyfour_twentyfour_weighted_signature_capacity
    (S₁ S₂ S₃ n₁ n₃ n₄₂ n₈₂ : ℕ)
    (hS₁ : S₁ = 8 * n₁) (hS₃ : S₃ = 8 * n₃)
    (hS₂ : S₂ = 4 * n₄₂ + 8 * n₈₂)
    (hn₄₂ : n₄₂ ≤ 1) (hcapacity : n₁ + n₃ + n₈₂ ≤ 5)
    (hsignature :
      (S₁ = 16 ∧ S₂ = 36 ∧ S₃ = 0) ∨
      (S₁ = 16 ∧ S₂ = 24 ∧ S₃ = 16) ∨
      (S₁ = 8 ∧ S₂ = 36 ∧ S₃ = 8) ∨
      (S₁ = 0 ∧ S₂ = 48 ∧ S₃ = 0) ∨
      (S₁ = 0 ∧ S₂ = 36 ∧ S₃ = 16) ∨
      (S₁ = 24 ∧ S₂ = 12 ∧ S₃ = 24)) : False := by
  rcases hsignature with h | h | h | h | h | h <;> omega

set_option maxHeartbeats 2000000 in
/-- The reduced `(24,24)` moment ledger has only six signatures once rows
of types one and three have weight divisible by eight and rows of type two
have weight divisible by four. -/
theorem twentyfour_twentyfour_weighted_row_signature
    (S₀ S₁ S₂ S₃ S₄ n₁ n₃ n₄₂ n₈₂ : ℕ)
    (hmass : S₀ + S₁ + S₂ + S₃ + S₄ = 60)
    (hedges : S₁ + 2 * S₂ + 3 * S₃ + 4 * S₄ = 120)
    (hcherries : S₂ + 3 * S₃ + 6 * S₄ = 84)
    (hS₁ : S₁ = 8 * n₁) (hS₃ : S₃ = 8 * n₃)
    (hS₂ : S₂ = 4 * n₄₂ + 8 * n₈₂) (hn₄₂ : n₄₂ ≤ 1) :
    (S₁ = 16 ∧ S₂ = 36 ∧ S₃ = 0) ∨
      (S₁ = 16 ∧ S₂ = 24 ∧ S₃ = 16) ∨
      (S₁ = 8 ∧ S₂ = 36 ∧ S₃ = 8) ∨
      (S₁ = 0 ∧ S₂ = 48 ∧ S₃ = 0) ∨
      (S₁ = 0 ∧ S₂ = 36 ∧ S₃ = 16) ∨
      (S₁ = 24 ∧ S₂ = 12 ∧ S₃ = 24) := by
  have hn₁ : n₁ ≤ 7 := by omega
  have hn₃ : n₃ ≤ 7 := by omega
  interval_cases n₁ <;> interval_cases n₃ <;> interval_cases n₄₂ <;> omega

/-- Finite-sum bookkeeping for the `(24,24)` row-order classification. -/
theorem twentyfour_twentyfour_weighted_count_decomposition
    {α : Type*} [DecidableEq α] (C : Finset α) (r q : α → ℕ)
    (hone : ∀ c ∈ C, q c = 1 → r c = 24)
    (htwo : ∀ c ∈ C, q c = 2 → r c = 12 ∨ r c = 24)
    (hthree : ∀ c ∈ C, q c = 3 → r c = 24) :
    let S := fun a : ℕ ↦ ∑ c ∈ C, if q c = a then r c / 3 else 0
    let n₁ := (C.filter fun c ↦ q c = 1).card
    let n₃ := (C.filter fun c ↦ q c = 3).card
    let n₄₂ := (C.filter fun c ↦ q c = 2 ∧ r c = 12).card
    let n₈₂ := (C.filter fun c ↦ q c = 2 ∧ r c = 24).card
    S 1 = 8 * n₁ ∧ S 3 = 8 * n₃ ∧ S 2 = 4 * n₄₂ + 8 * n₈₂ := by
  classical
  dsimp only
  let S := fun a : ℕ ↦ ∑ c ∈ C, if q c = a then r c / 3 else 0
  let n₁ := (C.filter fun c ↦ q c = 1).card
  let n₃ := (C.filter fun c ↦ q c = 3).card
  let n₄₂ := (C.filter fun c ↦ q c = 2 ∧ r c = 12).card
  let n₈₂ := (C.filter fun c ↦ q c = 2 ∧ r c = 24).card
  have hS₁ : S 1 = 8 * n₁ := by
    calc
      S 1 = ∑ c ∈ C, if q c = 1 then 8 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hq : q c = 1
        · rw [hone c hc hq]
        · simp [S, hq]
      _ = 8 * n₁ := by
        rw [← Finset.sum_filter]
        simp [n₁, Nat.mul_comm]
  have hS₃ : S 3 = 8 * n₃ := by
    calc
      S 3 = ∑ c ∈ C, if q c = 3 then 8 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hq : q c = 3
        · rw [hthree c hc hq]
        · simp [S, hq]
      _ = 8 * n₃ := by
        rw [← Finset.sum_filter]
        simp [n₃, Nat.mul_comm]
  have hS₂ : S 2 = 4 * n₄₂ + 8 * n₈₂ := by
    calc
      S 2 = ∑ c ∈ C, (
          (if q c = 2 ∧ r c = 12 then 4 else 0) +
            (if q c = 2 ∧ r c = 24 then 8 else 0)) := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hq : q c = 2
        · rcases htwo c hc hq with hr | hr <;> simp [S, hq, hr]
        · simp [S, hq]
      _ = 4 * n₄₂ + 8 * n₈₂ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
        simp [n₄₂, n₈₂, Nat.mul_comm]
  exact ⟨hS₁, hS₃, hS₂⟩

/-- Exact pair-ledger certificate for the last periodicity-feasible
three-component orphan partition `(12,12,24)`.  The variables enumerate the
seventeen possible reduced R-order/row types after periodicity.  The final
bound says that at most one order-12 source can be a one-neighbor cyclic
cover of the order-24 target. -/
theorem false_of_twelve_twelve_twentyfour_row_ledger
    (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ : ℕ)
    (hwithinTwelve :
      6*x₁ + x₂ + 2*x₅ + 12*x₆ + 6*x₈ + 2*x₁₀ = 9)
    (hwithinTwentyFour :
      3*x₀ + 6*x₄ + x₅ + x₇ + x₉ + 12*x₁₃ +
        6*x₁₄ + 6*x₁₅ + 2*x₁₆ = 21)
    (hcrossTwelve :
      2*x₂ + x₇ + 3*x₈ + 4*x₁₀ + 3*x₁₁ + 2*x₁₆ = 12)
    (hcrossFirstTwentyFour :
      x₇ + 2*x₉ + 3*x₁₅ + 2*x₁₆ = 12)
    (hcrossSecondTwentyFour :
      2*x₅ + x₇ + 3*x₁₄ + 2*x₁₆ = 12)
    (hcover : x₅ + x₇ + x₉ ≤ 1) : False := by
  have hx₅ : x₅ ≤ 1 := by omega
  have hx₇ : x₇ ≤ 1 := by omega
  have hx₉ : x₉ ≤ 1 := by omega
  interval_cases x₅ <;> interval_cases x₇ <;> interval_cases x₉ <;> omega

set_option maxHeartbeats 2000000 in
/-- The `(18,30)` balance equations leave a gap at forward masses one and
three.  Unlike the stronger parity claim, this statement is exact enough for
a bin of total forward mass three. -/
theorem eighteen_thirty_transport_entry_gap
    (r a c b d : ℕ) (hrLower : 3 ≤ r) (hrUpper : r ≤ 36)
    (hrThree : 3 ∣ r) (h₁ : 18*a = r*b) (h₂ : 30*c = r*d)
    (hrow : b + d = 4) : (0 < a → 2 ≤ a) ∧ a ≠ 3 := by
  obtain ⟨k, hk⟩ := hrThree
  have hb : b ≤ 4 := by omega
  have hd : d ≤ 4 := by omega
  interval_cases r <;> interval_cases b <;> interval_cases d <;> omega

/- Retired by the cold-build audit: numerically correct n=3 census, but the
original automation is not maintainably elaborable.  Restore with a compact proof.
-/
set_option maxHeartbeats 5000000 in
/-- The analogous forward-mass gap for the `(6,42)` balance equations. -/
theorem six_fortyTwo_transport_entry_gap
    (r a c b d : ℕ) (hrLower : 3 ≤ r) (hrUpper : r ≤ 36)
    (hrThree : 3 ∣ r) (h₁ : 6*a = r*b) (h₂ : 42*c = r*d)
    (hrow : b + d = 4) : (0 < a → 2 ≤ a) ∧ a ≠ 3 := by
  obtain ⟨k, hk⟩ := hrThree
  have hb : b ≤ 4 := by omega
  have hd : d ≤ 4 := by omega
  interval_cases r <;> interval_cases b <;> interval_cases d <;> omega

/-- A finite family of nonnegative masses cannot sum to three if every
positive mass is at least two and mass three itself is forbidden. -/
theorem false_of_sum_eq_three_of_gap_not_three
    {α : Type*} [DecidableEq α] (C : Finset α) (a : α → ℕ)
    (hsum : ∑ c ∈ C, a c = 3)
    (hgap : ∀ c ∈ C, 0 < a c → 2 ≤ a c)
    (hnot : ∀ c ∈ C, a c ≠ 3) : False := by
  have hne : ∑ c ∈ C, a c ≠ 0 := by omega
  obtain ⟨c, hc, hc0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hcPos : 0 < a c := Nat.pos_of_ne_zero hc0
  have hcLe : a c ≤ ∑ x ∈ C, a x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hc
  have hcTwo := hgap c hc hcPos
  have hcEq : a c = 2 := by
    have hcNe := hnot c hc
    omega
  have hrest : ∑ x ∈ C.erase c, a x = 1 := by
    have hsplit : (∑ x ∈ C.erase c, a x) + a c = ∑ x ∈ C, a x := by
      rw [Finset.sum_erase_add _ _ hc]
    rw [hsum, hcEq] at hsplit
    omega
  have hrestNe : ∑ x ∈ C.erase c, a x ≠ 0 := by omega
  obtain ⟨e, he, he0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrestNe
  have heC : e ∈ C := Finset.mem_of_mem_erase he
  have hePos : 0 < a e := Nat.pos_of_ne_zero he0
  have heTwo := hgap e heC hePos
  have heLe : a e ≤ ∑ x ∈ C.erase c, a x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) he
  omega

/-- Graph-level owner-bin contradiction for the `(18,30)` orphan pair. -/
theorem false_of_eighteen_thirty_transport_bin
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (ho₁ : o₁.supp.ncard = 18) (ho₂ : o₂.supp.ncard = 30)
    (E : Finset (secondOrderDefectGraph G).ConnectedComponent)
    (horder : ∀ e ∈ E, 3 ≤ e.supp.ncard ∧ e.supp.ncard ≤ 36 ∧
      3 ∣ e.supp.ncard)
    (hreverse : ∀ e ∈ E,
      componentQuotientMatrix G (secondOrderDefectGraph G) e o₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e o₂ = 4)
    (hforward : ∑ e ∈ E,
      componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e = 3) : False := by
  apply false_of_sum_eq_three_of_gap_not_three E
    (fun e => componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e)
    hforward
  · intro e he
    exact (eighteen_thirty_transport_entry_gap e.supp.ncard
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₂ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₂)
      (horder e he).1 (horder e he).2.1 (horder e he).2.2
      (by simpa [ho₁] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₁ e))
      (by simpa [ho₂] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₂ e))
      (hreverse e he)).1
  · intro e he
    exact (eighteen_thirty_transport_entry_gap e.supp.ncard
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₂ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₂)
      (horder e he).1 (horder e he).2.1 (horder e he).2.2
      (by simpa [ho₁] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₁ e))
      (by simpa [ho₂] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₂ e))
      (hreverse e he)).2

/-- Graph-level owner-bin contradiction for the `(6,42)` orphan pair. -/
theorem false_of_six_fortyTwo_transport_bin
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (ho₁ : o₁.supp.ncard = 6) (ho₂ : o₂.supp.ncard = 42)
    (E : Finset (secondOrderDefectGraph G).ConnectedComponent)
    (horder : ∀ e ∈ E, 3 ≤ e.supp.ncard ∧ e.supp.ncard ≤ 36 ∧
      3 ∣ e.supp.ncard)
    (hreverse : ∀ e ∈ E,
      componentQuotientMatrix G (secondOrderDefectGraph G) e o₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e o₂ = 4)
    (hforward : ∑ e ∈ E,
      componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e = 3) : False := by
  apply false_of_sum_eq_three_of_gap_not_three E
    (fun e => componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e)
    hforward
  · intro e he
    exact (six_fortyTwo_transport_entry_gap e.supp.ncard
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₂ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₂)
      (horder e he).1 (horder e he).2.1 (horder e he).2.2
      (by simpa [ho₁] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₁ e))
      (by simpa [ho₂] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₂ e))
      (hreverse e he)).1
  · intro e he
    exact (six_fortyTwo_transport_entry_gap e.supp.ncard
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₁ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) o₂ e)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁)
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o₂)
      (horder e he).1 (horder e he).2.1 (horder e he).2.2
      (by simpa [ho₁] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₁ e))
      (by simpa [ho₂] using (secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o₂ e))
      (hreverse e he)).2

/-- Extract the two named elements behind a two-part count vector.  This is
the bridge from filter-card census output to component-level eliminators. -/
theorem exists_distinct_pair_of_card_two_filter_counts
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ) (r s : ℕ)
    (hcard : C.card = 2)
    (hr : (C.filter fun c => w c = r).card = 1)
    (hs : (C.filter fun c => w c = s).card = 1)
    (hrs : r ≠ s) :
    ∃ c d, c ≠ d ∧ c ∈ C ∧ d ∈ C ∧ w c = r ∧ w d = s ∧ C = {c, d} := by
  classical
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hr
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hs
  have hcMemFilter : c ∈ C.filter fun x => w x = r := by simp [hc]
  have hdMemFilter : d ∈ C.filter fun x => w x = s := by simp [hd]
  have hcData := Finset.mem_filter.mp hcMemFilter
  have hdData := Finset.mem_filter.mp hdMemFilter
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hrs (hcData.2.symm.trans hdData.2)
  have hsubset : {c, d} ⊆ C := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hcData.1
    · exact hdData.1
  have hpair : C = {c, d} := by
    exact (Finset.eq_of_subset_of_card_le hsubset (by simp [hcard, hcd])).symm
  exact ⟨c, d, hcd, hcData.1, hdData.1, hcData.2, hdData.2, hpair⟩

set_option maxHeartbeats 5000000 in
/-- Elimination-oriented finset form of the two-part census: it names both
elements and identifies their unordered weight pair. -/
theorem two_part_three_divisible_named_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 2) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c)
    (heven₉ : Even (C.filter fun c => w c = 9).card)
    (heven₁₅ : Even (C.filter fun c => w c = 15).card)
    (heven₂₁ : Even (C.filter fun c => w c = 21).card)
    (heven₂₇ : Even (C.filter fun c => w c = 27).card)
    (heven₃₃ : Even (C.filter fun c => w c = 33).card)
    (heven₃₉ : Even (C.filter fun c => w c = 39).card) :
    ∃ c d, c ≠ d ∧ C = {c, d} ∧
      ((w c = 6 ∧ w d = 42) ∨ (w c = 42 ∧ w d = 6) ∨
       (w c = 12 ∧ w d = 36) ∨ (w c = 36 ∧ w d = 12) ∨
       (w c = 18 ∧ w d = 30) ∨ (w c = 30 ∧ w d = 18) ∨
       (w c = 24 ∧ w d = 24)) := by
  classical
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hcard
  have hcMem : c ∈ ({c, d} : Finset α) := by simp
  have hdMem : d ∈ ({c, d} : Finset α) := by simp
  have hcLower := hlower c hcMem
  have hdLower := hlower d hdMem
  obtain ⟨kc, hkc⟩ := hthree c hcMem
  obtain ⟨kd, hkd⟩ := hthree d hdMem
  refine ⟨c, d, hcd, rfl, ?_⟩
  simp [hcd] at hsum
  have hkcLower : 2 ≤ kc := by omega
  have hkdLower : 2 ≤ kd := by omega
  have hkcUpper : kc ≤ 14 := by omega
  have hkdUpper : kd ≤ 14 := by omega
  have hkdEq : kd = 16 - kc := by omega
  subst kd
  interval_cases kc <;>
    simp [Finset.filter_insert, Finset.filter_singleton, hkc, hkd,
      even_iff_two_dvd] at heven₉ heven₁₅ heven₂₁ heven₂₇ heven₃₃ heven₃₉ ⊢

/-- Five three-divisible parts of total forty-eight, each at least nine,
are four nines and one twelve.  This compact excess argument replaces the
retired five-part count-vector census after order-six orphans are excluded. -/
theorem five_part_nine_or_twelve_unique_twelve
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 5) (hsum : ∑ c ∈ C, w c = 48)
    (hnine : ∀ c ∈ C, 9 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c) :
    (∀ c ∈ C, w c = 9 ∨ w c = 12) ∧
      (C.filter fun c => w c = 12).card = 1 := by
  have horders : ∀ c ∈ C, w c = 9 ∨ w c = 12 := by
    intro c hc
    have hrest : 9 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
      calc
        9 * (C.erase c).card = ∑ _d ∈ C.erase c, 9 := by simp [mul_comm]
        _ ≤ ∑ d ∈ C.erase c, w d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hnine d (Finset.mem_of_mem_erase hd)
    have hcardErase : (C.erase c).card = 4 := by
      rw [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add C w hc
    obtain ⟨k, hk⟩ := hthree c hc
    have hcLower := hnine c hc
    omega
  refine ⟨horders, ?_⟩
  let n₁₂ := (C.filter fun c => w c = 12).card
  have hindicator : (∑ c ∈ C, if w c = 12 then 3 else 0) = 3 * n₁₂ := by
    rw [← Finset.sum_filter]
    simp [n₁₂, mul_comm]
  have hmass : (∑ c ∈ C, w c) = 9 * C.card + 3 * n₁₂ := by
    calc
      (∑ c ∈ C, w c) = ∑ c ∈ C, (9 + if w c = 12 then 3 else 0) := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h <;> simp [h]
      _ = 9 * C.card + 3 * n₁₂ := by
        rw [Finset.sum_add_distrib, hindicator]
        simp [mul_comm]
  change n₁₂ = 1
  omega

/- Retired n=3 census automation.
set_option maxHeartbeats 5000000 in
/-- Exact count-vector classification for three three-divisible parts of
total forty-eight, each at least six, with even odd-order multiplicities. -/
theorem three_part_three_divisible_count_vector_classification
    (n₆ n₉ n₁₂ n₁₅ n₁₈ n₂₁ n₂₄ n₂₇ n₃₀ n₃₃ n₃₆ : ℕ)
    (hcount : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ + n₂₇ +
      n₃₀ + n₃₃ + n₃₆ = 3)
    (hmass : 6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ + 21*n₂₁ +
      24*n₂₄ + 27*n₂₇ + 30*n₃₀ + 33*n₃₃ + 36*n₃₆ = 48)
    (heven₉ : Even n₉) (heven₁₅ : Even n₁₅) (heven₂₁ : Even n₂₁)
    (heven₂₇ : Even n₂₇) (heven₃₃ : Even n₃₃) :
    (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧
      n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 1) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧
      n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧
      n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧
      n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧
      n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 2 ∧
      n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 2 ∧ n₂₁ = 0 ∧
      n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧
      n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) := by
  obtain ⟨k₉, hk₉⟩ := heven₉
  obtain ⟨k₁₅, hk₁₅⟩ := heven₁₅
  obtain ⟨k₂₁, hk₂₁⟩ := heven₂₁
  obtain ⟨k₂₇, hk₂₇⟩ := heven₂₇
  obtain ⟨k₃₃, hk₃₃⟩ := heven₃₃
  have hexcess : n₉ + 2*n₁₂ + 3*n₁₅ + 4*n₁₈ + 5*n₂₁ +
      6*n₂₄ + 7*n₂₇ + 8*n₃₀ + 9*n₃₃ + 10*n₃₆ = 10 := by omega
  have hn₂₇ : n₂₇ = 0 := by omega
  have hn₃₃ : n₃₃ = 0 := by omega
  have hn₉Cases : n₉ = 0 ∨ n₉ = 2 := by omega
  have hn₁₂Cases : n₁₂ = 0 ∨ n₁₂ = 1 ∨ n₁₂ = 2 ∨ n₁₂ = 3 := by omega
  have hn₁₅Cases : n₁₅ = 0 ∨ n₁₅ = 2 := by omega
  have hn₁₈Cases : n₁₈ = 0 ∨ n₁₈ = 1 ∨ n₁₈ = 2 := by omega
  have hn₂₁Cases : n₂₁ = 0 ∨ n₂₁ = 2 := by omega
  have hn₂₄Cases : n₂₄ = 0 ∨ n₂₄ = 1 ∨ n₂₄ = 2 := by omega
  have hn₃₀Cases : n₃₀ = 0 ∨ n₃₀ = 1 := by omega
  have hn₃₆Cases : n₃₆ = 0 ∨ n₃₆ = 1 := by omega
  rcases hn₃₆Cases with h₃₆ | h₃₆ <;> try omega
  all_goals rcases hn₃₀Cases with h₃₀ | h₃₀ <;> try omega
  all_goals rcases hn₂₄Cases with h₂₄ | h₂₄ | h₂₄ <;> try omega
  all_goals rcases hn₂₁Cases with h₂₁ | h₂₁ <;> try omega
  all_goals rcases hn₁₈Cases with h₁₈ | h₁₈ | h₁₈ <;> try omega
  all_goals rcases hn₁₅Cases with h₁₅ | h₁₅ <;> try omega
  all_goals rcases hn₁₂Cases with h₁₂ | h₁₂ | h₁₂ | h₁₂ <;> try omega
  all_goals rcases hn₉Cases with h₉ | h₉ <;> omega

set_option maxHeartbeats 2000000 in
/-- Finset form of the exact three-part, three-divisible count census. -/
theorem three_part_three_divisible_count_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 3) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c)
    (heven₉ : Even (C.filter fun c => w c = 9).card)
    (heven₁₅ : Even (C.filter fun c => w c = 15).card)
    (heven₂₁ : Even (C.filter fun c => w c = 21).card)
    (heven₂₇ : Even (C.filter fun c => w c = 27).card)
    (heven₃₃ : Even (C.filter fun c => w c = 33).card) :
    let n₆ := (C.filter fun c => w c = 6).card
    let n₉ := (C.filter fun c => w c = 9).card
    let n₁₂ := (C.filter fun c => w c = 12).card
    let n₁₅ := (C.filter fun c => w c = 15).card
    let n₁₈ := (C.filter fun c => w c = 18).card
    let n₂₁ := (C.filter fun c => w c = 21).card
    let n₂₄ := (C.filter fun c => w c = 24).card
    let n₂₇ := (C.filter fun c => w c = 27).card
    let n₃₀ := (C.filter fun c => w c = 30).card
    let n₃₃ := (C.filter fun c => w c = 33).card
    let n₃₆ := (C.filter fun c => w c = 36).card
    (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 1) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 2 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 2 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) := by
  classical
  dsimp only
  let n₆ := (C.filter fun c => w c = 6).card
  let n₉ := (C.filter fun c => w c = 9).card
  let n₁₂ := (C.filter fun c => w c = 12).card
  let n₁₅ := (C.filter fun c => w c = 15).card
  let n₁₈ := (C.filter fun c => w c = 18).card
  let n₂₁ := (C.filter fun c => w c = 21).card
  let n₂₄ := (C.filter fun c => w c = 24).card
  let n₂₇ := (C.filter fun c => w c = 27).card
  let n₃₀ := (C.filter fun c => w c = 30).card
  let n₃₃ := (C.filter fun c => w c = 33).card
  let n₃₆ := (C.filter fun c => w c = 36).card
  have horders : ∀ c ∈ C, w c = 6 ∨ w c = 9 ∨ w c = 12 ∨ w c = 15 ∨
      w c = 18 ∨ w c = 21 ∨ w c = 24 ∨ w c = 27 ∨ w c = 30 ∨
      w c = 33 ∨ w c = 36 := by
    intro c hc
    have hrest : 6 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
      calc
        6 * (C.erase c).card = ∑ _d ∈ C.erase c, 6 := by simp [mul_comm]
        _ ≤ ∑ d ∈ C.erase c, w d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hlower d (Finset.mem_of_mem_erase hd)
    have hcardErase : (C.erase c).card = 2 := by
      rw [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add C w hc
    have hcLower := hlower c hc
    obtain ⟨k, hk⟩ := hthree c hc
    omega
  have hcountEq : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ + n₂₇ +
      n₃₀ + n₃₃ + n₃₆ = 3 := by
    calc
      n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ + n₂₇ + n₃₀ + n₃₃ + n₃₆ =
          ∑ c ∈ C, ((if w c = 6 then 1 else 0) + (if w c = 9 then 1 else 0) +
            (if w c = 12 then 1 else 0) + (if w c = 15 then 1 else 0) +
            (if w c = 18 then 1 else 0) + (if w c = 21 then 1 else 0) +
            (if w c = 24 then 1 else 0) + (if w c = 27 then 1 else 0) +
            (if w c = 30 then 1 else 0) + (if w c = 33 then 1 else 0) +
            (if w c = 36 then 1 else 0)) := by
              simp [n₆, n₉, n₁₂, n₁₅, n₁₈, n₂₁, n₂₄, n₂₇, n₃₀, n₃₃, n₃₆,
                Finset.sum_add_distrib]
      _ = ∑ _c ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
      _ = 3 := by simp [hcard]
  have hmass (a : ℕ) : a * (C.filter fun c => w c = a).card =
      ∑ c ∈ C, if w c = a then a else 0 := by
    calc
      a * (C.filter fun c => w c = a).card =
          (C.filter fun c => w c = a).card * a := Nat.mul_comm _ _
      _ = ∑ _c ∈ C.filter (fun c => w c = a), a := by simp
      _ = ∑ c ∈ C, if w c = a then a else 0 := by rw [Finset.sum_filter]
  have hmassEq : 6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ + 21*n₂₁ +
      24*n₂₄ + 27*n₂₇ + 30*n₃₀ + 33*n₃₃ + 36*n₃₆ = 48 := by
    calc
      6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ + 21*n₂₁ + 24*n₂₄ + 27*n₂₇ + 30*n₃₀ + 33*n₃₃ + 36*n₃₆ =
          ∑ c ∈ C, ((if w c = 6 then 6 else 0) + (if w c = 9 then 9 else 0) +
            (if w c = 12 then 12 else 0) + (if w c = 15 then 15 else 0) +
            (if w c = 18 then 18 else 0) + (if w c = 21 then 21 else 0) +
            (if w c = 24 then 24 else 0) + (if w c = 27 then 27 else 0) +
            (if w c = 30 then 30 else 0) + (if w c = 33 then 33 else 0) +
            (if w c = 36 then 36 else 0)) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← hmass 6, ← hmass 9, ← hmass 12, ← hmass 15, ← hmass 18,
                ← hmass 21, ← hmass 24, ← hmass 27, ← hmass 30, ← hmass 33,
                ← hmass 36]
      _ = ∑ c ∈ C, w c := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
      _ = 48 := hsum
  change Even n₉ at heven₉
  change Even n₁₅ at heven₁₅
  change Even n₂₁ at heven₂₁
  change Even n₂₇ at heven₂₇
  change Even n₃₃ at heven₃₃
  exact three_part_three_divisible_count_vector_classification
    n₆ n₉ n₁₂ n₁₅ n₁₈ n₂₁ n₂₄ n₂₇ n₃₀ n₃₃ n₃₆ hcountEq hmassEq
      heven₉ heven₁₅ heven₂₁ heven₂₇ heven₃₃
-/

/-- In the symmetric `(12,12,12,12)` orphan branch, each order-12 target
needs `54` internal cherries.  All periodic row types contribute a multiple
of `12` except an order-6 double-cover row, which contributes `6`; cover
uniqueness bounds the number of the latter by one.  Thus every target sees
exactly one such row, and the four incidences come from exactly two rows. -/
theorem four_twelve_cycles_force_two_orderSix_doubleCovers
    (b₀ b₁ b₂ b₃ n t₀ t₁ t₂ t₃ : ℕ)
    (hb₀ : b₀ ≤ 1) (hb₁ : b₁ ≤ 1) (hb₂ : b₂ ≤ 1) (hb₃ : b₃ ≤ 1)
    (h₀ : 6*b₀ + 12*t₀ = 54) (h₁ : 6*b₁ + 12*t₁ = 54)
    (h₂ : 6*b₂ + 12*t₂ = 54) (h₃ : 6*b₃ + 12*t₃ = 54)
    (hincidence : b₀ + b₁ + b₂ + b₃ = 2*n) :
    b₀ = 1 ∧ b₁ = 1 ∧ b₂ = 1 ∧ b₃ = 1 ∧ n = 2 := by
  omega

/-- Two order-six source rows which each spend one double-cover incidence
among three order-twelve targets must share a target as soon as every target
receives an even number of those incidences.  In the four-layer residual the
evenness is the target cherry ledger modulo twelve: the two order-six rows
contribute six cherries apiece, while every order-twelve row contributes a
multiple of twelve. -/
theorem two_unit_rows_three_even_columns_share
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℕ)
    (ha : a₀ + a₁ + a₂ = 1) (hb : b₀ + b₁ + b₂ = 1)
    (h₀ : Even (a₀ + b₀)) (h₁ : Even (a₁ + b₁))
    (h₂ : Even (a₂ + b₂)) :
    (a₀ = 1 ∧ b₀ = 1) ∨ (a₁ = 1 ∧ b₁ = 1) ∨
      (a₂ = 1 ∧ b₂ = 1) := by
  obtain ⟨k₀, hk₀⟩ := h₀
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  omega

/-- Contradiction form used after applying double-cover target uniqueness:
if no target can receive both unit incidences, the two even-column unit rows
cannot exist. -/
theorem false_of_two_unit_rows_three_even_columns_no_shared
    (a₀ a₁ a₂ b₀ b₁ b₂ : ℕ)
    (ha : a₀ + a₁ + a₂ = 1) (hb : b₀ + b₁ + b₂ = 1)
    (h₀ : Even (a₀ + b₀)) (h₁ : Even (a₁ + b₁))
    (h₂ : Even (a₂ + b₂))
    (hno₀ : a₀ = 1 → b₀ ≠ 1) (hno₁ : a₁ = 1 → b₁ ≠ 1)
    (hno₂ : a₂ = 1 → b₂ ≠ 1) : False := by
  rcases two_unit_rows_three_even_columns_share
      a₀ a₁ a₂ b₀ b₁ b₂ ha hb h₀ h₁ h₂ with h | h | h
  · exact hno₀ h.1 h.2
  · exact hno₁ h.1 h.2
  · exact hno₂ h.1 h.2

/-- Parity extraction from a finite local-excess ledger.  If the total is
nine, one distinguished owner term is three, and every term other than two
named exceptions and the owner is even, then the two exceptional terms have
even sum.  This is the abstract bookkeeping step behind the order-twelve
target column parity in the four-layer branch. -/
theorem even_two_exceptions_of_sum_eq_nine_owner_eq_three
    {C : Type*} [Fintype C] [DecidableEq C]
    (T : C → ℤ) (u c₁ c₂ : C)
    (huc₁ : u ≠ c₁) (huc₂ : u ≠ c₂) (hc₁c₂ : c₁ ≠ c₂)
    (hsum : ∑ c, T c = 9) (hu : T u = 3)
    (hrest : ∀ c, c ≠ u → c ≠ c₁ → c ≠ c₂ → Even (T c)) :
    Even (T c₁ + T c₂) := by
  let S₁ := (Finset.univ : Finset C).erase u
  let S₂ := S₁.erase c₁
  let S₃ := S₂.erase c₂
  have hc₁S₁ : c₁ ∈ S₁ := by
    simp [S₁, huc₁.symm]
  have hc₂S₂ : c₂ ∈ S₂ := by
    simp [S₂, S₁, huc₂.symm, hc₁c₂.symm]
  have hsplitu := Finset.sum_erase_add
    (Finset.univ : Finset C) T (Finset.mem_univ u)
  have hsplitc₁ := Finset.sum_erase_add S₁ T hc₁S₁
  have hsplitc₂ := Finset.sum_erase_add S₂ T hc₂S₂
  have hS₃even : Even (∑ c ∈ S₃, T c) := by
    rw [even_iff_two_dvd]
    apply Finset.dvd_sum
    intro c hc
    rw [Finset.mem_erase] at hc
    have hcS₂ := hc.2
    rw [Finset.mem_erase] at hcS₂
    have hcS₁ := hcS₂.2
    rw [Finset.mem_erase] at hcS₁
    exact even_iff_two_dvd.mp
      (hrest c hcS₁.1 hcS₂.1 hc.1)
  obtain ⟨k, hk⟩ := hS₃even
  dsimp only [S₁, S₂, S₃] at hsplitu hsplitc₁ hsplitc₂ hk
  obtain ⟨m, hm⟩ : Even (T c₁ + T c₂) := by
    refine ⟨3 - k, ?_⟩
    rw [hu] at hsplitu
    omega
  exact ⟨m, hm⟩

/-- Graph-facing local-excess parity for an order-twelve target with two
order-six exceptions.  Apart from the target's owner component, every other
component is assumed either to have order twelve or to have zero quotient
from the target.  Equal-order terms are products of consecutive integers;
the owner contributes three; balance identifies each order-six term modulo
two with its reverse quotient. -/
theorem degree_sixteen_orderTwelve_two_orderSix_column_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e u c₁ c₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (huc₁ : u ≠ c₁) (huc₂ : u ≠ c₂) (hc₁c₂ : c₁ ≠ c₂)
    (he : e.supp.ncard = 12) (hc₁ : c₁.supp.ncard = 6)
    (hc₂ : c₂.supp.ncard = 6)
    (heu : componentQuotientMatrix G (secondOrderDefectGraph G) e u = 1)
    (hue : componentQuotientMatrix G (secondOrderDefectGraph G) u e = 4)
    (hrest : ∀ f, f ≠ u → f ≠ c₁ → f ≠ c₂ →
      f.supp.ncard = 12 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) e f = 0) :
    Even (componentQuotientMatrix G (secondOrderDefectGraph G) e c₁ +
      componentQuotientMatrix G (secondOrderDefectGraph G) e c₂) := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let T : D.ConnectedComponent → ℤ := fun f =>
    (Q e f : ℤ) * (Q f e : ℤ) - (Q e f : ℤ)
  have hsum : ∑ f, T f = 9 := by
    have hlocal := secondOrder_componentQuotientMatrix_local_excess
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e
    change (∑ f, T f) = _
    rw [hlocal, he]
    norm_num
  have hu : T u = 3 := by
    simp [T, Q, D, heu, hue]
  have hrestEven : ∀ f, f ≠ u → f ≠ c₁ → f ≠ c₂ → Even (T f) := by
    intro f hfu hfc₁ hfc₂
    rcases hrest f hfu hfc₁ hfc₂ with hf | hzero
    · have hbal := secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e f
      rw [he, hf] at hbal
      have hsym : Q e f = Q f e := by
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 12) hbal
      dsimp only [T]
      rw [hsym]
      have hev := Int.even_mul_pred_self (Q f e : ℤ)
      convert hev using 1 <;> ring
    · simp [T, Q, D, hzero]
  have hTexceptions := even_two_exceptions_of_sum_eq_nine_owner_eq_three
    T u c₁ c₂ huc₁ huc₂ hc₁c₂ hsum hu hrestEven
  have hbal₁ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₁ e
  have hbal₂ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₂ e
  have hq₁ : Q c₁ e = 2 * Q e c₁ := by
    rw [hc₁, he] at hbal₁
    have hq : componentQuotientMatrix G (secondOrderDefectGraph G) c₁ e =
        2 * componentQuotientMatrix G (secondOrderDefectGraph G) e c₁ := by
      omega
    simpa [Q, D] using hq
  have hq₂ : Q c₂ e = 2 * Q e c₂ := by
    rw [hc₂, he] at hbal₂
    have hq : componentQuotientMatrix G (secondOrderDefectGraph G) c₂ e =
        2 * componentQuotientMatrix G (secondOrderDefectGraph G) e c₂ := by
      omega
    simpa [Q, D] using hq
  obtain ⟨k, hk⟩ := hTexceptions
  dsimp only [T] at hk
  rw [hq₁, hq₂] at hk
  have hevenZ : Even ((Q e c₁ : ℤ) + (Q e c₂ : ℤ)) := by
    refine ⟨k - (Q e c₁ : ℤ) * ((Q e c₁ : ℤ) - 1) -
        (Q e c₂ : ℤ) * ((Q e c₂ : ℤ) - 1), ?_⟩
    push_cast at hk
    nlinarith
  rw [even_iff_two_dvd]
  have hdvdZ : (2 : ℤ) ∣ (Q e c₁ : ℤ) + (Q e c₂ : ℤ) :=
    even_iff_two_dvd.mp hevenZ
  exact_mod_cast hdvdZ

/-- An order-six component which spends total quotient degree two into three
order-twelve targets has reverse quotient mass one across those targets.
This is detailed balance divided by the common size ratio two, and supplies
the unit-row hypotheses of the four-layer collision capstone. -/
theorem degree_sixteen_orderSix_three_orderTwelve_reverse_sum_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c e₀ e₁ e₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 6) (he₀ : e₀.supp.ncard = 12)
    (he₁ : e₁.supp.ncard = 12) (he₂ : e₂.supp.ncard = 12)
    (hforward :
      componentQuotientMatrix G (secondOrderDefectGraph G) c e₀ +
        componentQuotientMatrix G (secondOrderDefectGraph G) c e₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) c e₂ = 2) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c = 1 := by
  have hbal₀ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e₀
  have hbal₁ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e₁
  have hbal₂ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e₂
  rw [hc, he₀] at hbal₀
  rw [hc, he₁] at hbal₁
  rw [hc, he₂] at hbal₂
  omega

/-- Divisibility extraction from the local-excess identity.  If every local
quotient interaction term of a defect component is divisible by three, then
the component order is divisible by three as well, because their sum is
`|c| - 3`.  This is the arithmetic core of the per-orphan divisibility
wrapper in the four-layer branch. -/
theorem degree_sixteen_component_card_dvd_three_of_localExcess_terms
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hterms : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      (3 : ℤ) ∣
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
            (componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ) -
          (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ)) :
    3 ∣ c.supp.ncard := by
  have hsumDvd : (3 : ℤ) ∣
      ∑ e, ((componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          (componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ) -
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ)) := by
    apply Finset.dvd_sum
    intro e _he
    exact hterms e
  rw [secondOrder_componentQuotientMatrix_local_excess
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c] at hsumDvd
  obtain ⟨k, hk⟩ := hsumDvd
  have hcast : (c.supp.ncard : ℤ) = 3 * (k + 1) := by omega
  have hdvdZ : (3 : ℤ) ∣ (c.supp.ncard : ℤ) := ⟨k + 1, hcast⟩
  exact_mod_cast hdvdZ

/-- Equal-sized component blocks of quotient degree at most one contribute
zero to the local-excess sum.  Detailed balance makes the reverse quotient
equal to the forward quotient, and the latter is zero or one.  This packages
the orphan-matching contribution in the four-layer divisibility proof. -/
theorem degree_sixteen_equalSize_localExcess_term_eq_zero_of_quotient_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hsize : c.supp.ncard = e.supp.ncard)
    (hle : componentQuotientMatrix G (secondOrderDefectGraph G) c e ≤ 1) :
    (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) *
          (componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ) -
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ) = 0 := by
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e
  rw [hsize] at hbal
  have hpos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
  have hsym : componentQuotientMatrix G (secondOrderDefectGraph G) c e =
      componentQuotientMatrix G (secondOrderDefectGraph G) e c :=
    Nat.eq_of_mul_eq_mul_left hpos hbal
  rw [← hsym]
  interval_cases componentQuotientMatrix G (secondOrderDefectGraph G) c e <;>
    norm_num

/-- Classification-driven per-component divisibility wrapper.  If every
target block is either absent, an equal-sized matching block of degree at
most one, or belongs to a component whose order is divisible by three, then
the source component itself has order divisible by three.  In the four-layer
orphan cell these alternatives are respectively unequal orphan components,
equal orphan components, and minimum/used components. -/
theorem degree_sixteen_component_card_dvd_three_of_zero_equal_or_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hclass : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 ∨
        (c.supp.ncard = e.supp.ncard ∧
          componentQuotientMatrix G (secondOrderDefectGraph G) c e ≤ 1) ∨
        3 ∣ e.supp.ncard) :
    3 ∣ c.supp.ncard := by
  by_contra hc
  apply hc
  apply degree_sixteen_component_card_dvd_three_of_localExcess_terms
    G hfree hmin hcard c
  intro e
  rcases hclass e with hzero | hequal | hthree
  · simp [hzero]
  · have hterm :=
      degree_sixteen_equalSize_localExcess_term_eq_zero_of_quotient_le_one
        G hfree hmin hcard c e hequal.1 hequal.2
    rw [hterm]
    exact dvd_zero 3
  · have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e c
    obtain ⟨k, hk⟩ := hthree
    have hdvdProd : 3 ∣ c.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
      rw [← hbal, hk]
      simpa [mul_assoc] using dvd_mul_right 3
        (k * componentQuotientMatrix G (secondOrderDefectGraph G) e c)
    have hp : Nat.Prime 3 := by norm_num
    have hdvd : 3 ∣ componentQuotientMatrix G
        (secondOrderDefectGraph G) c e :=
      (hp.dvd_mul.mp hdvdProd).resolve_left hc
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨(k : ℤ) *
        ((componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℤ) - 1), ?_⟩
    rw [hk]
    push_cast
    ring

/-- The orders of the defect components selected by a component-closed
finite vertex cell sum to the cardinality of that cell.  This is the generic
bridge from the graph partition to the finite integer partition used below. -/
theorem sum_component_sizes_filter_eq_card_of_component_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (S : Finset V)
    (hclosed : ∀ (c : D.ConnectedComponent) (z : V), z ∈ c.supp →
      (z ∈ S ↔ componentRepresentative D c ∈ S)) :
    (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ S), c.supp.ncard) = S.card := by
  classical
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ S)
  let F := fun c : D.ConnectedComponent => c.supp.toFinite.toFinset
  have hpair : (↑C : Set D.ConnectedComponent).PairwiseDisjoint F := by
    intro c hc e he hce
    change Disjoint (F c) (F e)
    rw [Finset.disjoint_left]
    intro z hzc hze
    have hzc' : z ∈ c.supp := by simpa [F] using hzc
    have hze' : z ∈ e.supp := by simpa [F] using hze
    have hcz : D.connectedComponentMk z = c :=
      (ConnectedComponent.mem_supp_iff c z).mp hzc'
    have hez : D.connectedComponentMk z = e :=
      (ConnectedComponent.mem_supp_iff e z).mp hze'
    exact hce (hcz.symm.trans hez)
  have hunion : C.biUnion F = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨c, hcC, hzc⟩ := Finset.mem_biUnion.mp hz
      have hrep : componentRepresentative D c ∈ S :=
        (Finset.mem_filter.mp hcC).2
      have hzSupp : z ∈ c.supp := by simpa [F] using hzc
      exact (hclosed c z hzSupp).mpr hrep
    · intro hzS
      let c := D.connectedComponentMk z
      have hzc : z ∈ c.supp := by simp [c]
      have hrep : componentRepresentative D c ∈ S :=
        (hclosed c z hzc).mp hzS
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrep⟩, ?_⟩
      simpa [F] using hzc
  calc
    (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
        componentRepresentative D c ∈ S), c.supp.ncard) =
        ∑ c ∈ C, (F c).card := by
          apply Finset.sum_congr rfl
          intro c hc
          simpa [C, F] using
            (Set.ncard_eq_toFinset_card c.supp c.supp.toFinite)
    _ = (C.biUnion F).card := (Finset.card_biUnion hpair).symm
    _ = S.card := congrArg Finset.card hunion

/-- A weighted form of `sum_component_sizes_filter_eq_card_of_component_closed`:
any function constant on defect components may be summed either once per
vertex or as component order times the component weight. -/
theorem sum_component_sizes_mul_filter_eq_sum_of_component_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (S : Finset V)
    (hclosed : ∀ (c : D.ConnectedComponent) (z : V), z ∈ c.supp →
      (z ∈ S ↔ componentRepresentative D c ∈ S))
    (f : D.ConnectedComponent → ℕ) :
    (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent ↦
      componentRepresentative D c ∈ S), c.supp.ncard * f c) =
      ∑ z ∈ S, f (D.connectedComponentMk z) := by
  classical
  let C := Finset.univ.filter (fun c : D.ConnectedComponent ↦
    componentRepresentative D c ∈ S)
  let F := fun c : D.ConnectedComponent ↦ c.supp.toFinite.toFinset
  have hpair : (↑C : Set D.ConnectedComponent).PairwiseDisjoint F := by
    intro c hc e he hce
    change Disjoint (F c) (F e)
    rw [Finset.disjoint_left]
    intro z hzc hze
    have hzc' : z ∈ c.supp := by simpa [F] using hzc
    have hze' : z ∈ e.supp := by simpa [F] using hze
    have hcz : D.connectedComponentMk z = c :=
      (ConnectedComponent.mem_supp_iff c z).mp hzc'
    have hez : D.connectedComponentMk z = e :=
      (ConnectedComponent.mem_supp_iff e z).mp hze'
    exact hce (hcz.symm.trans hez)
  have hunion : C.biUnion F = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨c, hcC, hzc⟩ := Finset.mem_biUnion.mp hz
      have hrep : componentRepresentative D c ∈ S :=
        (Finset.mem_filter.mp hcC).2
      have hzSupp : z ∈ c.supp := by simpa [F] using hzc
      exact (hclosed c z hzSupp).mpr hrep
    · intro hzS
      let c := D.connectedComponentMk z
      have hzc : z ∈ c.supp := by simp [c]
      have hrep : componentRepresentative D c ∈ S :=
        (hclosed c z hzc).mp hzS
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrep⟩, ?_⟩
      simpa [F] using hzc
  calc
    (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent ↦
        componentRepresentative D c ∈ S), c.supp.ncard * f c) =
        ∑ c ∈ C, c.supp.ncard * f c := rfl
    _ = ∑ c ∈ C, ∑ z ∈ F c, f (D.connectedComponentMk z) := by
      apply Finset.sum_congr rfl
      intro c hc
      have hmk : ∀ z ∈ F c, D.connectedComponentMk z = c := by
        intro z hz
        apply (ConnectedComponent.mem_supp_iff c z).mp
        simpa [F] using hz
      rw [Finset.sum_congr rfl (fun z hz ↦ congrArg f (hmk z hz))]
      have hcardF : c.supp.ncard = (F c).card := by
        simpa [F] using
          (Set.ncard_eq_toFinset_card c.supp c.supp.toFinite)
      simp [hcardF]
    _ = ∑ z ∈ C.biUnion F, f (D.connectedComponentMk z) :=
      (Finset.sum_biUnion hpair).symm
    _ = ∑ z ∈ S, f (D.connectedComponentMk z) := by rw [hunion]

/-- Summing a component-quotient row over a component-closed vertex cell
counts exactly the source representative's neighbors in that cell. -/
theorem sum_componentQuotient_filter_eq_inter_neighbor_card_of_component_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (S : Finset V)
    (hclosed : ∀ y : V,
      y ∈ S ↔ componentRepresentative D (D.connectedComponentMk y) ∈ S)
    (c : D.ConnectedComponent) :
    (∑ e ∈ Finset.univ.filter (fun e : D.ConnectedComponent =>
      componentRepresentative D e ∈ S), componentQuotientMatrix G D c e) =
      (S ∩ G.neighborFinset (componentRepresentative D c)).card := by
  classical
  let C := Finset.univ.filter (fun e : D.ConnectedComponent =>
    componentRepresentative D e ∈ S)
  let F := fun e : D.ConnectedComponent =>
    componentNeighborFinset G D e (componentRepresentative D c)
  have hpair : (↑C : Set D.ConnectedComponent).PairwiseDisjoint F := by
    intro e he f hf hef
    change Disjoint (F e) (F f)
    rw [Finset.disjoint_left]
    intro y hye hyf
    have hye' := (Finset.mem_filter.mp hye).2
    have hyf' := (Finset.mem_filter.mp hyf).2
    exact hef (hye'.symm.trans hyf')
  have hunion : C.biUnion F = S ∩ G.neighborFinset (componentRepresentative D c) := by
    ext y
    constructor
    · intro hy
      obtain ⟨e, heC, hye⟩ := Finset.mem_biUnion.mp hy
      have heRep : componentRepresentative D e ∈ S := (Finset.mem_filter.mp heC).2
      have hyeData := Finset.mem_filter.mp hye
      have hcomp : D.connectedComponentMk y = e := hyeData.2
      exact Finset.mem_inter.mpr
        ⟨(hclosed y).mpr (by simpa [hcomp] using heRep), hyeData.1⟩
    · intro hy
      have hyData := Finset.mem_inter.mp hy
      let e := D.connectedComponentMk y
      apply Finset.mem_biUnion.mpr
      refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hclosed y).mp hyData.1⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hyData.2, rfl⟩
  calc
    (∑ e ∈ Finset.univ.filter (fun e : D.ConnectedComponent =>
        componentRepresentative D e ∈ S), componentQuotientMatrix G D c e) =
        ∑ e ∈ C, (F e).card := by rfl
    _ = (C.biUnion F).card := (Finset.card_biUnion hpair).symm
    _ = (S ∩ G.neighborFinset (componentRepresentative D c)).card :=
      congrArg Finset.card hunion

/-- A partition of mass forty-eight into parts of size at least six has at
most eight parts. -/
theorem card_le_eight_of_sum_eq_fortyEight_of_six_le
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hsum : ∑ c ∈ C, w c = 48) (hlower : ∀ c ∈ C, 6 ≤ w c) :
    C.card ≤ 8 := by
  have hbound : 6 * C.card ≤ ∑ c ∈ C, w c := by
    calc
      6 * C.card = ∑ _c ∈ C, 6 := by simp [mul_comm]
      _ ≤ ∑ c ∈ C, w c := by
        apply Finset.sum_le_sum
        intro c hc
        exact hlower c hc
  rw [hsum] at hbound
  omega

/-- The extremal eight-part partition of forty-eight with every part at
least six is uniquely the constant partition by six. -/
theorem all_eq_six_of_card_eq_eight_sum_eq_fortyEight_of_six_le
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 8) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) :
    ∀ c ∈ C, w c = 6 := by
  intro c hc
  have hrest : 6 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
    calc
      6 * (C.erase c).card = ∑ _d ∈ C.erase c, 6 := by simp [mul_comm]
      _ ≤ ∑ d ∈ C.erase c, w d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hlower d (Finset.mem_of_mem_erase hd)
  have hcardErase : (C.erase c).card = 7 := by
    rw [Finset.card_erase_of_mem hc, hcard]
  have hsplit := Finset.sum_erase_add C w hc
  have hcLower := hlower c hc
  omega

/-- In a seven-part partition of forty-eight, a six-vertex floor leaves at
most twelve vertices in any one part.  Three-divisibility then restricts
every part to `6`, `9`, or `12`. -/
theorem seven_part_orders_eq_six_nine_or_twelve
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 7) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c) :
    ∀ c ∈ C, w c = 6 ∨ w c = 9 ∨ w c = 12 := by
  intro c hc
  have hrest : 6 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
    calc
      6 * (C.erase c).card = ∑ _d ∈ C.erase c, 6 := by simp [mul_comm]
      _ ≤ ∑ d ∈ C.erase c, w d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hlower d (Finset.mem_of_mem_erase hd)
  have hcardErase : (C.erase c).card = 6 := by
    rw [Finset.card_erase_of_mem hc, hcard]
  have hsplit := Finset.sum_erase_add C w hc
  have hcLower := hlower c hc
  obtain ⟨k, hk⟩ := hthree c hc
  omega

/-- Counting the three possible orders in a seven-part partition identifies
the two possible multisets. -/
theorem seven_part_six_nine_twelve_count_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 7) (hsum : ∑ c ∈ C, w c = 48)
    (horders : ∀ c ∈ C, w c = 6 ∨ w c = 9 ∨ w c = 12) :
    let n₆ := (C.filter fun c => w c = 6).card
    let n₉ := (C.filter fun c => w c = 9).card
    let n₁₂ := (C.filter fun c => w c = 12).card
    (n₆ = 6 ∧ n₉ = 0 ∧ n₁₂ = 1) ∨
      (n₆ = 5 ∧ n₉ = 2 ∧ n₁₂ = 0) := by
  classical
  dsimp only
  let n₆ := (C.filter fun c => w c = 6).card
  let n₉ := (C.filter fun c => w c = 9).card
  let n₁₂ := (C.filter fun c => w c = 12).card
  have hcountEq : n₆ + n₉ + n₁₂ = 7 := by
    calc
      n₆ + n₉ + n₁₂ =
          ∑ c ∈ C, ((if w c = 6 then 1 else 0) +
            (if w c = 9 then 1 else 0) +
            (if w c = 12 then 1 else 0)) := by
              simp [n₆, n₉, n₁₂, Finset.sum_add_distrib]
      _ = ∑ _c ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h <;> simp [h]
      _ = 7 := by simp [hcard]
  have hmass₆ : 6 * n₆ = ∑ c ∈ C, if w c = 6 then 6 else 0 := by
    calc
      6 * n₆ = n₆ * 6 := by omega
      _ = ∑ _c ∈ C.filter (fun c => w c = 6), 6 := by simp [n₆]
      _ = ∑ c ∈ C, if w c = 6 then 6 else 0 := by
        rw [Finset.sum_filter]
  have hmass₉ : 9 * n₉ = ∑ c ∈ C, if w c = 9 then 9 else 0 := by
    calc
      9 * n₉ = n₉ * 9 := by omega
      _ = ∑ _c ∈ C.filter (fun c => w c = 9), 9 := by simp [n₉]
      _ = ∑ c ∈ C, if w c = 9 then 9 else 0 := by
        rw [Finset.sum_filter]
  have hmass₁₂ : 12 * n₁₂ = ∑ c ∈ C, if w c = 12 then 12 else 0 := by
    calc
      12 * n₁₂ = n₁₂ * 12 := by omega
      _ = ∑ _c ∈ C.filter (fun c => w c = 12), 12 := by simp [n₁₂]
      _ = ∑ c ∈ C, if w c = 12 then 12 else 0 := by
        rw [Finset.sum_filter]
  have hmassEq : 6 * n₆ + 9 * n₉ + 12 * n₁₂ = 48 := by
    calc
      6 * n₆ + 9 * n₉ + 12 * n₁₂ =
          ∑ c ∈ C, ((if w c = 6 then 6 else 0) +
            (if w c = 9 then 9 else 0) +
            (if w c = 12 then 12 else 0)) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← hmass₆, ← hmass₉, ← hmass₁₂]
      _ = ∑ c ∈ C, w c := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h <;> simp [h]
      _ = 48 := hsum
  omega

/- Retired by the cold-build audit: n=5 census pending a compact proof.
set_option maxHeartbeats 5000000 in
/-- Exact count-vector classification for five three-divisible parts of total
forty-eight, each at least six, when every odd part has even multiplicity. -/
theorem five_part_three_divisible_count_vector_classification
    (n₆ n₉ n₁₂ n₁₅ n₁₈ n₂₁ n₂₄ : ℕ)
    (hcount : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ = 5)
    (hmass : 6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ +
      21*n₂₁ + 24*n₂₄ = 48)
    (heven₉ : Even n₉) (heven₁₅ : Even n₁₅) (heven₂₁ : Even n₂₁) :
    (n₆ = 4 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1) ∨
      (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 2 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 3 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 1 ∧ n₉ = 2 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 0 ∧ n₉ = 4 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) := by
  obtain ⟨k₉, hk₉⟩ := heven₉
  obtain ⟨k₁₅, hk₁₅⟩ := heven₁₅
  obtain ⟨k₂₁, hk₂₁⟩ := heven₂₁
  have hexcess : n₉ + 2*n₁₂ + 3*n₁₅ + 4*n₁₈ + 5*n₂₁ + 6*n₂₄ = 6 := by
    omega
  have hn₁₂Cases : n₁₂ = 0 ∨ n₁₂ = 1 ∨ n₁₂ = 2 ∨ n₁₂ = 3 := by omega
  have hn₁₅Cases : n₁₅ = 0 ∨ n₁₅ = 1 ∨ n₁₅ = 2 := by omega
  have hn₁₈Cases : n₁₈ = 0 ∨ n₁₈ = 1 := by omega
  have hn₂₁Cases : n₂₁ = 0 ∨ n₂₁ = 1 := by omega
  have hn₂₄Cases : n₂₄ = 0 ∨ n₂₄ = 1 := by omega
  rcases hn₁₂Cases with h₁₂ | h₁₂ | h₁₂ | h₁₂ <;> try omega
  all_goals rcases hn₁₅Cases with h₁₅ | h₁₅ | h₁₅ <;> try omega
  all_goals rcases hn₁₈Cases with h₁₈ | h₁₈ <;> try omega
  all_goals rcases hn₂₁Cases with h₂₁ | h₂₁ <;> try omega
  all_goals rcases hn₂₄Cases with h₂₄ | h₂₄ <;> omega

set_option maxHeartbeats 5000000 in
/-- A five-element family of three-divisible weights at least six and of
total mass forty-eight has exactly one of the seven admissible count vectors,
provided each odd weight occurs with even multiplicity. -/
theorem five_part_three_divisible_count_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 5) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c)
    (heven₉ : Even (C.filter fun c => w c = 9).card)
    (heven₁₅ : Even (C.filter fun c => w c = 15).card)
    (heven₂₁ : Even (C.filter fun c => w c = 21).card) :
    let n₆ := (C.filter fun c => w c = 6).card
    let n₉ := (C.filter fun c => w c = 9).card
    let n₁₂ := (C.filter fun c => w c = 12).card
    let n₁₅ := (C.filter fun c => w c = 15).card
    let n₁₈ := (C.filter fun c => w c = 18).card
    let n₂₁ := (C.filter fun c => w c = 21).card
    let n₂₄ := (C.filter fun c => w c = 24).card
    (n₆ = 4 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1) ∨
      (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 2 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 3 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 1 ∧ n₉ = 2 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 0 ∧ n₉ = 4 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) := by
  classical
  dsimp only
  let n₆ := (C.filter fun c => w c = 6).card
  let n₉ := (C.filter fun c => w c = 9).card
  let n₁₂ := (C.filter fun c => w c = 12).card
  let n₁₅ := (C.filter fun c => w c = 15).card
  let n₁₈ := (C.filter fun c => w c = 18).card
  let n₂₁ := (C.filter fun c => w c = 21).card
  let n₂₄ := (C.filter fun c => w c = 24).card
  have horders : ∀ c ∈ C, w c = 6 ∨ w c = 9 ∨ w c = 12 ∨ w c = 15 ∨
      w c = 18 ∨ w c = 21 ∨ w c = 24 := by
    intro c hc
    have hrest : 6 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
      calc
        6 * (C.erase c).card = ∑ _d ∈ C.erase c, 6 := by simp [mul_comm]
        _ ≤ ∑ d ∈ C.erase c, w d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hlower d (Finset.mem_of_mem_erase hd)
    have hcardErase : (C.erase c).card = 4 := by
      rw [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add C w hc
    have hcLower := hlower c hc
    obtain ⟨k, hk⟩ := hthree c hc
    omega
  have hcountEq : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ = 5 := by
    calc
      n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ =
          ∑ c ∈ C, ((if w c = 6 then 1 else 0) +
            (if w c = 9 then 1 else 0) + (if w c = 12 then 1 else 0) +
            (if w c = 15 then 1 else 0) + (if w c = 18 then 1 else 0) +
            (if w c = 21 then 1 else 0) + (if w c = 24 then 1 else 0)) := by
              simp [n₆, n₉, n₁₂, n₁₅, n₁₈, n₂₁, n₂₄,
                Finset.sum_add_distrib]
      _ = ∑ _c ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h | h | h <;> simp [h]
      _ = 5 := by simp [hcard]
  have hmass (a : ℕ) :
      a * (C.filter fun c => w c = a).card =
        ∑ c ∈ C, if w c = a then a else 0 := by
    calc
      a * (C.filter fun c => w c = a).card =
          (C.filter fun c => w c = a).card * a := Nat.mul_comm _ _
      _ = ∑ _c ∈ C.filter (fun c => w c = a), a := by simp
      _ = ∑ c ∈ C, if w c = a then a else 0 := by rw [Finset.sum_filter]
  have hmassEq : 6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ +
      21*n₂₁ + 24*n₂₄ = 48 := by
    calc
      6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ + 21*n₂₁ + 24*n₂₄ =
          ∑ c ∈ C, ((if w c = 6 then 6 else 0) +
            (if w c = 9 then 9 else 0) + (if w c = 12 then 12 else 0) +
            (if w c = 15 then 15 else 0) + (if w c = 18 then 18 else 0) +
            (if w c = 21 then 21 else 0) + (if w c = 24 then 24 else 0)) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← hmass 6, ← hmass 9, ← hmass 12, ← hmass 15,
                ← hmass 18, ← hmass 21, ← hmass 24]
      _ = ∑ c ∈ C, w c := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h | h | h <;> simp [h]
      _ = 48 := hsum
  change Even n₉ at heven₉
  change Even n₁₅ at heven₁₅
  change Even n₂₁ at heven₂₁
  exact five_part_three_divisible_count_vector_classification
    n₆ n₉ n₁₂ n₁₅ n₁₈ n₂₁ n₂₄ hcountEq hmassEq heven₉ heven₁₅ heven₂₁
-/

/- Retired by the cold-build audit: n=4 vector census pending a compact proof.
set_option maxHeartbeats 5000000 in
/-- Exact count-vector classification for four three-divisible parts of total
forty-eight, each at least six, when every odd part has even multiplicity. -/
theorem four_part_three_divisible_count_vector_classification
    (n₆ n₉ n₁₂ n₁₅ n₁₈ n₂₁ n₂₄ n₂₇ n₃₀ : ℕ)
    (hcount : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ + n₂₇ + n₃₀ = 4)
    (hmass : 6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ +
      21*n₂₁ + 24*n₂₄ + 27*n₂₇ + 30*n₃₀ = 48)
    (heven₉ : Even n₉) (heven₁₅ : Even n₁₅)
    (heven₂₁ : Even n₂₁) (heven₂₇ : Even n₂₇) :
    (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 2 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 4 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) := by
  obtain ⟨k₉, hk₉⟩ := heven₉
  obtain ⟨k₁₅, hk₁₅⟩ := heven₁₅
  obtain ⟨k₂₁, hk₂₁⟩ := heven₂₁
  obtain ⟨k₂₇, hk₂₇⟩ := heven₂₇
  have hexcess : n₉ + 2*n₁₂ + 3*n₁₅ + 4*n₁₈ + 5*n₂₁ +
      6*n₂₄ + 7*n₂₇ + 8*n₃₀ = 8 := by omega
  have hn₂₁ : n₂₁ = 0 := by omega
  have hn₂₇ : n₂₇ = 0 := by omega
  have hn₁₂Cases : n₁₂ = 0 ∨ n₁₂ = 1 ∨ n₁₂ = 2 ∨ n₁₂ = 3 ∨ n₁₂ = 4 := by omega
  have hn₁₅Cases : n₁₅ = 0 ∨ n₁₅ = 1 ∨ n₁₅ = 2 := by omega
  have hn₁₈Cases : n₁₈ = 0 ∨ n₁₈ = 1 ∨ n₁₈ = 2 := by omega
  have hn₂₄Cases : n₂₄ = 0 ∨ n₂₄ = 1 := by omega
  have hn₃₀Cases : n₃₀ = 0 ∨ n₃₀ = 1 := by omega
  rcases hn₁₂Cases with h₁₂ | h₁₂ | h₁₂ | h₁₂ | h₁₂ <;> try omega
  all_goals rcases hn₁₅Cases with h₁₅ | h₁₅ | h₁₅ <;> try omega
  all_goals rcases hn₁₈Cases with h₁₈ | h₁₈ | h₁₈ <;> try omega
  all_goals rcases hn₂₄Cases with h₂₄ | h₂₄ <;> try omega
  all_goals rcases hn₃₀Cases with h₃₀ | h₃₀ <;> omega
-/

/-- A singleton family of total weight forty-eight consists of one
weight-forty-eight element. -/
theorem one_part_weight_count_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 1) (hsum : ∑ c ∈ C, w c = 48) :
    (C.filter fun c => w c = 48).card = 1 := by
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hcard
  simp only [Finset.sum_singleton, Finset.filter_singleton]
  simp_all

/- Retired by the cold-build audit: n=4 finset census pending a compact proof.
set_option maxHeartbeats 2000000 in
/-- Finset form of the exact four-part, three-divisible count classification. -/
theorem four_part_three_divisible_count_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 4) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c)
    (heven₉ : Even (C.filter fun c => w c = 9).card)
    (heven₁₅ : Even (C.filter fun c => w c = 15).card)
    (heven₂₁ : Even (C.filter fun c => w c = 21).card)
    (heven₂₇ : Even (C.filter fun c => w c = 27).card) :
    let n₆ := (C.filter fun c => w c = 6).card
    let n₉ := (C.filter fun c => w c = 9).card
    let n₁₂ := (C.filter fun c => w c = 12).card
    let n₁₅ := (C.filter fun c => w c = 15).card
    let n₁₈ := (C.filter fun c => w c = 18).card
    let n₂₁ := (C.filter fun c => w c = 21).card
    let n₂₄ := (C.filter fun c => w c = 24).card
    let n₂₇ := (C.filter fun c => w c = 27).card
    let n₃₀ := (C.filter fun c => w c = 30).card
    (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 2 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 4 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) := by
  classical
  dsimp only
  let n₆ := (C.filter fun c => w c = 6).card
  let n₉ := (C.filter fun c => w c = 9).card
  let n₁₂ := (C.filter fun c => w c = 12).card
  let n₁₅ := (C.filter fun c => w c = 15).card
  let n₁₈ := (C.filter fun c => w c = 18).card
  let n₂₁ := (C.filter fun c => w c = 21).card
  let n₂₄ := (C.filter fun c => w c = 24).card
  let n₂₇ := (C.filter fun c => w c = 27).card
  let n₃₀ := (C.filter fun c => w c = 30).card
  have horders : ∀ c ∈ C, w c = 6 ∨ w c = 9 ∨ w c = 12 ∨ w c = 15 ∨
      w c = 18 ∨ w c = 21 ∨ w c = 24 ∨ w c = 27 ∨ w c = 30 := by
    intro c hc
    have hrest : 6 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
      calc
        6 * (C.erase c).card = ∑ _d ∈ C.erase c, 6 := by simp [mul_comm]
        _ ≤ ∑ d ∈ C.erase c, w d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hlower d (Finset.mem_of_mem_erase hd)
    have hcardErase : (C.erase c).card = 3 := by
      rw [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add C w hc
    have hcLower := hlower c hc
    obtain ⟨k, hk⟩ := hthree c hc
    omega
  have hcountEq : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ + n₂₇ + n₃₀ = 4 := by
    calc
      n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ + n₂₁ + n₂₄ + n₂₇ + n₃₀ =
          ∑ c ∈ C, ((if w c = 6 then 1 else 0) + (if w c = 9 then 1 else 0) +
            (if w c = 12 then 1 else 0) + (if w c = 15 then 1 else 0) +
            (if w c = 18 then 1 else 0) + (if w c = 21 then 1 else 0) +
            (if w c = 24 then 1 else 0) + (if w c = 27 then 1 else 0) +
            (if w c = 30 then 1 else 0)) := by
              simp [n₆, n₉, n₁₂, n₁₅, n₁₈, n₂₁, n₂₄, n₂₇, n₃₀,
                Finset.sum_add_distrib]
      _ = ∑ _c ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h | h | h | h | h <;> simp [h]
      _ = 4 := by simp [hcard]
  have hmass (a : ℕ) : a * (C.filter fun c => w c = a).card =
      ∑ c ∈ C, if w c = a then a else 0 := by
    calc
      a * (C.filter fun c => w c = a).card =
          (C.filter fun c => w c = a).card * a := Nat.mul_comm _ _
      _ = ∑ _c ∈ C.filter (fun c => w c = a), a := by simp
      _ = ∑ c ∈ C, if w c = a then a else 0 := by rw [Finset.sum_filter]
  have hmassEq : 6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ +
      21*n₂₁ + 24*n₂₄ + 27*n₂₇ + 30*n₃₀ = 48 := by
    calc
      6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ + 21*n₂₁ + 24*n₂₄ + 27*n₂₇ + 30*n₃₀ =
          ∑ c ∈ C, ((if w c = 6 then 6 else 0) + (if w c = 9 then 9 else 0) +
            (if w c = 12 then 12 else 0) + (if w c = 15 then 15 else 0) +
            (if w c = 18 then 18 else 0) + (if w c = 21 then 21 else 0) +
            (if w c = 24 then 24 else 0) + (if w c = 27 then 27 else 0) +
            (if w c = 30 then 30 else 0)) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← hmass 6, ← hmass 9, ← hmass 12, ← hmass 15,
                ← hmass 18, ← hmass 21, ← hmass 24, ← hmass 27, ← hmass 30]
      _ = ∑ c ∈ C, w c := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h | h | h | h | h <;> simp [h]
      _ = 48 := hsum
  change Even n₉ at heven₉
  change Even n₁₅ at heven₁₅
  change Even n₂₁ at heven₂₁
  change Even n₂₇ at heven₂₇
  exact four_part_three_divisible_count_vector_classification
    n₆ n₉ n₁₂ n₁₅ n₁₈ n₂₁ n₂₄ n₂₇ n₃₀ hcountEq hmassEq
      heven₉ heven₁₅ heven₂₁ heven₂₇
-/

set_option maxHeartbeats 2000000 in
/-- Exact count classification for a six-part partition of forty-eight into
three-divisible parts of size at least six, with even multiplicity for odd
part sizes. -/
theorem six_part_three_divisible_count_classification
    {α : Type*} [DecidableEq α] (C : Finset α) (w : α → ℕ)
    (hcard : C.card = 6) (hsum : ∑ c ∈ C, w c = 48)
    (hlower : ∀ c ∈ C, 6 ≤ w c) (hthree : ∀ c ∈ C, 3 ∣ w c)
    (heven₉ : Even (C.filter fun c => w c = 9).card)
    (heven₁₅ : Even (C.filter fun c => w c = 15).card) :
    let n₆ := (C.filter fun c => w c = 6).card
    let n₉ := (C.filter fun c => w c = 9).card
    let n₁₂ := (C.filter fun c => w c = 12).card
    let n₁₅ := (C.filter fun c => w c = 15).card
    let n₁₈ := (C.filter fun c => w c = 18).card
    (n₆ = 5 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1) ∨
      (n₆ = 4 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0) ∨
      (n₆ = 3 ∧ n₉ = 2 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0) ∨
      (n₆ = 2 ∧ n₉ = 4 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0) := by
  classical
  dsimp only
  let n₆ := (C.filter fun c => w c = 6).card
  let n₉ := (C.filter fun c => w c = 9).card
  let n₁₂ := (C.filter fun c => w c = 12).card
  let n₁₅ := (C.filter fun c => w c = 15).card
  let n₁₈ := (C.filter fun c => w c = 18).card
  have horders : ∀ c ∈ C,
      w c = 6 ∨ w c = 9 ∨ w c = 12 ∨ w c = 15 ∨ w c = 18 := by
    intro c hc
    have hrest : 6 * (C.erase c).card ≤ ∑ d ∈ C.erase c, w d := by
      calc
        6 * (C.erase c).card = ∑ _d ∈ C.erase c, 6 := by simp [mul_comm]
        _ ≤ ∑ d ∈ C.erase c, w d := by
          apply Finset.sum_le_sum
          intro d hd
          exact hlower d (Finset.mem_of_mem_erase hd)
    have hcardErase : (C.erase c).card = 5 := by
      rw [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add C w hc
    have hcLower := hlower c hc
    obtain ⟨k, hk⟩ := hthree c hc
    omega
  have hcountEq : n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ = 6 := by
    calc
      n₆ + n₉ + n₁₂ + n₁₅ + n₁₈ =
          ∑ c ∈ C, ((if w c = 6 then 1 else 0) +
            (if w c = 9 then 1 else 0) +
            (if w c = 12 then 1 else 0) +
            (if w c = 15 then 1 else 0) +
            (if w c = 18 then 1 else 0)) := by
              simp [n₆, n₉, n₁₂, n₁₅, n₁₈, Finset.sum_add_distrib]
      _ = ∑ _c ∈ C, 1 := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h <;> simp [h]
      _ = 6 := by simp [hcard]
  have hmass (a : ℕ) :
      a * (C.filter fun c => w c = a).card =
        ∑ c ∈ C, if w c = a then a else 0 := by
    calc
      a * (C.filter fun c => w c = a).card =
          (C.filter fun c => w c = a).card * a := Nat.mul_comm _ _
      _ = ∑ _c ∈ C.filter (fun c => w c = a), a := by simp
      _ = ∑ c ∈ C, if w c = a then a else 0 := by
        rw [Finset.sum_filter]
  have hmassEq :
      6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ = 48 := by
    calc
      6*n₆ + 9*n₉ + 12*n₁₂ + 15*n₁₅ + 18*n₁₈ =
          ∑ c ∈ C, ((if w c = 6 then 6 else 0) +
            (if w c = 9 then 9 else 0) +
            (if w c = 12 then 12 else 0) +
            (if w c = 15 then 15 else 0) +
            (if w c = 18 then 18 else 0)) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_add_distrib, Finset.sum_add_distrib,
                ← hmass 6, ← hmass 9, ← hmass 12, ← hmass 15, ← hmass 18]
      _ = ∑ c ∈ C, w c := by
        apply Finset.sum_congr rfl
        intro c hc
        rcases horders c hc with h | h | h | h | h <;> simp [h]
      _ = 48 := hsum
  change Even n₉ at heven₉
  change Even n₁₅ at heven₁₅
  obtain ⟨k₉, hk₉⟩ := heven₉
  obtain ⟨k₁₅, hk₁₅⟩ := heven₁₅
  have hexcess : n₉ + 2*n₁₂ + 3*n₁₅ + 4*n₁₈ = 4 := by omega
  have hn₁₂ : n₁₂ ≤ 2 := by omega
  have hn₁₅ : n₁₅ ≤ 1 := by omega
  have hn₁₈ : n₁₈ ≤ 1 := by omega
  have hn₁₂Cases : n₁₂ = 0 ∨ n₁₂ = 1 ∨ n₁₂ = 2 := by omega
  have hn₁₅Cases : n₁₅ = 0 ∨ n₁₅ = 1 := by omega
  have hn₁₈Cases : n₁₈ = 0 ∨ n₁₈ = 1 := by omega
  rcases hn₁₂Cases with h₁₂ | h₁₂ | h₁₂ <;>
    rcases hn₁₅Cases with h₁₅ | h₁₅ <;>
    rcases hn₁₈Cases with h₁₈ | h₁₈ <;> omega

/-- Graph-facing capstone for the four-layer owner-bin obstruction.  Two
distinct minimum order-six components cannot each have one reverse-quotient
incidence among the same three order-twelve targets when all three column
sums are even.  The arithmetic selector finds a common target; detailed
balance turns its reverse quotient one into a positive forward quotient,
and minimum-to-larger target-source uniqueness identifies the two sources. -/
theorem false_of_two_orderSix_sources_three_orderTwelve_targets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₁ c₂ e₀ e₁ e₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₁min : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c₁.supp.ncard ≤ l.supp.ncard)
    (hc₁ : c₁.supp.ncard = 6) (hc₂ : c₂.supp.ncard = 6)
    (he₀ : e₀.supp.ncard = 12) (he₁ : e₁.supp.ncard = 12)
    (he₂ : e₂.supp.ncard = 12) (hcne : c₁ ≠ c₂)
    (hrow₁ : componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c₁ = 1)
    (hrow₂ : componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c₂ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c₂ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c₂ = 1)
    (hcol₀ : Even
      (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c₂))
    (hcol₁ : Even
      (componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c₂))
    (hcol₂ : Even
      (componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c₁ +
        componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c₂)) : False := by
  let D := secondOrderDefectGraph G
  have hshared := two_unit_rows_three_even_columns_share
    (componentQuotientMatrix G D e₀ c₁)
    (componentQuotientMatrix G D e₁ c₁)
    (componentQuotientMatrix G D e₂ c₁)
    (componentQuotientMatrix G D e₀ c₂)
    (componentQuotientMatrix G D e₁ c₂)
    (componentQuotientMatrix G D e₂ c₂)
    hrow₁ hrow₂ hcol₀ hcol₁ hcol₂
  have hsame : c₂.supp.ncard = c₁.supp.ncard := hc₂.trans hc₁.symm
  rcases hshared with h | h | h
  · have hbal₁ := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₁ e₀
    have hbal₂ := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₂ e₀
    have hpos₁ : 0 < componentQuotientMatrix G D c₁ e₀ := by
      have hrev : componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c₁ = 1 := by
        simpa [D] using h.1
      rw [hc₁, he₀, hrev] at hbal₁
      dsimp only [D]
      omega
    have hpos₂ : 0 < componentQuotientMatrix G D c₂ e₀ := by
      have hrev : componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c₂ = 1 := by
        simpa [D] using h.2
      rw [hc₂, he₀, hrev] at hbal₂
      dsimp only [D]
      omega
    have heq := secondOrder_minimum_largerTarget_source_unique
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c₁ c₂ e₀ hc₁min hsame (by omega) hpos₁ hpos₂
    exact hcne heq
  · have hbal₁ := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₁ e₁
    have hbal₂ := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₂ e₁
    have hpos₁ : 0 < componentQuotientMatrix G D c₁ e₁ := by
      have hrev : componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c₁ = 1 := by
        simpa [D] using h.1
      rw [hc₁, he₁, hrev] at hbal₁
      dsimp only [D]
      omega
    have hpos₂ : 0 < componentQuotientMatrix G D c₂ e₁ := by
      have hrev : componentQuotientMatrix G (secondOrderDefectGraph G) e₁ c₂ = 1 := by
        simpa [D] using h.2
      rw [hc₂, he₁, hrev] at hbal₂
      dsimp only [D]
      omega
    have heq := secondOrder_minimum_largerTarget_source_unique
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c₁ c₂ e₁ hc₁min hsame (by omega) hpos₁ hpos₂
    exact hcne heq
  · have hbal₁ := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₁ e₂
    have hbal₂ := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₂ e₂
    have hpos₁ : 0 < componentQuotientMatrix G D c₁ e₂ := by
      have hrev : componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c₁ = 1 := by
        simpa [D] using h.1
      rw [hc₁, he₂, hrev] at hbal₁
      dsimp only [D]
      omega
    have hpos₂ : 0 < componentQuotientMatrix G D c₂ e₂ := by
      have hrev : componentQuotientMatrix G (secondOrderDefectGraph G) e₂ c₂ = 1 := by
        simpa [D] using h.2
      rw [hc₂, he₂, hrev] at hbal₂
      dsimp only [D]
      omega
    have heq := secondOrder_minimum_largerTarget_source_unique
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c₁ c₂ e₂ hc₁min hsame (by omega) hpos₁ hpos₂
    exact hcne heq

/-- At the exact `d = 16` boundary, the total order of the
triangle-free-colored defect components is divisible by three.  This is the
global weighted color congruence used by the residual encoders. -/
theorem degree_sixteen_secondOrder_colorOrder_mod_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3) :
    ((Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card) % 3 = 0 := by
  have hcolor := secondOrder_colorOrder_mod_three
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  rw [hcard] at hcolor
  norm_num at hcolor ⊢
  exact hcolor

/-- At the degree-sixteen exact boundary, an odd defect component cannot
carry internal quotient degree three.  This labeling-free parity form is the
outer-signature constraint used in the small-layer quotient enumeration:
the internal handshake makes every odd component's diagonal quotient even. -/
theorem degree_sixteen_odd_component_diagonalQuotient_ne_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hodd : Odd c.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c ≠ 3 := by
  have heven := oddComponent_diagonalQuotient_even
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c hodd
  intro hthree
  rw [hthree] at heven
  norm_num at heven

/-- Arithmetic kernel for the two-layer O--R quotient.  Detailed balance
between a 5-divisible R component and a non-5-divisible O component forces
every positive O-to-R entry (which is bounded by the total O-to-R degree
five) to consume the entire row. -/
theorem eq_five_of_five_dvd_left_balance_not_dvd_right
    (r o a b : ℕ) (hr : 5 ∣ r) (ho : ¬ 5 ∣ o)
    (hbal : r * a = o * b) (hbpos : 0 < b) (hble : b ≤ 5) :
    b = 5 := by
  obtain ⟨k, rfl⟩ := hr
  have hdvdProd : 5 ∣ o * b := by
    rw [← hbal]
    simpa [mul_assoc] using dvd_mul_right 5 (k * a)
  have hp : Nat.Prime 5 := by norm_num
  have hbdvd : 5 ∣ b := (hp.dvd_mul.mp hdvdProd).resolve_left ho
  omega

/-- Three-primary analogue used by the zero-layer orphan cut. -/
theorem eq_three_of_three_dvd_left_balance_not_dvd_right
    (r o a b : ℕ) (hr : 3 ∣ r) (ho : ¬ 3 ∣ o)
    (hbal : r * a = o * b) (hbpos : 0 < b) (hble : b ≤ 3) :
    b = 3 := by
  obtain ⟨k, rfl⟩ := hr
  have hdvdProd : 3 ∣ o * b := by
    rw [← hbal]
    simpa [mul_assoc] using dvd_mul_right 3 (k * a)
  have hp : Nat.Prime 3 := by norm_num
  have hbdvd : 3 ∣ b := (hp.dvd_mul.mp hdvdProd).resolve_left ho
  omega

/-- Without the row bound, the same three-primary balance argument still
forces the right quotient entry to be divisible by three. -/
theorem three_dvd_right_of_three_dvd_left_balance_not_dvd_right
    (r o a b : ℕ) (hr : 3 ∣ r) (ho : ¬ 3 ∣ o)
    (hbal : r * a = o * b) : 3 ∣ b := by
  obtain ⟨k, rfl⟩ := hr
  have hdvdProd : 3 ∣ o * b := by
    rw [← hbal]
    simpa [mul_assoc] using dvd_mul_right 3 (k * a)
  have hp : Nat.Prime 3 := by norm_num
  exact (hp.dvd_mul.mp hdvdProd).resolve_left ho

/-- Once an O-to-R quotient entry consumes all five R neighbors, detailed
balance says that the R length divided by five divides the O length. -/
theorem div_five_dvd_right_of_balance_eq_five
    (r o a : ℕ) (hr : 5 ∣ r) (hbal : r * a = o * 5) :
    r / 5 ∣ o := by
  obtain ⟨k, rfl⟩ := hr
  have hk : k * a = o := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5)
    calc
      5 * (k * a) = (5 * k) * a := by simp [mul_assoc]
      _ = o * 5 := hbal
      _ = 5 * o := by omega
  rw [Nat.mul_div_right k (by norm_num)]
  exact ⟨a, hk.symm⟩

/-- Three-primary concentrated-cut divisor rule. -/
theorem div_three_dvd_right_of_balance_eq_three
    (r o a : ℕ) (hr : 3 ∣ r) (hbal : r * a = o * 3) :
    r / 3 ∣ o := by
  obtain ⟨k, rfl⟩ := hr
  have hk : k * a = o := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    calc
      3 * (k * a) = (3 * k) * a := by simp [mul_assoc]
      _ = o * 3 := hbal
      _ = 3 * o := by omega
  rw [Nat.mul_div_right k (by norm_num)]
  exact ⟨a, hk.symm⟩

/-- Integral indicator vector of a finite vertex set. -/
def vertexFinsetIndicator {V : Type*} [DecidableEq V]
    (S : Finset V) : V → ℤ := fun x => if x ∈ S then 1 else 0

/-- Multiplying a finite-set indicator by an adjacency matrix counts the
neighbors lying in that set.  This is the bridge from the residual cell
degree formulas to the second-order matrix identity. -/
theorem adjMatrix_mulVec_vertexFinsetIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : V) :
    (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator S) x =
      ((S ∩ G.neighborFinset x).card : ℤ) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  rw [Finset.sum_congr rfl (fun y hy => by
    simp only [vertexFinsetIndicator]
    rfl)]
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have heq : (G.neighborFinset x).filter (fun y => y ∈ S) =
      S ∩ G.neighborFinset x := by
    ext y
    simp [and_comm]
  rw [heq]

/-- The all-ones matrix sends a finite-set indicator to its cardinality. -/
theorem onesMatrix_mulVec_vertexFinsetIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) :
    (FriendshipTheoremOQ01.onesMatrix V).mulVec (vertexFinsetIndicator S) =
      fun _ => (S.card : ℤ) := by
  funext x
  simp only [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec,
    dotProduct, one_mul]
  simp [vertexFinsetIndicator]

/-- A child vertex has exactly its child degree many ambient neighbors in
the minimum-layer image. -/
theorem minimumLayerImage_inter_neighborFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {s : ℕ}
    (hregChild : ∀ x : minimumLayerVertex D c₀,
      (minimumLayerGraph G D c₀).degree x = s)
    (x : minimumLayerVertex D c₀) :
    (minimumLayerImageFinset D c₀ ∩ G.neighborFinset x.2.1).card = s := by
  classical
  let H := minimumLayerGraph G D c₀
  let ι : minimumLayerVertex D c₀ ↪ V :=
    ⟨minimumLayerVertexValue,
      minimumLayerVertexValue_injective (D := D) (c₀ := c₀)⟩
  have hinter : minimumLayerImageFinset D c₀ ∩ G.neighborFinset x.2.1 =
      (H.neighborFinset x).map ι := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzU, hzN⟩ := Finset.mem_inter.mp hz
      obtain ⟨q, _hq, hqz⟩ := Finset.mem_image.mp hzU
      subst z
      exact Finset.mem_map.mpr
        ⟨q, (H.mem_neighborFinset x q).mpr
          ((G.mem_neighborFinset x.2.1 q.2.1).mp hzN), rfl⟩
    · intro hz
      obtain ⟨q, hqN, hqz⟩ := Finset.mem_map.mp hz
      subst z
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩,
          (G.mem_neighborFinset x.2.1 q.2.1).mpr
            ((H.mem_neighborFinset x q).mp hqN)⟩
  rw [hinter, Finset.card_map, H.card_neighborFinset_eq_degree,
    hregChild x]

/-- The three-cell `(U,R,O)` adjacency quotient forced by a residual child
of degree `s` at ambient degree sixteen. -/
def degreeSixteenResidualQuotient (s : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  let p := s * (s - 1) + 3
  !![(s : ℤ), (16 - s : ℕ), 0;
     1, (p - s : ℕ), (16 - (1 + (p - s)) : ℕ);
     0, (p : ℤ), (16 - p : ℕ)]

set_option maxHeartbeats 800000 in
/-- All three surviving residual quotients have the same characteristic
polynomial, exposing the common nonprincipal factor `X² - 13`. -/
theorem degreeSixteenResidualQuotient_charpoly
    {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4) :
    (degreeSixteenResidualQuotient s).charpoly =
      (X - C (16 : ℤ)) * (X ^ 2 - C (13 : ℤ)) := by
  rcases hs with rfl | rfl | rfl <;>
    rw [show (degreeSixteenResidualQuotient _).charpoly =
      (Matrix.charmatrix (degreeSixteenResidualQuotient _)).det from rfl,
      Matrix.det_fin_three] <;>
    simp [degreeSixteenResidualQuotient, Matrix.charmatrix_apply_eq,
      Matrix.charmatrix_apply_ne] <;> ring

/-- **Operator-level scalar-123 terminal.**  Semisimplicity peels the
designated eigenvalue `2`; trace `-135` forces the residual trace nonzero,
while the arithmetic hypothesis and abstract trace escape force it zero. -/
theorem false_of_oneTwentyThree_semisimple_residual
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (hsq : S * S = (123 : ℚ) • (1 : E →ₗ[ℚ] E) - T)
    (htrace : LinearMap.trace ℚ E S = -(135 : ℚ))
    (hsemi : Module.End.IsSemisimple T)
    (harith : ∀ f : ℚ[X], f.Monic → Irreducible f → f ∣ T.charpoly →
      f ≠ X - C (2 : ℚ) → ¬ IsSquare (f.eval 123)) : False := by
  obtain ⟨r, hr2, hcop, hann, hrdvd⟩ :=
    exists_coprime_residual_annihilator_of_isSemisimple T hsemi 2
  have hne := residual_trace_ne_zero_of_sq_oneTwentyThree_of_trace_neg135
    S T hcomm r hcop hann hsq htrace
  have hzero := abstract_residual_trace_eq_zero
    S T hcomm hsq (LinearMap.aeval_self_charpoly T) hr2 hrdvd harith
  exact hne hzero

/-- **Graph-facing d=124 saturated terminal.**  A saturated `(124,12)`
minimum layer cannot exist: its canonical 112-fiber hard sector produces
the contradictory scalar-123 residual traces. -/
theorem no_minimumLayer_saturated_124_hardSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 124 ≤ G.minDegree)
    (hcard : Fintype.card V = 124 * (124 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 12)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        12 * (12 - 1) + 3) : False := by
  classical
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
  let P := (D.comap (fun z : X => z.1)).adjMatrix ℚ
  have hhard := exists_minimumLayer_saturated_124_hardSector_square
    G hfree hmin hcard c₀ hregChild hcardChild
  obtain ⟨owner, huniform, hcommAE, hcommPE, htrace, hsq⟩ := hhard
  let E := normalizedOwnerProjection (K := ℚ) owner 112
  let Q : Matrix X X ℚ := 1 - E
  have hQ : Q * Q = Q := by
    simpa [Q, E, IsIdempotentElem] using
      (complement_normalizedOwnerProjection_isIdempotent
        (K := ℚ) owner 112 (by norm_num) huniform)
  have hcommAQ : A * Q = Q * A := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcommAE]
  have hcommPQ : P * Q = Q * P := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcommPE]
  have hPsymm : P.IsSymm := SimpleGraph.isSymm_adjMatrix _
  have hpkg := range_restrict_oneTwentyThree_semisimple_package
    A P Q hPsymm hQ hcommAQ hcommPQ htrace hsq
  dsimp only at hpkg
  obtain ⟨htraceR, hsqR, hcommR, hsemiR⟩ := hpkg
  apply false_of_oneTwentyThree_semisimple_residual _ _
    hcommR hsqR htraceR hsemiR
  intro f hfmonic hfirr hfdvd hfne
  obtain ⟨c, hc3, hcmax, hfcycle⟩ :=
    exteriorHardSector_irreducible_dvd_cycleChebyshev
      G hfree (d := 124) (by norm_num) (by exact ⟨62, by norm_num⟩)
        hmin hcard c₀ Q hQ hcommPQ f hfirr hfdvd
  have hcmax' : c.supp.ncard ≤ 15255 := by
    norm_num at hcard
    rwa [hcard] at hcmax
  exact oneTwentyThree_cycleFactor_eval_nonsquare_except_two
    c.supp.ncard hc3 hcmax' f hfmonic hfirr hfcycle hfne

/-- **Unconditional sharp minimum-layer descent.**  The scalar-123
terminal removes the final `(d,s)=(124,12)` saturated residual from
`secondOrder_minimumLayer_gap_or_degree_oneTwentyFour`. -/
theorem secondOrder_minimumLayer_strict_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hd4 : d ≠ 4) (hd12 : d ≠ 12)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧ s < d ∧ s * (s - 1) + 4 ≤ d := by
  obtain ⟨s, hreg, hcardChild, hsEven, hsd, hbranch⟩ :=
    secondOrder_minimumLayer_gap_or_degree_oneTwentyFour
      G hfree hd heven hmin hcard hd4 hd12 c₀ hc₀min
  refine ⟨s, hreg, hcardChild, hsEven, hsd, ?_⟩
  rcases hbranch with hresidual | hgap
  · obtain ⟨rfl, rfl, hc₀three, hcount⟩ := hresidual
    exact False.elim (no_minimumLayer_saturated_124_hardSector
      G hfree hmin hcard c₀ hreg hcardChild)
  · exact hgap

/-- At ambient degree sixteen, unconditional sharp descent leaves only the
three even child degrees `0`, `2`, and `4`. -/
theorem secondOrder_degree_sixteen_minimumLayer_degree_zero_two_or_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (s = 0 ∨ s = 2 ∨ s = 4) ∧
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 := by
  obtain ⟨s, hreg, hcardChild, hsEven, hsd, hgap⟩ :=
    secondOrder_minimumLayer_strict_gap G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard (by norm_num) (by norm_num)
        c₀ hc₀min
  obtain ⟨k, hk⟩ := hsEven
  have hcases : s = 0 ∨ s = 2 ∨ s = 4 := by
    interval_cases s <;> norm_num at hgap <;> omega
  exact ⟨s, hcases, hreg, hcardChild⟩

/-- Exact cardinality of the exterior vertices missed by every disjoint
child-to-complement incidence row. -/
theorem minimumLayer_unused_exterior_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    ((Finset.univ \ U) \ Finset.univ.biUnion E).card =
      (d * (d - 1) + 3 - (s * (s - 1) + 3)) -
        (s * (s - 1) + 3) * (d - s) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hcardE : ∀ x : minimumLayerVertex D c₀, (E x).card = d - s := by
    intro x
    exact card_minimumLayerExternalNeighborFinset G D c₀
      hregParent hregChild x
  have hcardChildD : Fintype.card (minimumLayerVertex D c₀) =
      s * (s - 1) + 3 := by
    simpa [D] using hcardChild
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hunionCard : (Finset.univ.biUnion E).card =
      (s * (s - 1) + 3) * (d - s) := by
    rw [Finset.card_biUnion hpair]
    rw [Finset.sum_congr rfl (fun x _ => hcardE x)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcardChildD]
    norm_num
  have hunionSub : Finset.univ.biUnion E ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  rw [Finset.card_sdiff_of_subset hunionSub, hunionCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ U),
    Finset.card_univ, card_minimumLayerImageFinset, hcard, hcardChild]

/-- In the tight d=16, s=4 extension, exactly 48 exterior vertices are
orphans—missed by every child external-neighborhood row. -/
theorem degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    ((Finset.univ \ U) \ Finset.univ.biUnion E).card = 48 := by
  have h := minimumLayer_unused_exterior_card G hfree (d := 16) (s := 4)
    (by norm_num) (by norm_num) hmin hcard c₀ hregChild (by
      norm_num
      exact hcardChild)
  norm_num at h ⊢
  exact h

/-- Every orphan exterior vertex is serviced exactly once by each child
row: its neighborhood meets that row's external-neighbor set in one point. -/
theorem minimumLayer_orphan_service_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀))
    (u : minimumLayerVertex (secondOrderDefectGraph G) c₀) :
    (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀ u ∩
      G.neighborFinset z).card = 1 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀, ¬ G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm, hzOutside⟩
  have hzNotD : ¬ D.Adj u.2.1 z := by
    intro hD
    have hcomp : D.connectedComponentMk z = u.1.1 :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hD.symm).trans
        ((ConnectedComponent.mem_supp_iff u.1.1 u.2.1).mp u.2.2)
    have hzSupp : z ∈ u.1.1.supp :=
      (ConnectedComponent.mem_supp_iff u.1.1 z).mpr hcomp
    apply hzOutside
    exact Finset.mem_image.mpr
      ⟨⟨u.1, ⟨z, hzSupp⟩⟩, Finset.mem_univ _, rfl⟩
  have huz : u.2.1 ≠ z := by
    intro huz
    apply hzOutside
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, huz⟩
  have hcommon := card_common_eq_if_secondOrderDefect G hfree u.2.1 z huz
  have hzNotMem : z ∉ D.neighborFinset u.2.1 := by
    simpa [D.mem_neighborFinset] using hzNotD
  rw [if_neg hzNotMem] at hcommon
  have hnonempty : (G.neighborFinset u.2.1 ∩ G.neighborFinset z).Nonempty :=
    Finset.card_pos.mp (by omega)
  let q := hnonempty.choose
  have hqmem := hnonempty.choose_spec
  have ⟨hqu, hqz⟩ := Finset.mem_inter.mp hqmem
  have hqOutside : q ∉ U := by
    intro hqU
    obtain ⟨v, _hv, hvq⟩ := Finset.mem_image.mp hqU
    apply hzNoChildAdj v
    have hzq : G.Adj z q := (G.mem_neighborFinset z q).mp hqz
    change v.2.1 = q at hvq
    rwa [hvq]
  have hserviceNonempty : (E u ∩ G.neighborFinset z).Nonempty := by
    exact ⟨q, Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hqu, hqOutside⟩, hqz⟩⟩
  have hsub : E u ∩ G.neighborFinset z ⊆
      G.neighborFinset u.2.1 ∩ G.neighborFinset z := by
    intro y hy
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1,
        (Finset.mem_inter.mp hy).2⟩
  have hle := Finset.card_le_card hsub
  have hpos := Finset.card_pos.mpr hserviceNonempty
  change (E u ∩ G.neighborFinset z).card = 1
  omega

/-- The rowwise service law summed over the disjoint exterior rows: every
orphan has exactly `s(s-1)+3` neighbors in the used exterior, one for each
vertex of the minimum-layer child. -/
theorem minimumLayer_orphan_used_exterior_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset z).card =
      s * (s - 1) + 3 := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hpairInter :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset z) := by
    intro u hu v hv huv
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left)
        (hpair hu hv huv))
  have heq : Finset.univ.biUnion E ∩ G.neighborFinset z =
      Finset.univ.biUnion (fun u => E u ∩ G.neighborFinset z) := by
    ext y
    simp
  rw [heq, Finset.card_biUnion hpairInter]
  have hservice : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset z).card = 1 := by
    intro u
    exact minimumLayer_orphan_service_card_eq_one
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
        z hzOutside hzUnused u
  simp_rw [hservice]
  simpa [D] using hcardChild

/-- In the zero-layer branch every orphan has exactly three neighbors in
the used exterior, one in each of the three owner rows. -/
theorem degree_sixteen_zeroLayer_orphan_used_exterior_neighbor_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset z).card = 3 := by
  simpa using minimumLayer_orphan_used_exterior_neighbor_card
    G hfree (d := 16) (s := 0) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused

/-- In the two-layer branch every orphan has exactly five neighbors in the
used exterior, one in each row owned by the minimum `C₅`. -/
theorem degree_sixteen_twoLayer_orphan_used_exterior_neighbor_card_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset z).card = 5 := by
  simpa using minimumLayer_orphan_used_exterior_neighbor_card
    G hfree (d := 16) (s := 2) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused

/-- At ambient degree sixteen, the exact one-service-per-child-row law
leaves `16 - |U|` nonservice neighbors at every orphan, uniformly in the
minimum-layer child degree. -/
theorem degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)
    (G.neighborFinset z \ S).card = 16 - (s * (s - 1) + 3) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ v : V, G.degree v = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hpairE := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have hpairS :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset z) := by
    intro u hu v hv huv
    change Disjoint (E u ∩ G.neighborFinset z)
      (E v ∩ G.neighborFinset z)
    rw [Finset.disjoint_left]
    intro q hqu hqv
    exact (Finset.disjoint_left.mp (hpairE hu hv huv))
      (Finset.mem_inter.mp hqu).1 (Finset.mem_inter.mp hqv).1
  have hservice : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset z).card = 1 := by
    intro u
    exact minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild z hzOutside hzUnused u
  have hcardS : S.card = s * (s - 1) + 3 := by
    change (Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)).card = s * (s - 1) + 3
    rw [Finset.card_biUnion hpairS]
    rw [Finset.sum_congr rfl (fun u _ => hservice u)]
    simp [hcardChild, D]
  have hSsub : S ⊆ G.neighborFinset z := by
    intro q hq
    obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_inter.mp hq).2
  rw [Finset.card_sdiff_of_subset hSsub, hcardS,
    G.card_neighborFinset_eq_degree, hregParent z]

/-- Concrete residual degrees for the three surviving degree-sixteen
children: `13`, `11`, and `1` at child degrees `0`, `2`, and `4`. -/
theorem degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)
    (G.neighborFinset z \ S).card =
      if s = 0 then 13 else if s = 2 then 11 else 1 := by
  rcases hs with rfl | rfl | rfl <;>
    simpa using degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused

/-- In the d=16, s=4 branch, the fifteen exact service points consume all
but one neighbor of each orphan exterior vertex. -/
theorem degree_sixteen_fourLayer_orphan_unserviced_neighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)
    (G.neighborFinset z \ S).card = 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ v : V, G.degree v = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hpairE := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild)
  have hpairS :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset z) := by
    intro u hu v hv huv
    change Disjoint (E u ∩ G.neighborFinset z)
      (E v ∩ G.neighborFinset z)
    rw [Finset.disjoint_left]
    intro q hqu hqv
    exact (Finset.disjoint_left.mp (hpairE hu hv huv))
      (Finset.mem_inter.mp hqu).1 (Finset.mem_inter.mp hqv).1
  have hservice : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset z).card = 1 := by
    intro u
    exact minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused u
  have hcardS : S.card = 15 := by
    change (Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)).card = 15
    rw [Finset.card_biUnion hpairS]
    rw [Finset.sum_congr rfl (fun u _ => hservice u)]
    simp [hcardChild, D]
  have hSsub : S ⊆ G.neighborFinset z := by
    intro q hq
    obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_inter.mp hq).2
  rw [Finset.card_sdiff_of_subset hSsub, hcardS,
    G.card_neighborFinset_eq_degree, hregParent z]

/-- The nonservice neighbors are exactly the neighbors remaining inside the
orphan set.  Hence the orphan-induced residual degree is
`16 - (s(s-1)+3)` for every degree-sixteen child. -/
theorem degree_sixteen_minimumLayer_orphan_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion
          (minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀)) :
    (((Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
          Finset.univ.biUnion
            (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) ∩
        G.neighborFinset z).card = 16 - (s * (s - 1) + 3) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hzO : z ∈ O := hz
  have hzOutside : z ∉ U := (Finset.mem_sdiff.mp
    (Finset.mem_sdiff.mp hzO).1).2
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hzO).2
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀,
      ¬G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm, hzOutside⟩
  have heq : O ∩ G.neighborFinset z = G.neighborFinset z \ S := by
    ext y
    constructor
    · intro hy
      have hyO := (Finset.mem_inter.mp hy).1
      have hyN := (Finset.mem_inter.mp hy).2
      refine Finset.mem_sdiff.mpr ⟨hyN, ?_⟩
      intro hyS
      obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hyS
      exact (Finset.mem_sdiff.mp hyO).2
        (Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, (Finset.mem_inter.mp hyu).1⟩)
    · intro hy
      have hyN := (Finset.mem_sdiff.mp hy).1
      have hyNotS := (Finset.mem_sdiff.mp hy).2
      have hyOutside : y ∉ U := by
        intro hyU
        obtain ⟨v, _hv, hvy⟩ := Finset.mem_image.mp hyU
        apply hzNoChildAdj v
        change v.2.1 = y at hvy
        rw [hvy]
        exact (G.mem_neighborFinset z y).mp hyN
      have hyUnused : y ∉ Finset.univ.biUnion E := by
        intro hyUsed
        obtain ⟨u, hu, hyE⟩ := Finset.mem_biUnion.mp hyUsed
        apply hyNotS
        exact Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hyE, hyN⟩⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyOutside⟩, hyUnused⟩,
          hyN⟩
  rw [heq]
  exact degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card
    G hfree hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused

/-- Encoder-facing graph form of the degree-sixteen orphan calculation.
The induced orphan graph has the exact order and regular degree forced by
the child degree, and the handshake identity fixes twice its edge count. -/
theorem degree_sixteen_minimumLayer_orphan_induced_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    let H := G.induce (O : Set V)
    O.card =
        (16 * (16 - 1) + 3 - (s * (s - 1) + 3)) -
          (s * (s - 1) + 3) * (16 - s) ∧
      (∀ z : (O : Set V), H.degree z = 16 - (s * (s - 1) + 3)) ∧
      2 * H.edgeFinset.card =
        O.card * (16 - (s * (s - 1) + 3)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let H := G.induce (O : Set V)
  have hcardO : O.card =
      (16 * (16 - 1) + 3 - (s * (s - 1) + 3)) -
        (s * (s - 1) + 3) * (16 - s) :=
    minimumLayer_unused_exterior_card G hfree (d := 16) (s := s)
      (by norm_num) (by norm_num) hmin hcard c₀ hregChild hcardChild
  have hdegreeCard : ∀ z : (O : Set V), H.degree z =
      (O ∩ G.neighborFinset z.1).card := by
    intro z
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      exact Finset.mem_inter.mpr
        ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr
          ((H.mem_neighborFinset z y).mp hy)⟩
    · intro y _ y' _ hyy
      exact Subtype.ext hyy
    · intro y hy
      let y' : (O : Set V) := ⟨y, (Finset.mem_inter.mp hy).1⟩
      refine ⟨y', ?_, rfl⟩
      exact (H.mem_neighborFinset z y').mpr
        ((G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2)
  have hregular : ∀ z : (O : Set V),
      H.degree z = 16 - (s * (s - 1) + 3) := by
    intro z
    rw [hdegreeCard]
    exact degree_sixteen_minimumLayer_orphan_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild z.1 z.2
  refine ⟨hcardO, hregular, ?_⟩
  calc
    2 * H.edgeFinset.card = ∑ z : (O : Set V), H.degree z :=
      H.sum_degrees_eq_twice_card_edges.symm
    _ = ∑ _z : (O : Set V), (16 - (s * (s - 1) + 3)) := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact hregular z
    _ = O.card * (16 - (s * (s - 1) + 3)) := by simp

/-- In the `s = 0` branch the orphan graph is 13-regular on 192 vertices
and has 1248 edges. -/
theorem degree_sixteen_zeroLayer_orphan_induced_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let H := G.induce (O : Set V)
    O.card = 192 ∧ (∀ z : (O : Set V), H.degree z = 13) ∧
      H.edgeFinset.card = 1248 := by
  obtain ⟨hO, hreg, hedges⟩ :=
    degree_sixteen_minimumLayer_orphan_induced_regular
      G hfree (s := 0) hmin hcard c₀ hregChild (by norm_num; exact hcardChild)
  dsimp only at hO hreg hedges ⊢
  refine ⟨by norm_num at hO ⊢; exact hO, by simpa using hreg, ?_⟩
  norm_num [hO] at hedges ⊢
  omega

/-- In the `s = 2` branch the orphan graph is 11-regular on 168 vertices
and has 924 edges. -/
theorem degree_sixteen_twoLayer_orphan_induced_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let H := G.induce (O : Set V)
    O.card = 168 ∧ (∀ z : (O : Set V), H.degree z = 11) ∧
      H.edgeFinset.card = 924 := by
  obtain ⟨hO, hreg, hedges⟩ :=
    degree_sixteen_minimumLayer_orphan_induced_regular
      G hfree (s := 2) hmin hcard c₀ hregChild (by norm_num; exact hcardChild)
  dsimp only at hO hreg hedges ⊢
  refine ⟨by norm_num at hO ⊢; exact hO, by simpa using hreg, ?_⟩
  norm_num [hO] at hedges ⊢
  omega

/-- The 48 orphan vertices in the tight d=16, s=4 branch induce a
one-regular graph: every orphan's unique non-service neighbor is another
orphan. -/
theorem degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion
          (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    (((Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
          Finset.univ.biUnion
            (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) ∩
        G.neighborFinset z).card = 1 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hzO : z ∈ O := hz
  have hzOutside : z ∉ U := (Finset.mem_sdiff.mp
    (Finset.mem_sdiff.mp hzO).1).2
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hzO).2
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀, ¬ G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm, hzOutside⟩
  have heq : O ∩ G.neighborFinset z = G.neighborFinset z \ S := by
    ext y
    constructor
    · intro hy
      have hyO := (Finset.mem_inter.mp hy).1
      have hyN := (Finset.mem_inter.mp hy).2
      refine Finset.mem_sdiff.mpr ⟨hyN, ?_⟩
      intro hyS
      obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hyS
      exact (Finset.mem_sdiff.mp hyO).2
        (Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, (Finset.mem_inter.mp hyu).1⟩)
    · intro hy
      have hyN := (Finset.mem_sdiff.mp hy).1
      have hyNotS := (Finset.mem_sdiff.mp hy).2
      have hyOutside : y ∉ U := by
        intro hyU
        obtain ⟨v, _hv, hvy⟩ := Finset.mem_image.mp hyU
        apply hzNoChildAdj v
        change v.2.1 = y at hvy
        rw [hvy]
        exact (G.mem_neighborFinset z y).mp hyN
      have hyUnused : y ∉ Finset.univ.biUnion E := by
        intro hyUsed
        obtain ⟨u, hu, hyE⟩ := Finset.mem_biUnion.mp hyUsed
        apply hyNotS
        exact Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hyE, hyN⟩⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyOutside⟩, hyUnused⟩,
          hyN⟩
  rw [heq]
  exact degree_sixteen_fourLayer_orphan_unserviced_neighbor_card_eq_one
    G hfree hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused

/-- Graph form of the orphan matching: the induced orphan graph is
one-regular on 48 vertices and therefore has exactly 24 edges. -/
theorem degree_sixteen_fourLayer_orphan_induced_oneRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    let H := G.induce (O : Set V)
    (∀ z : (O : Set V), H.degree z = 1) ∧ H.edgeFinset.card = 24 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let H := G.induce (O : Set V)
  have hcardO : O.card = 48 := by
    exact degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  have hdegreeCard : ∀ z : (O : Set V), H.degree z =
      (O ∩ G.neighborFinset z.1).card := by
    intro z
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      have hzy : G.Adj z.1 y.1 := (H.mem_neighborFinset z y).mp hy
      exact Finset.mem_inter.mpr
        ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr hzy⟩
    · intro y hy₁ y' hy₂ hyy
      exact Subtype.ext hyy
    · intro y hy
      let y' : (O : Set V) := ⟨y, (Finset.mem_inter.mp hy).1⟩
      refine ⟨y', ?_, rfl⟩
      apply (H.mem_neighborFinset z y').mpr
      exact (G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2
  have hdegreeOne : ∀ z : (O : Set V), H.degree z = 1 := by
    intro z
    rw [hdegreeCard]
    exact degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z.1 z.2
  refine ⟨hdegreeOne, ?_⟩
  have hsum : ∑ z : (O : Set V), H.degree z = 48 := by
    simp_rw [hdegreeOne]
    simp [hcardO]
  have hedges : 48 = 2 * H.edgeFinset.card := by
    calc
      48 = ∑ z : (O : Set V), H.degree z := hsum.symm
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  apply Nat.mul_left_cancel (n := 2) (by norm_num)
  calc
    2 * H.edgeFinset.card = 48 := hedges.symm
    _ = 2 * 24 := by norm_num

/-- Two distinct orphans can be co-serviced in at most one child row.
More precisely, common service points belonging to two child rows force the
rows to coincide.  This is the `λ ≤ 1` packing law behind the d=16 terminal. -/
theorem degree_sixteen_fourLayer_shared_service_row_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V} (hzz' : z ≠ z')
    {u v : minimumLayerVertex (secondOrderDefectGraph G) c₀}
    {y y' : V}
    (hyu : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ u)
    (hyz : G.Adj z y) (hyz' : G.Adj z' y)
    (hy'v : y' ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v)
    (hy'z : G.Adj z y') (hy'z' : G.Adj z' y') :
    u = v := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hcommon := common_le_one_of_not_containsC4 hfree z z' hzz'
  have hyCommon : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y).mpr hyz,
        (G.mem_neighborFinset z' y).mpr hyz'⟩
  have hy'Common : y' ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y').mpr hy'z,
        (G.mem_neighborFinset z' y').mpr hy'z'⟩
  have hyy' : y = y' :=
    Finset.card_le_one.mp hcommon y hyCommon y' hy'Common
  by_contra huv
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild)
  have hdisj : Disjoint (E u) (E v) :=
    hpair (Finset.mem_univ u) (Finset.mem_univ v) huv
  exact (Finset.disjoint_left.mp hdisj) hyu (hyy' ▸ hy'v)

/-- If two distinct orphans share no service point, then they are adjacent in
the second-order defect graph.  The only possible common neighbors of two
orphans are service points: a common orphan neighbor would violate the
one-regularity of the induced orphan graph. -/
theorem degree_sixteen_fourLayer_uncovered_orphans_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : z ≠ z')
    (huncovered : ∀ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      ∀ y ∈ minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u,
        ¬(G.Adj z y ∧ G.Adj z' y)) :
    (secondOrderDefectGraph G).Adj z z' := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hzO : z ∈ O := hz
  have hz'O : z' ∈ O := hz'
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hzO).2
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀,
      ¬G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm,
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzO).1).2⟩
  have hcommonEmpty :
      G.neighborFinset z ∩ G.neighborFinset z' = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    have hyz : G.Adj z y :=
      (G.mem_neighborFinset z y).mp (Finset.mem_inter.mp hy).1
    have hyz' : G.Adj z' y :=
      (G.mem_neighborFinset z' y).mp (Finset.mem_inter.mp hy).2
    have hyOutside : y ∉ U := by
      intro hyU
      obtain ⟨v, _hv, hvy⟩ := Finset.mem_image.mp hyU
      apply hzNoChildAdj v
      change v.2.1 = y at hvy
      rwa [hvy]
    have hyUnused : y ∉ Finset.univ.biUnion E := by
      intro hyUsed
      obtain ⟨u, _hu, hyE⟩ := Finset.mem_biUnion.mp hyUsed
      exact huncovered u y hyE ⟨hyz, hyz'⟩
    have hyO : y ∈ O := Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyOutside⟩, hyUnused⟩
    have hone := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild y hyO
    have hzMem : z ∈ O ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr
        ⟨hzO, (G.mem_neighborFinset y z).mpr hyz.symm⟩
    have hz'Mem : z' ∈ O ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr
        ⟨hz'O, (G.mem_neighborFinset y z').mpr hyz'.symm⟩
    have hone' : (O ∩ G.neighborFinset y).card ≤ 1 := by
      rw [hone]
    exact hzz' (Finset.card_le_one.mp hone' z hzMem z' hz'Mem)
  have hcommonCard :
      (G.neighborFinset z ∩ G.neighborFinset z').card = 0 := by
    rw [hcommonEmpty]
    simp
  have hformula := card_common_eq_if_secondOrderDefect G hfree z z' hzz'
  by_contra hnotD
  have hnotMem : z' ∉ D.neighborFinset z := by
    simpa [D.mem_neighborFinset] using hnotD
  rw [if_neg hnotMem] at hformula
  omega

/-- Every orphan has at most two uncovered orphan partners.  All such
partners are defect neighbors, while the exact-boundary defect graph has
degree two. -/
theorem degree_sixteen_fourLayer_uncovered_orphan_card_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ((O.erase z).filter (fun z' =>
      ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
        ¬(G.Adj z y ∧ G.Adj z' y))).card ≤ 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  let C := (O.erase z).filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  have hsub : C ⊆ D.neighborFinset z := by
    intro z' hz'C
    have hz'Filter := Finset.mem_filter.mp hz'C
    have hz'O : z' ∈ O := Finset.mem_of_mem_erase hz'Filter.1
    have hzz' : z ≠ z' := Ne.symm (Finset.ne_of_mem_erase hz'Filter.1)
    apply (D.mem_neighborFinset z z').mpr
    exact degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz'O hzz'
        hz'Filter.2
  have hle := Finset.card_le_card hsub
  have hdeg : D.degree z = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree (by norm_num)
      (by norm_num) hmin hcard z
  rw [D.card_neighborFinset_eq_degree, hdeg] at hle
  exact hle

/-- Consequently, each orphan has at least 45 covered partners among the
other 47 orphans.  `Covered` here means the complement of the row-wise
uncovered predicate; a following lemma can unpack it into a shared service
point. -/
theorem degree_sixteen_fourLayer_covered_orphan_card_ge_fortyFive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    let P := O.erase z
    let C := P.filter (fun z' =>
      ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
        ¬(G.Adj z y ∧ G.Adj z' y))
    45 ≤ (P \ C).card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  let P := O.erase z
  let C := P.filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  have hcardO : O.card = 48 :=
    degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  have hcardP : P.card = 47 := by
    rw [Finset.card_erase_of_mem hz, hcardO]
  have hcardC : C.card ≤ 2 :=
    degree_sixteen_fourLayer_uncovered_orphan_card_le_two
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hCsub : C ⊆ P := Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hCsub, hcardP]
  omega

/-- Every used exterior vertex has the residual orphan degree left after its
child owner and its one neighbor in each child-nonadjacent exterior row. -/
theorem degree_sixteen_minimumLayer_used_exterior_orphan_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    (O ∩ G.neighborFinset y).card =
      16 - (1 + (s * (s - 1) + 3 - s)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  let N := G.neighborFinset y
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ x : V, G.degree x = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have howner : ∀ {u : minimumLayerVertex D c₀}, y ∈ E u → u = v := by
    intro u hyu
    by_contra huv
    exact (Finset.disjoint_left.mp
      (hpair (Finset.mem_univ u) (Finset.mem_univ v) huv)) hyu hyv
  have hUN : (U ∩ N).card = 1 := by
    have heq : U ∩ N = {v.2.1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp
          (Finset.mem_inter.mp hx).1
        have hxy : G.Adj y x :=
          (G.mem_neighborFinset y x).mp (Finset.mem_inter.mp hx).2
        have hyu : y ∈ E u := by
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, (Finset.mem_sdiff.mp hyv).2⟩
          change u.2.1 = x at hux
          exact (G.mem_neighborFinset u.2.1 y).mpr (by simpa [hux] using hxy.symm)
        have huv := howner hyu
        subst u
        change v.2.1 = x at hux
        simpa [hux]
      · intro hx
        have hxv : x = v.2.1 := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩,
            (G.mem_neighborFinset y v.2.1).mpr
              ((G.mem_neighborFinset v.2.1 y).mp
                (Finset.mem_sdiff.mp hyv).1).symm⟩
    rw [heq]
    simp
  have hpairBlocks :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ N) := by
    intro u hu w hw huw
    change Disjoint (E u ∩ N) (E w ∩ N)
    rw [Finset.disjoint_left]
    intro q hqu hqw
    exact (Finset.disjoint_left.mp (hpair hu hw huw))
      (Finset.mem_inter.mp hqu).1 (Finset.mem_inter.mp hqw).1
  have hblock : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ N).card = if H.Adj u v then 0 else 1 := by
    intro u
    rw [Finset.inter_comm]
    exact minimumLayer_externalBlock_card_of_owned
      G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild u v hyv
  have hnonAdjCount :
      (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card =
        s * (s - 1) + 3 - s := by
    have hadjFilter :
        Finset.univ.filter (fun u : minimumLayerVertex D c₀ => H.Adj u v) =
          H.neighborFinset v := by
      ext u
      simp [H.adj_comm]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (minimumLayerVertex D c₀)))
      (fun u => H.Adj u v)
    rw [hadjFilter, H.card_neighborFinset_eq_degree, hregChild v,
      Finset.card_univ, hcardChild] at hsplit
    omega
  have hRN : (R ∩ N).card = s * (s - 1) + 3 - s := by
    have heq : R ∩ N = Finset.univ.biUnion (fun u => E u ∩ N) := by
      ext q
      simp [R]
    rw [heq, Finset.card_biUnion hpairBlocks]
    simp_rw [hblock]
    have hbool :
        (∑ u : minimumLayerVertex D c₀, if ¬H.Adj u v then 1 else 0) =
          (Finset.univ.filter
            (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card := by
      simpa only [Nat.cast_id] using
        (Finset.sum_boole (R := ℕ)
          (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v) Finset.univ)
    calc
      (∑ u : minimumLayerVertex D c₀, if H.Adj u v then 0 else 1) =
          (∑ u : minimumLayerVertex D c₀,
            if ¬H.Adj u v then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases huv : H.Adj u v <;> simp [huv]
      _ = (Finset.univ.filter
          (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card := hbool
      _ = s * (s - 1) + 3 - s := hnonAdjCount
  have hURdisj : Disjoint U R := by
    rw [Finset.disjoint_left]
    intro q hqU hqR
    have hRsub := minimumLayer_externalBiUnion_subset_complement G D c₀ hqR
    exact (Finset.mem_sdiff.mp hRsub).2 hqU
  have hURN : ((U ∪ R) ∩ N).card =
      1 + (s * (s - 1) + 3 - s) := by
    have heq : (U ∪ R) ∩ N = (U ∩ N) ∪ (R ∩ N) := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [heq, Finset.card_union_of_disjoint]
    · rw [hUN, hRN]
    · exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
        (Finset.disjoint_of_subset_right (Finset.inter_subset_left) hURdisj)
  have hONeq : O ∩ N = N \ (U ∪ R) := by
    ext q
    simp [O, N]
    tauto
  rw [hONeq, Finset.card_sdiff]
  have hNcard : N.card = 16 := by
    rw [G.card_neighborFinset_eq_degree, hregParent y]
  rw [hNcard, hURN]

/-- In the zero-layer branch every used-exterior vertex has exactly twelve
orphan neighbors.  This is the row sum used by the component-quotient
enumerator: the remaining four neighbors consist of its unique `U₃` owner
and one point in each of the three used-exterior owner rows. -/
theorem degree_sixteen_zeroLayer_used_exterior_orphan_degree_eq_twelve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    (O ∩ G.neighborFinset y).card = 12 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_orphan_degree
    G hfree (s := 0) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) v hyv

/-- In the two-layer branch every used-exterior vertex again has exactly
twelve orphan neighbors.  Its other four neighbors are its unique `U₅`
owner and one point in each of the three child rows nonadjacent to that
owner. -/
theorem degree_sixteen_twoLayer_used_exterior_orphan_degree_eq_twelve
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    (O ∩ G.neighborFinset y).card = 12 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_orphan_degree
    G hfree (s := 2) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) v hyv

/-- The first adjacency image of the orphan indicator, written on the three
residual cells.  This packages the exact quotient column for `O`. -/
theorem degree_sixteen_minimumLayer_adjMatrix_mulVec_orphanIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (x : V) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) x =
      if x ∈ U then 0
      else if x ∈ R then 16 - (1 + (s * (s - 1) + 3 - s))
      else 16 - (s * (s - 1) + 3) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  rw [adjMatrix_mulVec_vertexFinsetIndicator]
  by_cases hxU : x ∈ U
  · rw [if_pos hxU]
    have hempty : O ∩ G.neighborFinset x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp hxU
      have hyO := (Finset.mem_inter.mp hy).1
      have hxy := (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).2
      have hyE : y ∈ E u := by
        apply Finset.mem_sdiff.mpr
        change u.2.1 = x at hux
        refine ⟨(G.mem_neighborFinset u.2.1 y).mpr (by simpa [hux] using hxy), ?_⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hyO).1).2
      exact (Finset.mem_sdiff.mp hyO).2
        (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hyE⟩)
    change ((O ∩ G.neighborFinset x).card : ℤ) = 0
    rw [hempty]
    simp
  · rw [if_neg hxU]
    by_cases hxR : x ∈ R
    · rw [if_pos hxR]
      obtain ⟨v, _hv, hxv⟩ := Finset.mem_biUnion.mp hxR
      norm_cast
      exact degree_sixteen_minimumLayer_used_exterior_orphan_degree
        G hfree (s := s) hmin hcard c₀ hregChild hcardChild v hxv
    · rw [if_neg hxR]
      have hxO : x ∈ O := Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxU⟩, hxR⟩
      norm_cast
      exact degree_sixteen_minimumLayer_orphan_neighbor_card
        G hfree hmin hcard c₀ hregChild hcardChild x hxO

/-- Compatibility form for the `s=4` branch: every used exterior vertex
has exactly four orphan neighbors. -/
theorem degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    (O ∩ G.neighborFinset y).card = 4 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_orphan_degree
    G hfree (s := 4) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) v hyv

/-- Correct row-by-row used-exterior split at `d=16`: an owned point
has one neighbor in every child-nonadjacent exterior row, including exactly
one in its own row, and none in a child-adjacent row. -/
theorem degree_sixteen_minimumLayer_used_exterior_row_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u ∩ G.neighborFinset y).card =
      if (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v
        then 0 else 1 := by
  rw [Finset.inter_comm]
  exact minimumLayer_externalBlock_card_of_owned
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild u v hyv

/-- Compatibility wrapper for the `s=4` residual branch. -/
theorem degree_sixteen_fourLayer_used_exterior_row_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u ∩ G.neighborFinset y).card =
      if (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v
        then 0 else 1 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_row_neighbor_card
    G hfree (s := 4) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) u v hyv

/-- Summing the row block law: an exterior point has one used-exterior
neighbor for each child vertex not adjacent to its owner. -/
theorem degree_sixteen_minimumLayer_used_exterior_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset y).card =
      s * (s - 1) + 3 - s := by
  classical
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have hpairInter :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset y) := by
    intro u hu w hw huw
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left)
        (hpair hu hw huw))
  have heq : Finset.univ.biUnion E ∩ G.neighborFinset y =
      Finset.univ.biUnion (fun u => E u ∩ G.neighborFinset y) := by
    ext q
    simp
  rw [heq, Finset.card_biUnion hpairInter]
  have hrow : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset y).card = if H.Adj u v then 0 else 1 := by
    intro u
    exact degree_sixteen_minimumLayer_used_exterior_row_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild u v hyv
  simp_rw [hrow]
  have hadjFilter :
      Finset.univ.filter (fun u : minimumLayerVertex D c₀ => H.Adj u v) =
        H.neighborFinset v := by
    ext u
    simp [H.adj_comm]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (minimumLayerVertex D c₀)))
    (fun u => H.Adj u v)
  rw [hadjFilter, H.card_neighborFinset_eq_degree, hregChild v,
    Finset.card_univ, hcardChild] at hsplit
  have hnonadj :
      (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card =
        s * (s - 1) + 3 - s := by omega
  have hbool :
      (∑ u : minimumLayerVertex D c₀, if ¬H.Adj u v then 1 else 0) =
        (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card := by
    simpa only [Nat.cast_id] using
      (Finset.sum_boole (R := ℕ)
        (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v) Finset.univ)
  rw [← hnonadj, ← hbool]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases huv : H.Adj u v <;> simp [huv]

/-- In the zero-layer branch each used-exterior vertex has exactly three
neighbors in the used exterior. -/
theorem degree_sixteen_zeroLayer_used_exterior_neighbor_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset y).card = 3 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_neighbor_card
    G hfree (s := 0) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) v hyv

/-- In the two-layer branch each used-exterior vertex also has exactly
three neighbors in the used exterior: one in each child row nonadjacent to
its owner on the minimum `C₅`. -/
theorem degree_sixteen_twoLayer_used_exterior_neighbor_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset y).card = 3 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_neighbor_card
    G hfree (s := 2) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) v hyv

/-- The first adjacency image of the used-exterior indicator, i.e. the
`R`-column of the three-cell quotient. -/
theorem degree_sixteen_minimumLayer_adjMatrix_mulVec_usedIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (x : V) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator R) x =
      if x ∈ U then 16 - s
      else if x ∈ R then s * (s - 1) + 3 - s
      else s * (s - 1) + 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  rw [adjMatrix_mulVec_vertexFinsetIndicator]
  by_cases hxU : x ∈ U
  · rw [if_pos hxU]
    obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp hxU
    have heq : R ∩ G.neighborFinset x = E u := by
      ext y
      constructor
      · intro hy
        have hyR := (Finset.mem_inter.mp hy).1
        have hxy := (Finset.mem_inter.mp hy).2
        have hyOutside := minimumLayer_externalBiUnion_subset_complement
          G D c₀ hyR
        apply Finset.mem_sdiff.mpr
        change u.2.1 = x at hux
        exact ⟨(G.mem_neighborFinset u.2.1 y).mpr
          (by simpa [hux] using (G.mem_neighborFinset x y).mp hxy),
          (Finset.mem_sdiff.mp hyOutside).2⟩
      · intro hy
        have hy' := Finset.mem_sdiff.mp hy
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hy⟩
        · change u.2.1 = x at hux
          exact (G.mem_neighborFinset x y).mpr
            (by simpa [hux] using (G.mem_neighborFinset u.2.1 y).mp hy'.1)
    rw [heq]
    norm_cast
    have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
      rw [hcard]
      norm_num
    have hregParent : ∀ z : V, G.degree z = 16 :=
      regular_of_minDegree_card_lt_nextMooreLayer
        G hfree (by norm_num) hmin hbelow
    exact card_minimumLayerExternalNeighborFinset
      G D c₀ hregParent hregChild u
  · rw [if_neg hxU]
    by_cases hxR : x ∈ R
    · rw [if_pos hxR]
      obtain ⟨v, _hv, hxv⟩ := Finset.mem_biUnion.mp hxR
      norm_cast
      exact degree_sixteen_minimumLayer_used_exterior_neighbor_card
        G hfree hmin hcard c₀ hregChild hcardChild v hxv
    · rw [if_neg hxR]
      norm_cast
      exact minimumLayer_orphan_used_exterior_neighbor_card
        G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
          c₀ hregChild hcardChild x hxU hxR

/-- On the three surviving child degrees, the orphan indicator satisfies the
common quotient polynomial: `A² 1_O = |O| 1 + 13 1_O`. -/
theorem degree_sixteen_minimumLayer_adjMatrix_sq_mulVec_orphanIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    (G.adjMatrix ℤ * G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) =
      fun x => (O.card : ℤ) + 13 * vertexFinsetIndicator O x := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  let r : ℤ := 16 - (1 + (s * (s - 1) + 3 - s) : ℕ)
  let a : ℤ := 16 - (s * (s - 1) + 3 : ℕ)
  have hr : r = (16 - (1 + (s * (s - 1) + 3 - s)) : ℕ) := by
    rcases hs with rfl | rfl | rfl <;> norm_num [r]
  have ha : a = (16 - (s * (s - 1) + 3) : ℕ) := by
    rcases hs with rfl | rfl | rfl <;> norm_num [a]
  have hAO : (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) =
      r • vertexFinsetIndicator R + a • vertexFinsetIndicator O := by
    funext x
    have hprof := degree_sixteen_minimumLayer_adjMatrix_mulVec_orphanIndicator
      G hfree hmin hcard c₀ hregChild hcardChild x
    change (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) x =
      (if x ∈ U then 0 else if x ∈ R then
        (16 - (1 + (s * (s - 1) + 3 - s)) : ℕ)
        else (16 - (s * (s - 1) + 3) : ℕ)) at hprof
    rw [hprof]
    by_cases hxU : x ∈ U
    · have hxR : x ∉ R := by
        intro hxR
        have hcomp := minimumLayer_externalBiUnion_subset_complement G D c₀ hxR
        exact (Finset.mem_sdiff.mp hcomp).2 hxU
      have hxO : x ∉ O := by simp [O, hxU]
      simp [vertexFinsetIndicator, hxU, hxR, hxO]
    · by_cases hxR : x ∈ R
      · have hxO : x ∉ O := by simp [O, hxR]
        simp [vertexFinsetIndicator, hxU, hxR, hxO, hr]
      · have hxO : x ∈ O := by simp [O, hxU, hxR]
        simp [vertexFinsetIndicator, hxU, hxR, hxO, ha]
  rw [← Matrix.mulVec_mulVec, hAO, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [degree_sixteen_minimumLayer_adjMatrix_mulVec_usedIndicator
      G hfree hmin hcard c₀ hregChild hcardChild x,
    degree_sixteen_minimumLayer_adjMatrix_mulVec_orphanIndicator
      G hfree hmin hcard c₀ hregChild hcardChild x]
  have hcardO := minimumLayer_unused_exterior_card
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  change O.card = _ at hcardO
  rw [hcardO]
  by_cases hxU : x ∈ U
  · have hxR : x ∉ R := by
      intro hxR
      exact (Finset.mem_sdiff.mp
        (minimumLayer_externalBiUnion_subset_complement G D c₀ hxR)).2 hxU
    have hxO : x ∉ O := by simp [O, hxU]
    have hxU' : x ∈ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := hxU
    rcases hs with rfl | rfl | rfl <;>
      norm_num [r, a, vertexFinsetIndicator, hxU, hxR, hxO, hxU']
  · by_cases hxR : x ∈ R
    · have hxO : x ∉ O := by simp [O, hxR]
      have hxU' : x ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := hxU
      have hxR' : ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
          x ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ u := by
        obtain ⟨u, _hu, hxu⟩ := Finset.mem_biUnion.mp hxR
        exact ⟨u, hxu⟩
      rcases hs with rfl | rfl | rfl <;>
        norm_num [r, a, vertexFinsetIndicator, hxU, hxR, hxO, hxU', hxR']
    · have hxO : x ∈ O := by simp [O, hxU, hxR]
      have hxU' : x ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := hxU
      have hxR' : ¬∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
          x ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ u := by
        intro hex
        obtain ⟨u, hxu⟩ := hex
        exact hxR (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hxu⟩)
      rcases hs with rfl | rfl | rfl <;>
        norm_num [r, a, vertexFinsetIndicator, hxU, hxR, hxO, hxU', hxR']

/-- The orphan indicator is a top (`2`) eigenvector of the second-order
defect graph in every surviving degree-sixteen residual branch. -/
theorem degree_sixteen_minimumLayer_defect_mulVec_orphanIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    (D.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) =
      (2 : ℤ) • vertexFinsetIndicator O := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hD : D.adjMatrix ℤ =
      (15 : ℤ) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V -
          (G.adjMatrix ℤ * G.adjMatrix ℤ) := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsq
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] at hxy ⊢
    norm_num at hxy ⊢
    linear_combination hxy
  have hpoly :=
    degree_sixteen_minimumLayer_adjMatrix_sq_mulVec_orphanIndicator
      G hfree hs hmin hcard c₀ hregChild hcardChild
  change (G.adjMatrix ℤ * G.adjMatrix ℤ).mulVec
      (vertexFinsetIndicator O) = _ at hpoly
  rw [hD, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, onesMatrix_mulVec_vertexFinsetIndicator, hpoly]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Graph-facing closure consequence: both defect neighbors of every orphan
remain in the orphan cell, uniformly for `s = 0,2,4`. -/
theorem degree_sixteen_minimumLayer_orphan_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    {z q : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzq : (secondOrderDefectGraph G).Adj z q) :
    q ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hmul := congrFun
    (degree_sixteen_minimumLayer_defect_mulVec_orphanIndicator
      G hfree hs hmin hcard c₀ hregChild hcardChild) z
  change (D.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) z = _ at hmul
  rw [adjMatrix_mulVec_vertexFinsetIndicator] at hmul
  have hcardInter : (O ∩ D.neighborFinset z).card = 2 := by
    simp [vertexFinsetIndicator, hz] at hmul
    exact_mod_cast hmul
  have hcardN : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree]
    exact secondOrderDefectGraph_degree_eq_two
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard z
  have heq : O ∩ D.neighborFinset z = D.neighborFinset z := by
    apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_right)
    rw [hcardInter, hcardN]
  have hqN : q ∈ D.neighborFinset z := (D.mem_neighborFinset z q).mpr hzq
  have hqInter : q ∈ O ∩ D.neighborFinset z := by simpa [heq] using hqN
  exact (Finset.mem_inter.mp hqInter).1

/-- The minimum-layer image is closed under the defect graph simply because
it is the union of complete minimum-order connected components. -/
theorem minimumLayerImage_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {z q : V}
    (hz : z ∈ minimumLayerImageFinset D c₀) (hzq : D.Adj z q) :
    q ∈ minimumLayerImageFinset D c₀ := by
  classical
  obtain ⟨u, _hu, huz⟩ := Finset.mem_image.mp hz
  change u.2.1 = z at huz
  subst z
  have hcomp : D.connectedComponentMk q = u.1.1 :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hzq.symm).trans
      ((ConnectedComponent.mem_supp_iff u.1.1 u.2.1).mp u.2.2)
  have hqSupp : q ∈ u.1.1.supp :=
    (ConnectedComponent.mem_supp_iff u.1.1 q).mpr hcomp
  exact Finset.mem_image.mpr
    ⟨⟨u.1, ⟨q, hqSupp⟩⟩, Finset.mem_univ _, rfl⟩

/-- The used exterior is the third defect-closed cell: it is the complement
of the already closed minimum layer and orphan cells. -/
theorem degree_sixteen_minimumLayer_used_exterior_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    {z q : V}
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (hzq : (secondOrderDefectGraph G).Adj z q) :
    q ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hzNotU : z ∉ U := by
    have hzComp := minimumLayer_externalBiUnion_subset_complement G D c₀ hz
    exact (Finset.mem_sdiff.mp hzComp).2
  have hzNotO : z ∉ O := by
    intro hzO
    exact (Finset.mem_sdiff.mp hzO).2 hz
  have hqNotU : q ∉ U := by
    intro hqU
    exact hzNotU (minimumLayerImage_defect_closed D c₀ hqU hzq.symm)
  have hqNotO : q ∉ O := by
    intro hqO
    exact hzNotO (degree_sixteen_minimumLayer_orphan_defect_closed
      G hfree hs hmin hcard c₀ hregChild hcardChild hqO hzq.symm)
  by_contra hqNotR
  exact hqNotO (Finset.mem_sdiff.mpr
    ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hqNotU⟩, hqNotR⟩)

/-- Component form of used-exterior defect closure: the entire defect
component of every used point remains inside the used cell `R`. -/
theorem degree_sixteen_minimumLayer_used_component_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    ∀ z ∈ R, (D.connectedComponentMk z).supp ⊆ (R : Set V) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  have hclosed : ∀ z ∈ R, D.neighborFinset z ⊆ R := by
    intro z hz q hzq
    exact degree_sixteen_minimumLayer_used_exterior_defect_closed
      G hfree hs hmin hcard c₀ hregChild hcardChild hz
        ((D.mem_neighborFinset z q).mp hzq)
  have hwalk : ∀ (a b : V) (p : D.Walk a b), a ∈ R → b ∈ R := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        have hv : _ ∈ R := hclosed _ ha
          ((D.mem_neighborFinset _ _).mpr hadj)
        exact ih hv
  intro z hz q hq
  have heq : D.connectedComponentMk q = D.connectedComponentMk z :=
    (ConnectedComponent.mem_supp_iff (D.connectedComponentMk z) q).mp hq
  have hr : D.Reachable z q := ConnectedComponent.eq.mp heq.symm
  obtain ⟨p⟩ := hr
  exact hwalk z q p hz

/-- In particular, every used exterior row is internally one-regular. -/
theorem degree_sixteen_fourLayer_used_exterior_sameRow_neighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ v ∩ G.neighborFinset y).card = 1 := by
  rw [degree_sixteen_fourLayer_used_exterior_row_neighbor_card
    G hfree hmin hcard c₀ hregChild hcardChild v v hyv]
  simp

/-- A service point through a fixed orphan lies in a four-orphan block, so
after deleting the fixed orphan it supplies exactly three covered partners. -/
theorem degree_sixteen_fourLayer_service_partner_block_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z y : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (u : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (hyu : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ u)
    (hzy : G.Adj z y) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    ((O ∩ G.neighborFinset y).erase z).card = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hfour : (O ∩ G.neighborFinset y).card = 4 :=
    degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
      G hfree hmin hcard c₀ hregChild hcardChild u hyu
  have hzMem : z ∈ O ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨hz, (G.mem_neighborFinset y z).mpr hzy.symm⟩
  rw [Finset.card_erase_of_mem hzMem, hfour]

/-- The fifteen service rows through a fixed orphan yield fifteen pairwise
disjoint three-partner blocks, hence cover exactly 45 other orphans. -/
theorem degree_sixteen_fourLayer_exists_service_partner_packing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    ∃ service : minimumLayerVertex D c₀ → V,
      (∀ u, service u ∈ E u ∧ G.Adj z (service u)) ∧
      ((↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u =>
          (O ∩ G.neighborFinset (service u)).erase z)) ∧
      (Finset.univ.biUnion (fun u =>
        (O ∩ G.neighborFinset (service u)).erase z)).card = 45 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hzOutside : z ∉ U :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hz).2
  have hex : ∀ u : minimumLayerVertex D c₀,
      ∃ y, y ∈ E u ∧ G.Adj z y := by
    intro u
    have hone := minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild)
        z hzOutside hzUnused u
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hone
    have hymem : y ∈ E u ∩ G.neighborFinset z := by
      rw [hy]
      exact Finset.mem_singleton_self y
    exact ⟨y, (Finset.mem_inter.mp hymem).1,
      (G.mem_neighborFinset z y).mp (Finset.mem_inter.mp hymem).2⟩
  choose service hservice using hex
  refine ⟨service, hservice, ?_, ?_⟩
  · intro u hu v hv huv
    change Disjoint
      ((O ∩ G.neighborFinset (service u)).erase z)
      ((O ∩ G.neighborFinset (service v)).erase z)
    rw [Finset.disjoint_left]
    intro q hqu hqv
    have hqu' := Finset.mem_erase.mp hqu
    have hqv' := Finset.mem_erase.mp hqv
    have hzq : z ≠ q := Ne.symm hqu'.1
    have hrow := degree_sixteen_fourLayer_shared_service_row_unique
      G hfree hmin hcard c₀ hregChild hcardChild hzq
        (hservice u).1 (hservice u).2
        ((G.mem_neighborFinset (service u) q).mp
          (Finset.mem_inter.mp hqu'.2).2).symm
        (hservice v).1 (hservice v).2
        ((G.mem_neighborFinset (service v) q).mp
          (Finset.mem_inter.mp hqv'.2).2).symm
    exact huv hrow
  · rw [Finset.card_biUnion]
    · have hthree : ∀ u : minimumLayerVertex D c₀,
          ((O ∩ G.neighborFinset (service u)).erase z).card = 3 := by
        intro u
        exact degree_sixteen_fourLayer_service_partner_block_card_eq_three
          G hfree hmin hcard c₀ hregChild hcardChild hz u
            (hservice u).1 (hservice u).2
      rw [Finset.sum_congr rfl (fun u _ => hthree u)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change Fintype.card
        (minimumLayerVertex (secondOrderDefectGraph G) c₀) * 3 = 45
      rw [hcardChild]
    · intro u hu v hv huv
      change Disjoint
        ((O ∩ G.neighborFinset (service u)).erase z)
        ((O ∩ G.neighborFinset (service v)).erase z)
      rw [Finset.disjoint_left]
      intro q hqu hqv
      have hqu' := Finset.mem_erase.mp hqu
      have hqv' := Finset.mem_erase.mp hqv
      have hzq : z ≠ q := Ne.symm hqu'.1
      have hrow := degree_sixteen_fourLayer_shared_service_row_unique
        G hfree hmin hcard c₀ hregChild hcardChild hzq
          (hservice u).1 (hservice u).2
          ((G.mem_neighborFinset (service u) q).mp
            (Finset.mem_inter.mp hqu'.2).2).symm
          (hservice v).1 (hservice v).2
          ((G.mem_neighborFinset (service v) q).mp
            (Finset.mem_inter.mp hqv'.2).2).symm
      exact huv hrow

/-- The abstract uncovered set has exactly two elements.  The complementary
covered set is precisely the explicit union of the fifteen disjoint
three-partner service blocks. -/
theorem degree_sixteen_fourLayer_uncovered_orphan_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ((O.erase z).filter (fun z' =>
      ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
        ¬(G.Adj z y ∧ G.Adj z' y))).card = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  let P := O.erase z
  let C := P.filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  obtain ⟨service, hservice, hpair, hcardK⟩ :=
    degree_sixteen_fourLayer_exists_service_partner_packing
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  let K := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    (O ∩ G.neighborFinset (service u)).erase z)
  have hKP : K = P \ C := by
    ext q
    constructor
    · intro hqK
      obtain ⟨u, _hu, hqBlock⟩ := Finset.mem_biUnion.mp hqK
      have hqErase := Finset.mem_erase.mp hqBlock
      have hqO := (Finset.mem_inter.mp hqErase.2).1
      have hqAdj : G.Adj q (service u) :=
        (G.mem_neighborFinset (service u) q).mp
          (Finset.mem_inter.mp hqErase.2).2 |>.symm
      have hqP : q ∈ P := Finset.mem_erase.mpr ⟨hqErase.1, hqO⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hqP, ?_⟩
      intro hqC
      have hpred := (Finset.mem_filter.mp hqC).2
      exact hpred u (service u) (hservice u).1
        ⟨(hservice u).2, hqAdj⟩
    · intro hqPC
      have hqP := (Finset.mem_sdiff.mp hqPC).1
      have hqNotC := (Finset.mem_sdiff.mp hqPC).2
      have hnotPred : ¬(∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
          ¬(G.Adj z y ∧ G.Adj q y)) := by
        intro hp
        exact hqNotC (Finset.mem_filter.mpr ⟨hqP, hp⟩)
      push_neg at hnotPred
      obtain ⟨u, y, hyE, hzy, hqy⟩ := hnotPred
      have hone := minimumLayer_orphan_service_card_eq_one
        G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
          c₀ hregChild (by norm_num; exact hcardChild) z
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
          (Finset.mem_sdiff.mp hz).2 u
      have hyMem : y ∈ E u ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr
          ⟨hyE, (G.mem_neighborFinset z y).mpr hzy⟩
      have hsMem : service u ∈ E u ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr
          ⟨(hservice u).1,
            (G.mem_neighborFinset z (service u)).mpr (hservice u).2⟩
      have hle : (E u ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
      have hys : y = service u :=
        Finset.card_le_one.mp hle y hyMem (service u) hsMem
      apply Finset.mem_biUnion.mpr
      refine ⟨u, Finset.mem_univ _, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · exact (Finset.ne_of_mem_erase hqP)
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_of_mem_erase hqP,
            (G.mem_neighborFinset (service u) q).mpr (by simpa [← hys] using hqy.symm)⟩
  have hcardO : O.card = 48 :=
    degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  have hcardP : P.card = 47 := by
    rw [Finset.card_erase_of_mem hz, hcardO]
  have hCsub : C ⊆ P := Finset.filter_subset _ _
  have hcardPC : (P \ C).card = 45 := by
    rw [← hKP]
    exact hcardK
  rw [Finset.card_sdiff_of_subset hCsub, hcardP] at hcardPC
  have hcancel := Nat.sub_add_cancel (Finset.card_le_card hCsub)
  rw [hcardP, hcardPC] at hcancel
  change C.card = 2
  apply Nat.add_left_cancel (n := 45)
  calc
    45 + C.card = 47 := hcancel
    _ = 45 + 2 := by norm_num

/-- The orphan set is closed under the second-order defect graph: both defect
neighbors of every orphan are its two uncovered orphan partners. -/
theorem degree_sixteen_fourLayer_orphans_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ∀ z ∈ O, D.neighborFinset z ⊆ O := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  intro z hz
  let C := (O.erase z).filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  have hCcard : C.card = 2 :=
    degree_sixteen_fourLayer_uncovered_orphan_card_eq_two
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hCsubD : C ⊆ D.neighborFinset z := by
    intro z' hz'C
    have hz'Filter := Finset.mem_filter.mp hz'C
    have hz'O : z' ∈ O := Finset.mem_of_mem_erase hz'Filter.1
    have hzz' : z ≠ z' := Ne.symm (Finset.ne_of_mem_erase hz'Filter.1)
    apply (D.mem_neighborFinset z z').mpr
    exact degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz'O hzz'
        hz'Filter.2
  have hDcard : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree,
      secondOrderDefectGraph_degree_eq_two G hfree (by norm_num)
        (by norm_num) hmin hcard z]
  have hCD : C = D.neighborFinset z :=
    Finset.eq_of_subset_of_card_le hCsubD (by rw [hCcard, hDcard])
  intro z' hz'D
  rw [← hCD] at hz'D
  exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hz'D).1

/-- Component form of uniform orphan defect closure: the entire defect
component of every orphan remains in the orphan cell. -/
theorem degree_sixteen_minimumLayer_orphan_component_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ∀ z ∈ O, (D.connectedComponentMk z).supp ⊆ (O : Set V) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  have hclosed : ∀ z ∈ O, D.neighborFinset z ⊆ O := by
    intro z hz q hzq
    exact degree_sixteen_minimumLayer_orphan_defect_closed
      G hfree hs hmin hcard c₀ hregChild hcardChild hz
        ((D.mem_neighborFinset z q).mp hzq)
  have hwalk : ∀ (a b : V) (p : D.Walk a b), a ∈ O → b ∈ O := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        have hv : _ ∈ O := hclosed _ ha
          ((D.mem_neighborFinset _ _).mpr hadj)
        exact ih hv
  intro z hz q hq
  have heq : D.connectedComponentMk q = D.connectedComponentMk z :=
    (ConnectedComponent.mem_supp_iff (D.connectedComponentMk z) q).mp hq
  have hr : D.Reachable z q := ConnectedComponent.eq.mp heq.symm
  obtain ⟨p⟩ := hr
  exact hwalk z q p hz

/-- Compatibility wrapper for the `s=4` component closure theorem. -/
theorem degree_sixteen_fourLayer_orphan_component_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ∀ z ∈ O, (D.connectedComponentMk z).supp ⊆ (O : Set V) := by
  simpa using degree_sixteen_minimumLayer_orphan_component_subset
    G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)

/-- The two smaller residual children pin the chosen defect-component order:
the empty child has one triangle, while the two-regular five-vertex child has
one defect component of order five. -/
theorem degree_sixteen_smallLayer_component_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    (s = 0 → c₀.supp.ncard = 3) ∧ (s = 2 → c₀.supp.ncard = 5) := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨r, hr3, hre, _⟩ :=
    secondOrderDefect_component_resolvent_chebyshev
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₀ 0
  have hw3 : 3 ≤ c₀.supp.ncard := by rw [← hre]; exact hr3
  have hkpos : 0 < (Finset.univ.filter
      (fun c : D.ConnectedComponent => c.supp.ncard = c₀.supp.ncard)).card := by
    apply Finset.card_pos.mpr
    exact ⟨c₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hlayer := card_minimumLayerVertex D c₀
  rw [hcardChild] at hlayer
  constructor
  · intro hs0
    subst s
    norm_num at hlayer
    nlinarith
  · intro hs2
    subst s
    norm_num at hlayer
    have hw5 : c₀.supp.ncard ≤ 5 := by nlinarith
    interval_cases c₀.supp.ncard <;> norm_num at hlayer ⊢ <;> omega

/-- In the two-regular residual branch the unique minimum defect component
is the five-vertex child itself, so its component-quotient diagonal is the
child degree two. -/
theorem degree_sixteen_twoLayer_minimumComponent_diagonal_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c₀ c₀ = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  let C : Finset V := c₀.supp.toFinite.toFinset
  have hCU : C ⊆ U := by
    intro z hz
    have hzc : z ∈ c₀.supp := by simpa [C] using hz
    let c : minimumLayerComponent D c₀ := ⟨c₀, rfl⟩
    let x : minimumLayerVertex D c₀ := ⟨c, ⟨z, hzc⟩⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hcardC : C.card = 5 := by
    rw [show C.card = c₀.supp.ncard by
      simpa [C] using
        (Set.ncard_eq_toFinset_card c₀.supp c₀.supp.toFinite).symm,
      hbase]
  have hcardU : U.card = 5 := by
    rw [card_minimumLayerImageFinset]
    exact hcardChild
  have hCUeq : C = U :=
    Finset.eq_of_subset_of_card_le hCU (by rw [hcardU, hcardC])
  let z := componentRepresentative D c₀
  have hzc : z ∈ c₀.supp := componentRepresentative_mem D c₀
  let c : minimumLayerComponent D c₀ := ⟨c₀, rfl⟩
  let x : minimumLayerVertex D c₀ := ⟨c, ⟨z, hzc⟩⟩
  have hinter : componentNeighborFinset G D c₀ z =
      U ∩ G.neighborFinset z := by
    ext q
    simp only [componentNeighborFinset, Finset.mem_filter,
      Finset.mem_inter]
    have hqU : q ∈ U ↔ q ∈ c₀.supp := by
      rw [← hCUeq]
      simp [C]
    rw [hqU, ConnectedComponent.mem_supp_iff]
    tauto
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard) c₀ c₀ hzc
  rw [hQ, hinter]
  exact minimumLayerImage_inter_neighborFinset_card G D c₀ hregChild x

/-- **Order-five mass squeeze in the two-layer branch.**  The unique
minimum component has order five, is canonically forward-oriented (all odd
cycle blocks are), and contributes diagonal mass two.  The mixed order-five
theorem makes the total selected mass divisible by five, while the global
nonsquare trace bounds it by sixteen.  Hence only `5`, `10`, or `15` remain. -/
theorem degree_sixteen_twoLayer_orientedFiveMass_eq_five_ten_or_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    orientedAnchorMass G u (forwardOriented G u) 5 = 5 ∨
      orientedAnchorMass G u (forwardOriented G u) 5 = 10 ∨
      orientedAnchorMass G u (forwardOriented G u) 5 = 15 := by
  classical
  let D := secondOrderDefectGraph G
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  have hcOdd : Odd c₀.supp.ncard := by rw [hbase]; norm_num
  have hcFwd : forwardOriented G u c₀ := by
    intro x y
    exact graph_equalOddCycle_diagBlock_adj_shift_iff
      (hℓ3 c₀) hcOdd G D (u c₀) (hu c₀)
        (adjMatrix_comm_secondOrderDefect_of_even
          G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard)
        (huD c₀) x y
  have hcMem : c₀ ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
      5 ∣ c.supp.ncard ∧ forwardOriented G u c) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hbase], hcFwd⟩
  have hbridge := orientedAnchorMass_eq_sum_diagonalQuotient
    G hfree (d := 16) (p := 5) (by norm_num) (by norm_num) hmin hcard
      u hu huRange (forwardOriented G u)
  have hcdiag := degree_sixteen_twoLayer_minimumComponent_diagonal_eq_two
    G hfree hmin hcard c₀ hregChild hcardChild
  have hmassLower : 2 ≤ orientedAnchorMass G u (forwardOriented G u) 5 := by
    rw [hbridge]
    rw [← hcdiag]
    exact Finset.single_le_sum
      (f := fun c : D.ConnectedComponent =>
        componentQuotientMatrix G D c c)
      (fun _ _ => Nat.zero_le _) hcMem
  have hmassUpper : orientedAnchorMass G u (forwardOriented G u) 5 ≤ 16 := by
    rw [hbridge]
    calc
      (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
          5 ∣ c.supp.ncard ∧ forwardOriented G u c),
          componentQuotientMatrix G D c c) ≤
          ∑ c : D.ConnectedComponent, componentQuotientMatrix G D c c := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      _ = 16 := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard (by norm_num)
  have hdvd := five_dvd_orientedAnchorMass_forwardOriented
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      u hℓ3 hbij huD
  omega

/-- The order-five mass squeeze forces at least three selected
five-divisible forward components.  Since the minimum `C₅` is one of them,
at least two additional selected components occur outside the base layer. -/
theorem degree_sixteen_twoLayer_three_le_forwardFive_component_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    3 ≤ (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent =>
        5 ∣ c.supp.ncard ∧ forwardOriented G u c)).card := by
  have hmass :=
    degree_sixteen_twoLayer_orientedFiveMass_eq_five_ten_or_fifteen
      G hfree hmin hcard c₀ hregChild hcardChild u hu huRange hℓ3 hbij huD
  have hmassLower : 5 ≤ orientedAnchorMass G u (forwardOriented G u) 5 := by
    rcases hmass with h5 | h10 | h15 <;> omega
  have hmassUpper :=
    orientedAnchorMass_forwardOriented_le_two_mul_component_card
      G hfree (d := 16) (p := 5) (by norm_num) (by norm_num) hmin hcard
        u hu huRange
  omega

/-- Sharp orphan-cycle lower bounds in the two small residual branches.
Since `c₀` is minimum and the orphan is outside the minimum layer, its full
component is strictly larger than the base length `3` or `5`. -/
theorem degree_sixteen_smallLayer_orphan_component_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    (s = 0 → 4 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) ∧
      (s = 2 → 6 ≤
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbase := degree_sixteen_smallLayer_component_card
    G hfree hs hmin hcard c₀ hregChild hcardChild
  have hne : (D.connectedComponentMk z).supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let c : minimumLayerComponent D c₀ := ⟨D.connectedComponentMk z, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    have hzU : z ∈ U := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hzU
  have hle : c₀.supp.ncard ≤ (D.connectedComponentMk z).supp.ncard :=
    hc₀min (D.connectedComponentMk z)
  constructor
  · intro hs0
    have hb : c₀.supp.ncard = 3 := hbase.1 hs0
    change 4 ≤ (D.connectedComponentMk z).supp.ncard
    omega
  · intro hs2
    have hb : c₀.supp.ncard = 5 := hbase.2 hs2
    change 6 ≤ (D.connectedComponentMk z).supp.ncard
    omega

/-- The same sharp cycle floors hold in the used-exterior cell, which is
also disjoint from the minimum layer and defect-closed. -/
theorem degree_sixteen_smallLayer_used_component_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    (s = 0 → 4 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) ∧
      (s = 2 → 6 ≤
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbase := degree_sixteen_smallLayer_component_card
    G hfree hs hmin hcard c₀ hregChild hcardChild
  have hne : (D.connectedComponentMk z).supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let c : minimumLayerComponent D c₀ := ⟨D.connectedComponentMk z, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    have hzU : z ∈ U := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have hzComp := minimumLayer_externalBiUnion_subset_complement G D c₀ hz
    exact (Finset.mem_sdiff.mp hzComp).2 hzU
  have hle : c₀.supp.ncard ≤ (D.connectedComponentMk z).supp.ncard :=
    hc₀min (D.connectedComponentMk z)
  constructor
  · intro hs0
    have hb : c₀.supp.ncard = 3 := hbase.1 hs0
    change 4 ≤ (D.connectedComponentMk z).supp.ncard
    omega
  · intro hs2
    have hb : c₀.supp.ncard = 5 := hbase.2 hs2
    change 6 ≤ (D.connectedComponentMk z).supp.ncard
    omega

/-- In the two small residual branches, every used-exterior defect cycle has
order divisible by the base cycle order: by three for `s = 0`, and by five
for `s = 2`.  The minimum layer consists of the single base component in
these cases, while every used point has an original-graph neighbor in that
layer.  The boundary quotient divisibility theorem then applies across the
resulting positive component edge. -/
theorem degree_sixteen_smallLayer_used_component_card_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    (s = 0 → 3 ∣ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) ∧
      (s = 2 → 5 ∣
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let e := D.connectedComponentMk z
  have hbase := degree_sixteen_smallLayer_component_card
    G hfree hs hmin hcard c₀ hregChild hcardChild
  have hbaseEq : c₀.supp.ncard = s * (s - 1) + 3 := by
    rcases hs with hs0 | hs2
    · subst s
      simpa using hbase.1 rfl
    · subst s
      simpa using hbase.2 rfl
  let C : Finset V := c₀.supp.toFinite.toFinset
  have hCU : C ⊆ U := by
    intro x hx
    have hxc : x ∈ c₀.supp := by simpa [C] using hx
    let c : minimumLayerComponent D c₀ := ⟨c₀, rfl⟩
    let u : minimumLayerVertex D c₀ := ⟨c, ⟨x, hxc⟩⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hcardC : C.card = c₀.supp.ncard := by
    simpa [C] using (Set.ncard_eq_toFinset_card c₀.supp c₀.supp.toFinite).symm
  have hcardU : U.card = c₀.supp.ncard := by
    rw [card_minimumLayerImageFinset, hcardChild, ← hbaseEq]
  have hCUeq : C = U := by
    apply Finset.eq_of_subset_of_card_le hCU
    rw [hcardU, hcardC]
  obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.mp hz
  have huz : G.Adj u.2.1 z :=
    (G.mem_neighborFinset u.2.1 z).mp (Finset.mem_sdiff.mp hzu).1
  have huU : u.2.1 ∈ U :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have huC : u.2.1 ∈ c₀.supp := by
    have : u.2.1 ∈ C := by simpa [hCUeq] using huU
    simpa [C] using this
  have huMk : D.connectedComponentMk u.2.1 = c₀ :=
    (ConnectedComponent.mem_supp_iff c₀ u.2.1).mp huC
  have hzE : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hQpos : 0 < componentQuotientMatrix G D e c₀ := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) e c₀ hzE]
    apply Finset.card_pos.mpr
    refine ⟨u.2.1, ?_⟩
    simp [componentNeighborFinset, huz.symm, huMk]
  have hQpos' : 0 < componentQuotientMatrix G D c₀ e := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₀ e
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c₀ e = 0 := by omega
    rw [hzero', mul_zero] at hbal
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    have : 0 < e.supp.ncard * componentQuotientMatrix G D e c₀ :=
      Nat.mul_pos hepos hQpos
    exact (Nat.ne_of_gt this) hbal.symm
  have hlower := degree_sixteen_smallLayer_used_component_card_lower
    G hfree hs hmin hcard c₀ hc₀min hregChild hcardChild z hz
  have hlt : c₀.supp.ncard < e.supp.ncard := by
    rcases hs with hs0 | hs2
    · subst s
      rw [hbase.1 rfl]
      exact hlower.1 rfl
    · subst s
      rw [hbase.2 rfl]
      exact hlower.2 rfl
  have hdvd :=
    (secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c₀ e hlt hQpos').2.1
  constructor
  · intro hs0
    rw [hbase.1 hs0] at hdvd
    exact hdvd
  · intro hs2
    rw [hbase.2 hs2] at hdvd
    exact hdvd

/-- Uniform cut-divisibility form: in every surviving `d = 16` residual
branch, the chosen minimum defect-cycle order divides the order of every
used-exterior defect component.  A used point is adjacent to its child-row
owner, hence its component has a positive quotient edge to that owner's
minimum component.  Minimality and disjointness from the layer make this a
strict short-to-long edge, where boundary quotient divisibility applies. -/
theorem degree_sixteen_minimumLayer_used_component_base_card_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    c₀.supp.ncard ∣
      ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.mp hz
  let c : D.ConnectedComponent := u.1.1
  have hcSize : c.supp.ncard = c₀.supp.ncard := u.1.2
  have huz : G.Adj u.2.1 z :=
    (G.mem_neighborFinset u.2.1 z).mp (Finset.mem_sdiff.mp hzu).1
  have huc : u.2.1 ∈ c.supp := u.2.2
  have hzE : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hQpos : 0 < componentQuotientMatrix G D e c := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) e c hzE]
    apply Finset.card_pos.mpr
    refine ⟨u.2.1, ?_⟩
    have huMk : D.connectedComponentMk u.2.1 = c :=
      (ConnectedComponent.mem_supp_iff c u.2.1).mp huc
    simp [componentNeighborFinset, huz.symm, huMk]
  have hQpos' : 0 < componentQuotientMatrix G D c e := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c e = 0 := by omega
    rw [hzero', mul_zero] at hbal
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    have hpos : 0 < e.supp.ncard * componentQuotientMatrix G D e c :=
      Nat.mul_pos hepos hQpos
    exact (Nat.ne_of_gt hpos) hbal.symm
  have hzOutside : z ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp
      (minimumLayer_externalBiUnion_subset_complement G D c₀ hz)).2
  have hne : e.supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let ce : minimumLayerComponent D c₀ := ⟨e, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨ce, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    exact hzOutside (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have hlt : c.supp.ncard < e.supp.ncard := by
    rw [hcSize]
    have hle := hc₀min e
    omega
  have hdvd :=
    (secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c e hlt hQpos').2.1
  rwa [hcSize] at hdvd

/-- Exact quotient form of the used-component cut law.  Every used-exterior
defect component `e` is attached to one minimum-layer component `c`; every
vertex of `e` has exactly one neighbor in `c`, while detailed balance gives
`|c| Q(c,e) = |e|`. -/
theorem degree_sixteen_minimumLayer_used_component_quotient_entries
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    ∃ c : D.ConnectedComponent,
      c.supp.ncard = c₀.supp.ncard ∧
      componentQuotientMatrix G D e c = 1 ∧
      c.supp.ncard * componentQuotientMatrix G D c e = e.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.mp hz
  let c : D.ConnectedComponent := u.1.1
  have hcSize : c.supp.ncard = c₀.supp.ncard := u.1.2
  have huz : G.Adj u.2.1 z :=
    (G.mem_neighborFinset u.2.1 z).mp (Finset.mem_sdiff.mp hzu).1
  have huc : u.2.1 ∈ c.supp := u.2.2
  have hzE : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hQpos : 0 < componentQuotientMatrix G D e c := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) e c hzE]
    apply Finset.card_pos.mpr
    refine ⟨u.2.1, ?_⟩
    have huMk : D.connectedComponentMk u.2.1 = c :=
      (ConnectedComponent.mem_supp_iff c u.2.1).mp huc
    simp [componentNeighborFinset, huz.symm, huMk]
  have hQpos' : 0 < componentQuotientMatrix G D c e := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c e = 0 := by omega
    rw [hzero', mul_zero] at hbal
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    have hpos : 0 < e.supp.ncard * componentQuotientMatrix G D e c :=
      Nat.mul_pos hepos hQpos
    exact (Nat.ne_of_gt hpos) hbal.symm
  have hzOutside : z ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp
      (minimumLayer_externalBiUnion_subset_complement G D c₀ hz)).2
  have hne : e.supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let ce : minimumLayerComponent D c₀ := ⟨e, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨ce, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    exact hzOutside (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have hlt : c.supp.ncard < e.supp.ncard := by
    rw [hcSize]
    have hle := hc₀min e
    omega
  obtain ⟨hone, _hdvd, hratio⟩ :=
    secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c e hlt hQpos'
  exact ⟨c, hcSize, hone, hratio⟩

/-- Uniform color restriction for every `d = 16` residual branch.  A used
component and its minimum-layer owner cannot both have triangle-free-colored
defect rims.  This packages the owner choice, strict size increase, and the
cyclic-cover color obstruction in one encoder-facing statement. -/
theorem degree_sixteen_minimumLayer_used_component_not_both_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (huinj : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    ∃ c : D.ConnectedComponent,
      c.supp.ncard = c₀.supp.ncard ∧
      ¬ ((∀ x, G.Adj (u c x) (u c (x + 1))) ∧
        (∀ y, G.Adj (u e y) (u e (y + 1)))) := by
  dsimp only
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  obtain ⟨c, hc, hone, hratio⟩ :=
    degree_sixteen_minimumLayer_used_component_quotient_entries
      G hfree hmin hcard c₀ hc₀min z hz
  have hzOutside : z ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp
      (minimumLayer_externalBiUnion_subset_complement G D c₀ hz)).2
  have hne : e.supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let ce : minimumLayerComponent D c₀ := ⟨e, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨ce, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    exact hzOutside (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have hlt : c.supp.ncard < e.supp.ncard := by
    rw [hc]
    have hle := hc₀min e
    omega
  have hcmin : ∀ l : D.ConnectedComponent, c.supp.ncard ≤ l.supp.ncard := by
    intro l
    rw [hc]
    exact hc₀min l
  have hpos : 0 < componentQuotientMatrix G D c e := by
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c e = 0 := by omega
    rw [hzero', mul_zero] at hratio
    exact (Nat.ne_of_gt hepos) hratio.symm
  refine ⟨c, hc, ?_⟩
  exact not_both_triangleFree_of_minimumComponent_longer_edge
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      (r := c.supp.ncard) (n := e.supp.ncard) (hℓ3 c) (hℓ3 e)
      c e hcmin hlt hpos (u c) (u e) (huinj c) (huinj e)
      (huRange c) (huRange e) (huD c) (huD e)

/-- In the two-layer branch, every used component of order `5k` meets each
minimum-layer vertex in exactly `k` neighbors: the quotient entries satisfy
`Q(e,c)=1` and `5 Q(c,e)=|e|` for its (necessarily order-five) owner
component. -/
theorem degree_sixteen_twoLayer_used_component_quotient_entries
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    componentQuotientMatrix G D e c₀ = 1 ∧
      5 * componentQuotientMatrix G D c₀ e = e.supp.ncard := by
  classical
  dsimp only
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  obtain ⟨c, hc, hone, hratio⟩ :=
    degree_sixteen_minimumLayer_used_component_quotient_entries
      G hfree hmin hcard c₀ hc₀min z hz
  have hcount : (Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard)).card = 1 := by
    have hlayer := card_minimumLayerVertex (secondOrderDefectGraph G) c₀
    rw [hcardChild, hbase] at hlayer
    have hcountFive : (Finset.univ.filter (fun a :
        (secondOrderDefectGraph G).ConnectedComponent =>
          a.supp.ncard = 5)).card = 1 := by
      omega
    simpa [hbase] using hcountFive
  have hcMem : c ∈ Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hc₀Mem : c₀ ∈ Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcc₀ : c = c₀ :=
    Finset.card_le_one.mp (by rw [hcount]) c hcMem c₀ hc₀Mem
  subst c
  refine ⟨hone, ?_⟩
  simpa [hbase] using hratio

/-- Every used-component block in the two-layer branch is not merely
balanced over the unique minimum `C₅`: after cyclically labeling both defect
cycles, its owner map advances globally by `+1` or globally by `-1` modulo
five.  Thus the entire block is determined by one offset and one orientation
bit. -/
theorem degree_sixteen_twoLayer_used_component_cycleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (u : ZMod 5 → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c₀.supp)
    (hvRange : Set.range v =
      ((secondOrderDefectGraph G).connectedComponentMk z).supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)}) :
    ∃ f : ZMod n → ZMod 5,
      (∀ x y, G.Adj (u x) (v y) ↔ x = f y) ∧
      ((∀ y, f (y + 1) = f y + 1) ∨
        (∀ y, f (y + 1) = f y - 1)) := by
  have hone := (degree_sixteen_twoLayer_used_component_quotient_entries
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild z hz).1
  exact exists_cycleCoverMap_of_componentQuotient_eq_one
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      (r := 5) (n := n) (by norm_num) hn c₀
      ((secondOrderDefectGraph G).connectedComponentMk z)
      u v huinj hvinj huRange hvRange huD hvD hone

/-- The base `C₅` and a used R cycle in the two-layer branch cannot both
be triangle-free-colored defect components.  Consequently, in the branch
where the base cycle is triangle-free-colored, every used R cycle is forced
to the antipodal color. -/
theorem degree_sixteen_twoLayer_not_both_triangleFree_used_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (u : ZMod 5 → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c₀.supp)
    (hvRange : Set.range v =
      ((secondOrderDefectGraph G).connectedComponentMk z).supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)}) :
    ¬ ((∀ x, G.Adj (u x) (u (x + 1))) ∧
      (∀ y, G.Adj (v y) (v (y + 1)))) := by
  let e := (secondOrderDefectGraph G).connectedComponentMk z
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  have helower := (degree_sixteen_smallLayer_used_component_card_lower
    G hfree (s := 2) (Or.inr rfl) hmin hcard c₀ hc₀min hregChild
      hcardChild z hz).2 rfl
  have hlt : c₀.supp.ncard < e.supp.ncard := by
    rw [hbase]
    change 5 < ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard
    omega
  have hratio := (degree_sixteen_twoLayer_used_component_quotient_entries
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild z hz).2
  have hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c₀ e := by
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    dsimp only [e] at hratio ⊢
    omega
  exact not_both_triangleFree_of_minimumComponent_longer_edge
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      (r := 5) (n := n) (by norm_num) hn c₀ e hc₀min hlt hpos
      u v huinj hvinj huRange hvRange huD hvD

/-- **Non-five orphan concentration in the two-layer branch.**  If an
orphan component whose order is not divisible by five has any positive
quotient entry toward a used R component, then that entry is exactly five:
every vertex of the orphan component sends its entire R-neighborhood into
that single component. -/
theorem degree_sixteen_twoLayer_orphan_to_used_quotient_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (zR : V)
    (hzR : zR ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (zO : V)
    (hzO : zO ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hnot : ¬ 5 ∣
      ((secondOrderDefectGraph G).connectedComponentMk zO).supp.ncard)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk zO)
      ((secondOrderDefectGraph G).connectedComponentMk zR)) :
    componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk zO)
      ((secondOrderDefectGraph G).connectedComponentMk zR) = 5 := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let e := D.connectedComponentMk zR
  let o := D.connectedComponentMk zO
  have heDvd : 5 ∣ e.supp.ncard :=
    (degree_sixteen_smallLayer_used_component_card_dvd
      G hfree (s := 2) (Or.inr rfl) hmin hcard c₀ hc₀min hregChild
        hcardChild zR hzR).2 rfl
  have heSubset : e.supp ⊆ (R : Set V) :=
    degree_sixteen_minimumLayer_used_component_subset
      G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
        (by norm_num; exact hcardChild) zR hzR
  have hcomponentSubset : componentNeighborFinset G D e zO ⊆
      R ∩ G.neighborFinset zO := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hye : y ∈ e.supp :=
      (ConnectedComponent.mem_supp_iff e y).mpr hy'.2
    exact Finset.mem_inter.mpr ⟨heSubset hye, hy'.1⟩
  have hzOutside : zO ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzO).1).2
  have hzUnused : zO ∉ R := (Finset.mem_sdiff.mp hzO).2
  have hRcard : (R ∩ G.neighborFinset zO).card = 5 := by
    simpa [D, R] using minimumLayer_orphan_used_exterior_neighbor_card
      G hfree (d := 16) (s := 2) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild zO hzOutside hzUnused
  have hoMem : zO ∈ o.supp := ConnectedComponent.connectedComponentMk_mem
  have hle : componentQuotientMatrix G D o e ≤ 5 := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) o e hoMem]
    rw [← hRcard]
    exact Finset.card_le_card hcomponentSubset
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  exact eq_five_of_five_dvd_left_balance_not_dvd_right
    e.supp.ncard o.supp.ncard
      (componentQuotientMatrix G D e o)
      (componentQuotientMatrix G D o e)
      heDvd (by simpa [o] using hnot) hbal (by simpa [D, o, e] using hpos) hle

/-- Divisibility form of a concentrated O--R cut: when `Q(o,e)=5` and the
R component has order `5k`, detailed balance forces `k ∣ |o|`. -/
theorem degree_sixteen_twoLayer_concentrated_cut_owner_ratio_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (heDvd : 5 ∣ e.supp.ncard)
    (hq : componentQuotientMatrix G (secondOrderDefectGraph G) o e = 5) :
    e.supp.ncard / 5 ∣ o.supp.ncard := by
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hq] at hbal
  exact div_five_dvd_right_of_balance_eq_five
    e.supp.ncard o.supp.ncard
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o)
      heDvd hbal

/-- Reduced detailed balance for two 5-divisible components.  Writing the
R and O orders as `5k` and `5m` removes the common factor and leaves the
small integer transport equation used by the two-layer encoder. -/
theorem degree_sixteen_twoLayer_fiveDivisible_cut_reduced_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (heDvd : 5 ∣ e.supp.ncard) (hoDvd : 5 ∣ o.supp.ncard) :
    ∃ k m : ℕ,
      e.supp.ncard = 5 * k ∧ o.supp.ncard = 5 * m ∧
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        m * componentQuotientMatrix G (secondOrderDefectGraph G) o e := by
  obtain ⟨k, hk⟩ := heDvd
  obtain ⟨m, hm⟩ := hoDvd
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hk, hm] at hbal
  have hreduced :
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        m * componentQuotientMatrix G (secondOrderDefectGraph G) o e := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5)
    simpa [mul_assoc] using hbal
  exact ⟨k, m, hk, hm, hreduced⟩

/-- Zero-layer analogue of orphan concentration.  A non-3-divisible orphan
component with a positive cut to a used R component sends all three of its
R neighbors into that one component. -/
theorem degree_sixteen_zeroLayer_orphan_to_used_quotient_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3)
    (zR : V)
    (hzR : zR ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (zO : V)
    (hzO : zO ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hnot : ¬ 3 ∣
      ((secondOrderDefectGraph G).connectedComponentMk zO).supp.ncard)
    (hpos : 0 < componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk zO)
      ((secondOrderDefectGraph G).connectedComponentMk zR)) :
    componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk zO)
      ((secondOrderDefectGraph G).connectedComponentMk zR) = 3 := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let e := D.connectedComponentMk zR
  let o := D.connectedComponentMk zO
  have heDvd : 3 ∣ e.supp.ncard :=
    (degree_sixteen_smallLayer_used_component_card_dvd
      G hfree (s := 0) (Or.inl rfl) hmin hcard c₀ hc₀min hregChild
        hcardChild zR hzR).1 rfl
  have heSubset : e.supp ⊆ (R : Set V) :=
    degree_sixteen_minimumLayer_used_component_subset
      G hfree (s := 0) (by norm_num) hmin hcard c₀ hregChild
        (by norm_num; exact hcardChild) zR hzR
  have hcomponentSubset : componentNeighborFinset G D e zO ⊆
      R ∩ G.neighborFinset zO := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hye : y ∈ e.supp :=
      (ConnectedComponent.mem_supp_iff e y).mpr hy'.2
    exact Finset.mem_inter.mpr ⟨heSubset hye, hy'.1⟩
  have hzOutside : zO ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzO).1).2
  have hzUnused : zO ∉ R := (Finset.mem_sdiff.mp hzO).2
  have hRcard : (R ∩ G.neighborFinset zO).card = 3 := by
    simpa [D, R] using minimumLayer_orphan_used_exterior_neighbor_card
      G hfree (d := 16) (s := 0) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild zO hzOutside hzUnused
  have hoMem : zO ∈ o.supp := ConnectedComponent.connectedComponentMk_mem
  have hle : componentQuotientMatrix G D o e ≤ 3 := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) o e hoMem]
    rw [← hRcard]
    exact Finset.card_le_card hcomponentSubset
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  exact eq_three_of_three_dvd_left_balance_not_dvd_right
    e.supp.ncard o.supp.ncard
      (componentQuotientMatrix G D e o)
      (componentQuotientMatrix G D o e)
      heDvd (by simpa [o] using hnot) hbal (by simpa [D, o, e] using hpos) hle

/-- Divisibility refinement of a concentrated zero-layer O--R cut: if the
R component has order `3k`, then `k` divides the orphan-component order. -/
theorem degree_sixteen_zeroLayer_concentrated_cut_owner_ratio_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (heDvd : 3 ∣ e.supp.ncard)
    (hq : componentQuotientMatrix G (secondOrderDefectGraph G) o e = 3) :
    e.supp.ncard / 3 ∣ o.supp.ncard := by
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hq] at hbal
  exact div_three_dvd_right_of_balance_eq_three
    e.supp.ncard o.supp.ncard
      (componentQuotientMatrix G (secondOrderDefectGraph G) e o)
      heDvd hbal

/-- Reduced detailed balance for two 3-divisible components in the zero-layer
branch.  Writing the R and O orders as `3k` and `3m` removes the common factor
and leaves the small integer transport equation used by the structured
encoder. -/
theorem degree_sixteen_zeroLayer_threeDivisible_cut_reduced_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (heDvd : 3 ∣ e.supp.ncard) (hoDvd : 3 ∣ o.supp.ncard) :
    ∃ k m : ℕ,
      e.supp.ncard = 3 * k ∧ o.supp.ncard = 3 * m ∧
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        m * componentQuotientMatrix G (secondOrderDefectGraph G) o e := by
  obtain ⟨k, hk⟩ := heDvd
  obtain ⟨m, hm⟩ := hoDvd
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hk, hm] at hbal
  have hreduced :
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        m * componentQuotientMatrix G (secondOrderDefectGraph G) o e := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    simpa [mul_assoc] using hbal
  exact ⟨k, m, hk, hm, hreduced⟩

/-- In the zero-layer branch the minimum layer is the single order-three
component.  Hence every used component attaches directly to `c₀`, with
reverse quotient one and forward quotient equal to one third of its order. -/
theorem degree_sixteen_zeroLayer_used_component_quotient_entries
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    componentQuotientMatrix G D e c₀ = 1 ∧
      3 * componentQuotientMatrix G D c₀ e = e.supp.ncard := by
  classical
  dsimp only
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 0) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).1 rfl
  obtain ⟨c, hc, hone, hratio⟩ :=
    degree_sixteen_minimumLayer_used_component_quotient_entries
      G hfree hmin hcard c₀ hc₀min z hz
  have hcount : (Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard)).card = 1 := by
    have hlayer := card_minimumLayerVertex (secondOrderDefectGraph G) c₀
    rw [hcardChild, hbase] at hlayer
    have hcountThree : (Finset.univ.filter (fun a :
        (secondOrderDefectGraph G).ConnectedComponent =>
          a.supp.ncard = 3)).card = 1 := by
      omega
    simpa [hbase] using hcountThree
  have hcMem : c ∈ Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hc₀Mem : c₀ ∈ Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcc₀ : c = c₀ :=
    Finset.card_le_one.mp (by rw [hcount]) c hcMem c₀ hc₀Mem
  subst c
  refine ⟨hone, ?_⟩
  simpa [hbase] using hratio

/-- Every used-component block in the zero-layer branch is an oriented
cyclic cover of the unique minimum `C₃`; after coordinate normalization the
whole U--R block is deterministic. -/
theorem degree_sixteen_zeroLayer_used_component_cycleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (u : ZMod 3 → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c₀.supp)
    (hvRange : Set.range v =
      ((secondOrderDefectGraph G).connectedComponentMk z).supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)}) :
    ∃ f : ZMod n → ZMod 3,
      (∀ x y, G.Adj (u x) (v y) ↔ x = f y) ∧
      ((∀ y, f (y + 1) = f y + 1) ∨
        (∀ y, f (y + 1) = f y - 1)) := by
  have hone := (degree_sixteen_zeroLayer_used_component_quotient_entries
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild z hz).1
  exact exists_cycleCoverMap_of_componentQuotient_eq_one
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      (r := 3) (n := n) (by norm_num) hn c₀
      ((secondOrderDefectGraph G).connectedComponentMk z)
      u v huinj hvinj huRange hvRange huD hvD hone

/-- In the four-layer branch every used defect cycle chooses one of the five
minimum `C₃` components as its owner.  Relative to arbitrary cyclic labels,
the corresponding incidence block is a globally oriented cyclic cover; it
is therefore determined by the owner, an offset, and one orientation bit. -/
theorem degree_sixteen_fourLayer_used_component_cycleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (huinj : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    ∃ c : D.ConnectedComponent,
      c.supp.ncard = 3 ∧
      componentQuotientMatrix G D e c = 1 ∧
      3 * componentQuotientMatrix G D c e = e.supp.ncard ∧
      ∃ f : ZMod e.supp.ncard → ZMod c.supp.ncard,
        (∀ x y, G.Adj (u c x) (u e y) ↔ x = f y) ∧
        ((∀ y, f (y + 1) = f y + 1) ∨
          (∀ y, f (y + 1) = f y - 1)) := by
  dsimp only
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  have hbase : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  obtain ⟨c, hc, hone, hratio⟩ :=
    degree_sixteen_minimumLayer_used_component_quotient_entries
      G hfree hmin hcard c₀ hc₀min z hz
  obtain ⟨f, hf, horient⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        (r := c.supp.ncard) (n := e.supp.ncard) (hℓ3 c) (hℓ3 e)
        c e (u c) (u e) (huinj c) (huinj e) (huRange c) (huRange e)
        (huD c) (huD e) hone
  refine ⟨c, hc.trans hbase, hone, ?_, f, hf, horient⟩
  simpa [hc, hbase] using hratio

/-- In the four-layer branch, any three child external-neighborhood rows
contain exactly thirty-six vertices.  In particular, the three rows belonging
to one minimum `C₃` owner form an exact size-36 bin for its owned used cycles. -/
theorem minimumLayer_owner_fiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) (a : minimumLayerComponent D c₀) :
    (Finset.univ.filter
      (fun x : minimumLayerVertex D c₀ => x.1 = a)).card = a.1.supp.ncard := by
  classical
  let X := Finset.univ.filter
    (fun x : minimumLayerVertex D c₀ => x.1 = a)
  let S := a.1.supp.toFinite.toFinset
  have hcard : X.card = S.card := by
    apply Finset.card_bij (fun x _ => x.2.1)
    · intro x hx
      have hxa : x.1 = a := (Finset.mem_filter.mp hx).2
      simpa [S, hxa] using x.2.2
    · intro x hx y hy hxy
      have hxa : x.1 = a := (Finset.mem_filter.mp hx).2
      have hya : y.1 = a := (Finset.mem_filter.mp hy).2
      cases x
      cases y
      subst_vars
      congr 1
      exact Subtype.ext hxy
    · intro z hz
      have hza : z ∈ a.1.supp := by simpa [S] using hz
      let x : minimumLayerVertex D c₀ := ⟨a, ⟨z, hza⟩⟩
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  rw [hcard]
  exact (Set.ncard_eq_toFinset_card a.1.supp a.1.supp.toFinite).symm

theorem degree_sixteen_fourLayer_three_externalRows_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (X : Finset (minimumLayerVertex (secondOrderDefectGraph G) c₀))
    (hX : X.card = 3) :
    (X.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)).card = 36 := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ z : V, G.degree z = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hrow : ∀ x : minimumLayerVertex D c₀, (E x).card = 12 := by
    intro x
    simpa [E] using card_minimumLayerExternalNeighborFinset
      G D c₀ hregParent hregChild x
  have hpairAll := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have hpairX : (↑X : Set (minimumLayerVertex D c₀)).PairwiseDisjoint E := by
    intro x hx y hy hxy
    exact hpairAll (Finset.mem_univ x) (Finset.mem_univ y) hxy
  change (X.biUnion E).card = 36
  rw [Finset.card_biUnion hpairX]
  rw [Finset.sum_congr rfl (fun x _ => hrow x)]
  simp [hX]

/-- Every orphan has exactly three neighbors in the union of any three
service rows.  This is the forward mass-three input for an owner bin. -/
theorem degree_sixteen_fourLayer_three_externalRows_orphan_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (X : Finset (minimumLayerVertex (secondOrderDefectGraph G) c₀))
    (hX : X.card = 3) (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    ((X.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) ∩ G.neighborFinset z).card = 3 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let N := G.neighborFinset z
  have hzOutside : z ∉ U := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzUnused : z ∉ R := (Finset.mem_sdiff.mp hz).2
  have hrow : ∀ x : minimumLayerVertex D c₀, (E x ∩ N).card = 1 := by
    intro x
    exact minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused x
  have hpairAll := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have hpair : (↑X : Set (minimumLayerVertex D c₀)).PairwiseDisjoint
      (fun x => E x ∩ N) := by
    intro x hx y hy hxy
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (hpairAll (Finset.mem_univ x) (Finset.mem_univ y) hxy))
  have hunion : (X.biUnion E) ∩ N = X.biUnion (fun x => E x ∩ N) := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨x, hx, hyE⟩, hyN⟩
      exact ⟨x, hx, hyE, hyN⟩
    · rintro ⟨x, hx, hyE, hyN⟩
      exact ⟨⟨x, hx, hyE⟩, hyN⟩
  change ((X.biUnion E) ∩ N).card = 3
  rw [hunion, Finset.card_biUnion hpair]
  rw [Finset.sum_congr rfl (fun x _ => hrow x)]
  simp [hX]

/-- Two service rows meeting the same used defect component have vertices
over the same minimum-layer component.  Equitability transports the first
row's positive incidence across the defect component, and disjointness of
service rows makes the transported owner unique. -/
theorem degree_sixteen_fourLayer_used_component_owner_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (x w : minimumLayerVertex (secondOrderDefectGraph G) c₀) {z q : V}
    (hzx : z ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ x)
    (hqw : q ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ w)
    (hcomp : (secondOrderDefectGraph G).connectedComponentMk q =
      (secondOrderDefectGraph G).connectedComponentMk z) :
    w.1 = x.1 := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let e := D.connectedComponentMk z
  let a : D.ConnectedComponent := x.1.1
  have hregD : ∀ v : V, D.degree v = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hze : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hqa : q ∈ e.supp := by
    rw [ConnectedComponent.mem_supp_iff, hcomp]
  have hQpos : 0 < componentQuotientMatrix G D e a := by
    rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm e a hze]
    apply Finset.card_pos.mpr
    refine ⟨x.2.1, ?_⟩
    have hxa : D.connectedComponentMk x.2.1 = a :=
      (ConnectedComponent.mem_supp_iff a x.2.1).mp x.2.2
    have hxz : G.Adj z x.2.1 :=
      ((G.mem_neighborFinset x.2.1 z).mp (Finset.mem_sdiff.mp hzx).1).symm
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset z x.2.1).mpr hxz, hxa⟩
  have hQq := componentQuotientMatrix_apply_eq G D 2 hregD hcomm e a hqa
  have hnonempty : (componentNeighborFinset G D a q).Nonempty := by
    apply Finset.card_pos.mp
    rw [← hQq]
    exact hQpos
  obtain ⟨t, ht⟩ := hnonempty
  have htData := Finset.mem_filter.mp ht
  have hta : t ∈ a.supp :=
    (ConnectedComponent.mem_supp_iff a t).mpr htData.2
  let u : minimumLayerVertex D c₀ :=
    ⟨x.1, ⟨t, by simpa [a] using hta⟩⟩
  have hqu : q ∈ E u := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(G.mem_neighborFinset u.2.1 q).mpr ?_, ?_⟩
    · simpa [u] using (G.mem_neighborFinset q t).mp htData.1 |>.symm
    · exact (Finset.mem_sdiff.mp hqw).2
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have huw : u = w := by
    by_contra huw
    exact (Finset.disjoint_left.mp
      (hpair (Finset.mem_univ u) (Finset.mem_univ w) huw)) hqu hqw
  simpa [u] using (congrArg Sigma.fst huw).symm

/-- The three service rows over a fixed minimum `C₃` component form a union
of whole used defect components. -/
theorem degree_sixteen_fourLayer_owner_bin_component_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (a : minimumLayerComponent (secondOrderDefectGraph G) c₀) :
    let D := secondOrderDefectGraph G
    let X := Finset.univ.filter
      (fun x : minimumLayerVertex D c₀ => x.1 = a)
    let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    ∀ y : V, y ∈ B ↔
      componentRepresentative D (D.connectedComponentMk y) ∈ B := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let X := Finset.univ.filter
    (fun x : minimumLayerVertex D c₀ => x.1 = a)
  let B := X.biUnion E
  have hstable : ∀ {y q : V}, y ∈ B →
      D.connectedComponentMk q = D.connectedComponentMk y → q ∈ B := by
    intro y q hy hqy
    obtain ⟨x, hxX, hyx⟩ := Finset.mem_biUnion.mp hy
    have hxOwner : x.1 = a := (Finset.mem_filter.mp hxX).2
    have hyR : y ∈ Finset.univ.biUnion E :=
      Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, hyx⟩
    have hqSupp : q ∈ (D.connectedComponentMk y).supp :=
      (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y) q).mpr hqy
    have hqR : q ∈ Finset.univ.biUnion E :=
      degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by omega) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild) y hyR hqSupp
    obtain ⟨w, _hw, hqw⟩ := Finset.mem_biUnion.mp hqR
    have hwOwner : w.1 = a := by
      rw [degree_sixteen_fourLayer_used_component_owner_eq
        G hfree hmin hcard c₀ hregChild hcardChild x w hyx hqw hqy,
        hxOwner]
    exact Finset.mem_biUnion.mpr
      ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwOwner⟩, hqw⟩
  intro y
  let r := componentRepresentative D (D.connectedComponentMk y)
  have hry : D.connectedComponentMk r = D.connectedComponentMk y :=
    (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y) r).mp
      (componentRepresentative_mem D (D.connectedComponentMk y))
  constructor
  · intro hy
    exact hstable hy hry
  · intro hr
    exact hstable hr hry.symm

/-- The used defect components owned by one minimum `C₃` form a partition of
its 36-vertex service bin; consequently every selected order is a
three-divisible integer between three and thirty-six. -/
theorem degree_sixteen_fourLayer_owner_bin_order_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (a : minimumLayerComponent (secondOrderDefectGraph G) c₀) :
    let D := secondOrderDefectGraph G
    let X := Finset.univ.filter
      (fun x : minimumLayerVertex D c₀ => x.1 = a)
    let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let E := Finset.univ.filter (fun e : D.ConnectedComponent =>
      componentRepresentative D e ∈ B)
    (∑ e ∈ E, e.supp.ncard) = 36 ∧
      ∀ e ∈ E, 3 ≤ e.supp.ncard ∧ e.supp.ncard ≤ 36 ∧
        3 ∣ e.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := Finset.univ.filter
    (fun x : minimumLayerVertex D c₀ => x.1 = a)
  let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let E := Finset.univ.filter (fun e : D.ConnectedComponent =>
    componentRepresentative D e ∈ B)
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have haThree : a.1.supp.ncard = 3 := a.2.trans hc₀three
  have hXcard : X.card = 3 := by
    simpa [X, haThree] using minimumLayer_owner_fiber_card D c₀ a
  have hBcard : B.card = 36 := by
    exact degree_sixteen_fourLayer_three_externalRows_card
      G hfree hmin hcard c₀ hregChild hcardChild X hXcard
  have hclose := degree_sixteen_fourLayer_owner_bin_component_closed
    G hfree hmin hcard c₀ hregChild hcardChild a
  have hclosed : ∀ (e : D.ConnectedComponent) (z : V), z ∈ e.supp →
      (z ∈ B ↔ componentRepresentative D e ∈ B) := by
    intro e z hze
    have hmk : D.connectedComponentMk z = e :=
      (ConnectedComponent.mem_supp_iff e z).mp hze
    simpa [D, X, B, hmk] using hclose z
  have hsum : (∑ e ∈ E, e.supp.ncard) = B.card := by
    simpa [E] using
      sum_component_sizes_filter_eq_card_of_component_closed D B hclosed
  have hsum36 : (∑ e ∈ E, e.supp.ncard) = 36 := hsum.trans hBcard
  refine ⟨hsum36, ?_⟩
  intro e he
  have herepB : componentRepresentative D e ∈ B :=
    (Finset.mem_filter.mp he).2
  have hBsubR : B ⊆ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, hzx⟩
  have hrepR := hBsubR herepB
  have hdvd : 3 ∣ e.supp.ncard := by
    have h := degree_sixteen_minimumLayer_used_component_base_card_dvd
      G hfree hmin hcard c₀ hc₀min (componentRepresentative D e) hrepR
    have hrep : D.connectedComponentMk (componentRepresentative D e) = e :=
      (ConnectedComponent.mem_supp_iff e
        (componentRepresentative D e)).mp (componentRepresentative_mem D e)
    rwa [hc₀three, hrep] at h
  have hlower : 3 ≤ e.supp.ncard := by
    obtain ⟨r, hr, hre, _⟩ := secondOrderDefect_component_resolvent_chebyshev
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e 0
    rwa [hre] at hr
  have hupper : e.supp.ncard ≤ 36 := by
    rw [← hsum36]
    exact Finset.single_le_sum
      (fun (x : D.ConnectedComponent) _ => Nat.zero_le x.supp.ncard) he
  exact ⟨hlower, hupper, hdvd⟩

/-- The fifteen pairwise-disjoint service rows in the four-layer branch have
twelve vertices each, so the full used-exterior cell has size 180. -/
theorem degree_sixteen_fourLayer_used_exterior_card_eq_oneEighty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    (Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)).card = 180 := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ z : V, G.degree z = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hrow : ∀ x : minimumLayerVertex D c₀, (E x).card = 12 := by
    intro x
    simpa [E] using card_minimumLayerExternalNeighborFinset
      G D c₀ hregParent hregChild x
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  change (Finset.univ.biUnion E).card = 180
  rw [Finset.card_biUnion hpair]
  rw [Finset.sum_congr rfl (fun x _ => hrow x)]
  calc
    (∑ _x : minimumLayerVertex D c₀, 12) =
        Fintype.card (minimumLayerVertex D c₀) * 12 := by simp
    _ = 180 := by
      rw [show Fintype.card (minimumLayerVertex D c₀) = 15 by
        simpa [D] using hcardChild]

/-- The used-exterior defect components partition the 180-point service
cell, and every component order is divisible by three. -/
theorem degree_sixteen_fourLayer_used_component_order_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent =>
      componentRepresentative D e ∈ R)
    (∑ e ∈ C, e.supp.ncard) = 180 ∧
      ∀ e ∈ C, 3 ∣ e.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion
    (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent =>
    componentRepresentative D e ∈ R)
  have hclosed : ∀ y : V,
      y ∈ R ↔ componentRepresentative D (D.connectedComponentMk y) ∈ R := by
    intro y
    constructor
    · intro hy
      exact degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild) y hy
          (componentRepresentative_mem D (D.connectedComponentMk y))
    · intro hr
      have hsub := degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild)
          (componentRepresentative D (D.connectedComponentMk y)) hr
      have hrepComp : D.connectedComponentMk
          (componentRepresentative D (D.connectedComponentMk y)) =
          D.connectedComponentMk y :=
        (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y)
          (componentRepresentative D (D.connectedComponentMk y))).mp
            (componentRepresentative_mem D (D.connectedComponentMk y))
      apply hsub
      rw [ConnectedComponent.mem_supp_iff, hrepComp]
  have hsum : (∑ e ∈ C, e.supp.ncard) = R.card := by
    simpa [C] using sum_component_sizes_filter_eq_card_of_component_closed
      D R (fun e z hz => by
        have hcomp : D.connectedComponentMk z = e :=
          (ConnectedComponent.mem_supp_iff e z).mp hz
        simpa [hcomp] using hclosed z)
  have hRcard : R.card = 180 := by
    exact degree_sixteen_fourLayer_used_exterior_card_eq_oneEighty
      G hfree hmin hcard c₀ hregChild hcardChild
  refine ⟨hsum.trans hRcard, ?_⟩
  intro e he
  have hrepR : componentRepresentative D e ∈ R :=
    (Finset.mem_filter.mp he).2
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hdvd := degree_sixteen_minimumLayer_used_component_base_card_dvd
    G hfree hmin hcard c₀ hc₀min
      (componentRepresentative D e) hrepR
  have hrep : D.connectedComponentMk (componentRepresentative D e) = e :=
    (ConnectedComponent.mem_supp_iff e
      (componentRepresentative D e)).mp (componentRepresentative_mem D e)
  rwa [hc₀three, hrep] at hdvd

/-- In the four-layer branch, every defect component meeting the used
exterior has order at least six.  Its order is a positive multiple of the
minimum order three, and equality would put its representative back in the
minimum layer, contrary to the exterior-cell separation. -/
theorem degree_sixteen_fourLayer_used_component_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he : componentRepresentative (secondOrderDefectGraph G) e ∈
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    6 ≤ e.supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hlower : 3 ≤ e.supp.ncard := by
    simpa [hc₀three] using hc₀min e
  have hdvd : 3 ∣ e.supp.ncard := by
    have hp := degree_sixteen_fourLayer_used_component_order_package
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
    exact hp.2 e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [D, R] using he⟩)
  have hne : e.supp.ncard ≠ 3 := by
    intro heq
    have heqBase : e.supp.ncard = c₀.supp.ncard := by omega
    let c : minimumLayerComponent D c₀ := ⟨e, heqBase⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨componentRepresentative D e, componentRepresentative_mem D e⟩⟩
    have hrepU : componentRepresentative D e ∈ U :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have houtside := minimumLayer_externalBiUnion_subset_complement G D c₀ he
    exact (Finset.mem_sdiff.mp houtside).2 hrepU
  rcases hdvd with ⟨k, hk⟩
  omega

/-- A quotient entry at least two from a used component into any defect
component forces divisibility of the target order by the used order. -/
theorem degree_sixteen_component_order_dvd_of_two_le_quotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (hq : 2 ≤ componentQuotientMatrix G (secondOrderDefectGraph G) e o) :
    e.supp.ncard ∣ o.supp.ncard := by
  by_contra hndvd
  have hle := secondOrder_componentQuotientMatrix_le_one_of_not_dvd
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o hndvd
  omega

/-- Summed detailed balance across the used-exterior component partition.
Every orphan has exactly fifteen service neighbors, so its weighted incoming
quotient mass from used components is `15 * |O|`. -/
theorem degree_sixteen_fourLayer_used_to_orphan_edge_mass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : componentRepresentative (secondOrderDefectGraph G) o ∈
      (Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent =>
      componentRepresentative D e ∈ R)
    (∑ e ∈ C, e.supp.ncard * componentQuotientMatrix G D e o) =
      o.supp.ncard * 15 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion
    (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent =>
    componentRepresentative D e ∈ R)
  have hclosed : ∀ y : V,
      y ∈ R ↔ componentRepresentative D (D.connectedComponentMk y) ∈ R := by
    intro y
    constructor
    · intro hy
      exact degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild) y hy
          (componentRepresentative_mem D (D.connectedComponentMk y))
    · intro hr
      have hsub := degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild)
          (componentRepresentative D (D.connectedComponentMk y)) hr
      have hrepComp : D.connectedComponentMk
          (componentRepresentative D (D.connectedComponentMk y)) =
          D.connectedComponentMk y :=
        (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y)
          (componentRepresentative D (D.connectedComponentMk y))).mp
            (componentRepresentative_mem D (D.connectedComponentMk y))
      apply hsub
      rw [ConnectedComponent.mem_supp_iff, hrepComp]
  have hsumQ : (∑ e ∈ C, componentQuotientMatrix G D o e) = 15 := by
    rw [sum_componentQuotient_filter_eq_inter_neighbor_card_of_component_closed
      G D R hclosed o]
    have hoData := Finset.mem_sdiff.mp ho
    have hoOutside : componentRepresentative D o ∉
        minimumLayerImageFinset D c₀ :=
      (Finset.mem_sdiff.mp hoData.1).2
    have hoUnused : componentRepresentative D o ∉ R := hoData.2
    simpa [R, D] using minimumLayer_orphan_used_exterior_neighbor_card
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild)
        (componentRepresentative D o) hoOutside hoUnused
  calc
    (∑ e ∈ C, e.supp.ncard * componentQuotientMatrix G D e o) =
        ∑ e ∈ C, o.supp.ncard * componentQuotientMatrix G D o e := by
          apply Finset.sum_congr rfl
          intro e _he
          exact secondOrder_componentQuotientMatrix_balance
            G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
    _ = o.supp.ncard * (∑ e ∈ C,
        componentQuotientMatrix G D o e) := by
          simp only [Finset.mul_sum]
    _ = o.supp.ncard * 15 := by rw [hsumQ]

/-- For a named two-component orphan cell, every minimum-owner bin supplies
the exact forward mass three and reverse mass four required by the transport
contradictions. -/
theorem degree_sixteen_fourLayer_two_orphan_owner_bin_quotient_package
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁ ≠ o₂)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁, o₂})
    (a : minimumLayerComponent (secondOrderDefectGraph G) c₀) :
    let D := secondOrderDefectGraph G
    let X := Finset.univ.filter
      (fun x : minimumLayerVertex D c₀ => x.1 = a)
    let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let E := Finset.univ.filter (fun e : D.ConnectedComponent =>
      componentRepresentative D e ∈ B)
    (∀ e ∈ E, 3 ≤ e.supp.ncard ∧ e.supp.ncard ≤ 36 ∧
      3 ∣ e.supp.ncard) ∧
    (∀ e ∈ E, componentQuotientMatrix G D e o₁ +
      componentQuotientMatrix G D e o₂ = 4) ∧
    (∑ e ∈ E, componentQuotientMatrix G D o₁ e) = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := Finset.univ.filter
    (fun x : minimumLayerVertex D c₀ => x.1 = a)
  let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let E := Finset.univ.filter (fun e : D.ConnectedComponent =>
    componentRepresentative D e ∈ B)
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  have horders := (degree_sixteen_fourLayer_owner_bin_order_package
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild a).2
  have hOclosed : ∀ y : V,
      y ∈ O ↔ componentRepresentative D (D.connectedComponentMk y) ∈ O := by
    intro y
    constructor
    · intro hy
      exact degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild y hy
          (componentRepresentative_mem D (D.connectedComponentMk y))
    · intro hr
      have hsub := degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild
          (componentRepresentative D (D.connectedComponentMk y)) hr
      have hrepComp : D.connectedComponentMk
          (componentRepresentative D (D.connectedComponentMk y)) =
          D.connectedComponentMk y :=
        (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y)
          (componentRepresentative D (D.connectedComponentMk y))).mp
            (componentRepresentative_mem D (D.connectedComponentMk y))
      apply hsub
      rw [ConnectedComponent.mem_supp_iff, hrepComp]
  have ho₁O : componentRepresentative D o₁ ∈ O := by
    have : o₁ ∈ ({o₁, o₂} : Finset D.ConnectedComponent) := by simp
    rw [← hpair] at this
    exact (Finset.mem_filter.mp this).2
  have hXcard : X.card = 3 := by
    have hc₀three : c₀.supp.ncard = 3 :=
      minimumLayer_child_common_length_eq_three
        G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
          c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
    simpa [X, a.2.trans hc₀three] using minimumLayer_owner_fiber_card D c₀ a
  have hforward : (∑ e ∈ E, componentQuotientMatrix G D o₁ e) = 3 := by
    rw [sum_componentQuotient_filter_eq_inter_neighbor_card_of_component_closed
      G D B (degree_sixteen_fourLayer_owner_bin_component_closed
        G hfree hmin hcard c₀ hregChild hcardChild a) o₁]
    exact degree_sixteen_fourLayer_three_externalRows_orphan_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild X hXcard
        (componentRepresentative D o₁) ho₁O
  refine ⟨horders, ?_, hforward⟩
  intro e he
  have herepB : componentRepresentative D e ∈ B :=
    (Finset.mem_filter.mp he).2
  obtain ⟨x, hx, hrepRow⟩ := Finset.mem_biUnion.mp herepB
  have hsumO : (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O), componentQuotientMatrix G D e c) = 4 := by
    rw [sum_componentQuotient_filter_eq_inter_neighbor_card_of_component_closed
      G D O hOclosed e]
    exact degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
      G hfree hmin hcard c₀ hregChild hcardChild x hrepRow
  rw [hpair] at hsumO
  simpa [hne] using hsumO

/-- Every used component has total quotient row four into the two named
orphan components. -/
theorem degree_sixteen_fourLayer_two_orphan_used_quotient_sum_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁ ≠ o₂)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁, o₂})
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he : componentRepresentative (secondOrderDefectGraph G) e ∈
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e o₁ +
      componentQuotientMatrix G (secondOrderDefectGraph G) e o₂ = 4 := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \ R
  have hOclosed : ∀ y : V,
      y ∈ O ↔ componentRepresentative D (D.connectedComponentMk y) ∈ O := by
    intro y
    constructor
    · intro hy
      exact degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild y hy
          (componentRepresentative_mem D (D.connectedComponentMk y))
    · intro hr
      have hsub := degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild
          (componentRepresentative D (D.connectedComponentMk y)) hr
      have hrepComp : D.connectedComponentMk
          (componentRepresentative D (D.connectedComponentMk y)) =
          D.connectedComponentMk y :=
        (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y)
          (componentRepresentative D (D.connectedComponentMk y))).mp
            (componentRepresentative_mem D (D.connectedComponentMk y))
      apply hsub
      rw [ConnectedComponent.mem_supp_iff, hrepComp]
  obtain ⟨x, _hx, hrepRow⟩ := Finset.mem_biUnion.mp he
  have hsumO : (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O), componentQuotientMatrix G D e c) = 4 := by
    rw [sum_componentQuotient_filter_eq_inter_neighbor_card_of_component_closed
      G D O hOclosed e]
    exact degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
      G hfree hmin hcard c₀ hregChild hcardChild x hrepRow
  rw [hpair] at hsumO
  simpa [D, R, O, hne] using hsumO

/-- If the orphan cell is a singleton, every used component sends quotient
entry four into its unique orphan component. -/
theorem degree_sixteen_fourLayer_one_orphan_used_quotient_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o})
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he : componentRepresentative (secondOrderDefectGraph G) e ∈
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e o = 4 := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \ R
  have hOclosed : ∀ y : V,
      y ∈ O ↔ componentRepresentative D (D.connectedComponentMk y) ∈ O := by
    intro y
    constructor
    · intro hy
      exact degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild y hy
          (componentRepresentative_mem D (D.connectedComponentMk y))
    · intro hr
      have hsub := degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild
          (componentRepresentative D (D.connectedComponentMk y)) hr
      have hrepComp : D.connectedComponentMk
          (componentRepresentative D (D.connectedComponentMk y)) =
          D.connectedComponentMk y :=
        (ConnectedComponent.mem_supp_iff (D.connectedComponentMk y)
          (componentRepresentative D (D.connectedComponentMk y))).mp
            (componentRepresentative_mem D (D.connectedComponentMk y))
      apply hsub
      rw [ConnectedComponent.mem_supp_iff, hrepComp]
  obtain ⟨x, _hx, hrepRow⟩ := Finset.mem_biUnion.mp he
  have hsumO : (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent ↦
      componentRepresentative D c ∈ O), componentQuotientMatrix G D e c) = 4 := by
    rw [sum_componentQuotient_filter_eq_inter_neighbor_card_of_component_closed
      G D O hOclosed e]
    exact degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
      G hfree hmin hcard c₀ hregChild hcardChild x hrepRow
  rw [hpair] at hsumO
  simpa [D, R, O] using hsumO

/-- In the singleton order-48 orphan branch, every used defect component
has order twelve.  Forward divisibility and balance first leave orders
twelve and twenty-four; at order twenty-four the reverse quotient is two,
so reverse divisibility would force `48 ∣ 24`. -/
theorem degree_sixteen_fourLayer_one_orphan_used_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : o.supp.ncard = 48)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o})
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he : componentRepresentative (secondOrderDefectGraph G) e ∈
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    e.supp.ncard = 12 := by
  have hq := degree_sixteen_fourLayer_one_orphan_used_quotient_eq_four
    G hfree hmin hcard c₀ hregChild hcardChild o hpair e he
  have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
    G hfree hmin hcard e o (by omega)
  rw [ho] at hdvd
  have hlower := degree_sixteen_fourLayer_used_component_card_lower
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild e he
  let D := secondOrderDefectGraph G
  obtain ⟨x, _hx, hrepRow⟩ := Finset.mem_biUnion.mp he
  let a : minimumLayerComponent D c₀ := x.1
  let X := Finset.univ.filter
    (fun y : minimumLayerVertex D c₀ ↦ y.1 = a)
  let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let E := Finset.univ.filter (fun f : D.ConnectedComponent ↦
    componentRepresentative D f ∈ B)
  have heE : e ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨x, ?_, hrepRow⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hupper : e.supp.ncard ≤ 36 :=
    ((degree_sixteen_fourLayer_owner_bin_order_package
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild a).2 e heE).2.1
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hq, ho] at hbal
  have hcases : e.supp.ncard = 12 ∨ e.supp.ncard = 24 := by
    interval_cases horder : e.supp.ncard
    all_goals (try norm_num [horder] at hdvd hbal)
    all_goals (try omega)
    all_goals simp [horder]
  rcases hcases with h12 | h24
  · exact h12
  · have hreverse : componentQuotientMatrix G
        (secondOrderDefectGraph G) o e = 2 := by
      rw [h24] at hbal
      omega
    have hdvdReverse := degree_sixteen_component_order_dvd_of_two_le_quotient
      G hfree hmin hcard o e (by rw [hreverse])
    rw [ho, h24] at hdvdReverse
    norm_num at hdvdReverse

/-- In the singleton order-48 orphan branch, at most one used component has
order twelve. -/
theorem degree_sixteen_fourLayer_one_orphan_order_twelve_count_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : o.supp.ncard = 48)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o}) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    (C.filter fun e ↦ e.supp.ncard = 12).card ≤ 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  apply Finset.card_le_one.mpr
  intro e₁ he₁ e₂ he₂
  have he₁Data := Finset.mem_filter.mp he₁
  have he₂Data := Finset.mem_filter.mp he₂
  have hq₁ := degree_sixteen_fourLayer_one_orphan_used_quotient_eq_four
    G hfree hmin hcard c₀ hregChild hcardChild o hpair e₁
      (Finset.mem_filter.mp he₁Data.1).2
  have hq₂ := degree_sixteen_fourLayer_one_orphan_used_quotient_eq_four
    G hfree hmin hcard c₀ hregChild hcardChild o hpair e₂
      (Finset.mem_filter.mp he₂Data.1).2
  have hone₁ : componentQuotientMatrix G D o e₁ = 1 := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e₁ o
    dsimp only [D] at hbal ⊢
    rw [he₁Data.2, hq₁, ho] at hbal
    omega
  have hone₂ : componentQuotientMatrix G D o e₂ = 1 := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e₂ o
    dsimp only [D] at hbal ⊢
    rw [he₂Data.2, hq₂, ho] at hbal
    omega
  apply secondOrder_multipleCover_target_source_unique_of_orders
    G hfree (d := 16) (m := 4) (by norm_num) (by norm_num) hmin hcard
      (by norm_num) e₁ e₂ o
  · omega
  · omega
  · exact hone₁
  · exact hone₂

/-- A singleton order-48 orphan component is impossible.  Every used
component would have order twelve, while four-cover uniqueness permits at
most one such component; this contradicts the exact used mass 180. -/
theorem degree_sixteen_fourLayer_false_of_one_order_fortyeight_orphan
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : o.supp.ncard = 48)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o}) : False := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  have hmass : (∑ e ∈ C, e.supp.ncard) = 180 :=
    (degree_sixteen_fourLayer_used_component_order_package
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild).1
  have hle : (C.filter fun e ↦ e.supp.ncard = 12).card ≤ 1 :=
    degree_sixteen_fourLayer_one_orphan_order_twelve_count_le_one
      G hfree hmin hcard c₀ hregChild hcardChild o ho hpair
  have hall : ∀ e ∈ C, e.supp.ncard = 12 := by
    intro e he
    exact degree_sixteen_fourLayer_one_orphan_used_component_order
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild o ho hpair e
        (Finset.mem_filter.mp he).2
  have hfilter : C.filter (fun e ↦ e.supp.ncard = 12) = C := by
    apply Finset.filter_eq_self.mpr
    exact hall
  rw [hfilter] at hle
  have hnonempty : C.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hmass
    simp at hmass
  obtain ⟨e, he⟩ := hnonempty
  have hC : C = {e} := by
    ext f
    constructor
    · intro hf
      simpa using Finset.card_le_one.mp hle f hf e he
    · intro hf
      have hfe : f = e := Finset.mem_singleton.mp hf
      simpa [hfe] using he
  rw [hC] at hmass
  simp [hall e he] at hmass

/-- In the symmetric `(24,24)` orphan branch, used rows of quotient type
one or three have order twenty-four, while rows of type two have order
twelve or twenty-four. -/
theorem degree_sixteen_fourLayer_twentyfour_twentyfour_used_row_orders
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁ ≠ o₂) (ho₁ : o₁.supp.ncard = 24)
    (ho₂ : o₂.supp.ncard = 24)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁, o₂})
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he : componentRepresentative (secondOrderDefectGraph G) e ∈
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁ = 1 →
      e.supp.ncard = 24) ∧
    (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁ = 2 →
      e.supp.ncard = 12 ∨ e.supp.ncard = 24) ∧
    (componentQuotientMatrix G (secondOrderDefectGraph G) e o₁ = 3 →
      e.supp.ncard = 24) := by
  let D := secondOrderDefectGraph G
  have hsum := degree_sixteen_fourLayer_two_orphan_used_quotient_sum_eq_four
    G hfree hmin hcard c₀ hregChild hcardChild o₁ o₂ hne hpair e he
  change componentQuotientMatrix G D e o₁ +
    componentQuotientMatrix G D e o₂ = 4 at hsum
  have hlower := degree_sixteen_fourLayer_used_component_card_lower
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild e he
  have hbal₁ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o₁
  have hbal₂ := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o₂
  constructor
  · intro hq
    change componentQuotientMatrix G D e o₁ = 1 at hq
    have hother : componentQuotientMatrix G D e o₂ = 3 := by omega
    have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
      G hfree hmin hcard e o₂ (by
        simpa [D] using
          (show 2 ≤ componentQuotientMatrix G D e o₂ by omega))
    rw [ho₂] at hdvd
    have hupper : e.supp.ncard ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    rw [ho₁, hq] at hbal₁
    omega
  · constructor
    · intro hq
      change componentQuotientMatrix G D e o₁ = 2 at hq
      have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
        G hfree hmin hcard e o₁ (by
          simpa [D] using
            (show 2 ≤ componentQuotientMatrix G D e o₁ by omega))
      rw [ho₁] at hdvd
      have hupper : e.supp.ncard ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
      rw [ho₁, hq] at hbal₁
      omega
    · intro hq
      change componentQuotientMatrix G D e o₁ = 3 at hq
      have hother : componentQuotientMatrix G D e o₂ = 1 := by omega
      have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
        G hfree hmin hcard e o₁ (by
          simpa [D] using
            (show 2 ≤ componentQuotientMatrix G D e o₁ by omega))
      rw [ho₁] at hdvd
      have hupper : e.supp.ncard ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
      rw [ho₂, hother] at hbal₂
      omega

/-- In a `(12,36)` orphan pair, no used component can have quotient entry
two or three into the order-twelve component.  Periodicity makes its order
divide twelve; the complementary row entry and detailed balance against
the order-thirty-six component then give the numerical contradiction. -/
theorem degree_sixteen_fourLayer_twelve_thirtysix_no_two_or_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁₂ o₃₆ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁₂ ≠ o₃₆) (ho₁₂ : o₁₂.supp.ncard = 12)
    (ho₃₆ : o₃₆.supp.ncard = 36)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁₂, o₃₆})
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he : componentRepresentative (secondOrderDefectGraph G) e ∈
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀)) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e o₁₂ ≠ 2 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e o₁₂ ≠ 3 := by
  let D := secondOrderDefectGraph G
  have hlower := degree_sixteen_fourLayer_used_component_card_lower
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild e he
  have hsum := degree_sixteen_fourLayer_two_orphan_used_quotient_sum_eq_four
    G hfree hmin hcard c₀ hregChild hcardChild o₁₂ o₃₆ hne hpair e he
  have hbalance := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o₃₆
  constructor <;> intro hq
  · have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
      G hfree hmin hcard e o₁₂ (by omega)
    rw [ho₁₂] at hdvd
    have hupper : e.supp.ncard ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    rw [ho₃₆] at hbalance
    interval_cases horder : e.supp.ncard <;> omega
  · have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
      G hfree hmin hcard e o₁₂ (by omega)
    rw [ho₁₂] at hdvd
    have hupper : e.supp.ncard ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    rw [ho₃₆] at hbalance
    interval_cases horder : e.supp.ncard <;> omega

/-- In the four-layer branch, every used-exterior defect cycle has order a
multiple of three. -/
theorem degree_sixteen_fourLayer_used_component_card_dvd_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    3 ∣ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  have hbase : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hdvd := degree_sixteen_minimumLayer_used_component_base_card_dvd
    G hfree hmin hcard c₀ hc₀min z hz
  rwa [hbase] at hdvd

/-- In the four-layer branch, a cut from a non-3-divisible component into
a used R component has O-to-R quotient entry divisible by three.  For an
orphan component, whose total R row is fifteen, this restricts its positive
entry multiset to a partition of fifteen into positive multiples of three. -/
theorem degree_sixteen_fourLayer_nonThree_to_used_quotient_dvd_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (zR z : V)
    (hzR : zR ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (hnot : ¬ 3 ∣
      ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) :
    3 ∣ componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk z)
      ((secondOrderDefectGraph G).connectedComponentMk zR) := by
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk zR
  let o := D.connectedComponentMk z
  have heDvd : 3 ∣ e.supp.ncard :=
    degree_sixteen_fourLayer_used_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild zR hzR
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  exact three_dvd_right_of_three_dvd_left_balance_not_dvd_right
    e.supp.ncard o.supp.ncard
      (componentQuotientMatrix G D e o)
      (componentQuotientMatrix G D o e)
      heDvd (by simpa [o] using hnot) hbal

/-- Reduced balance for a three-divisible R order and a three-divisible
O-to-R quotient entry.  Writing `|R| = 3k` and `Q(O,R) = 3b` leaves the
small transport equation `k Q(R,O) = |O| b`. -/
theorem degree_sixteen_fourLayer_threeDivisible_cut_reduced_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (heDvd : 3 ∣ e.supp.ncard)
    (hqDvd : 3 ∣ componentQuotientMatrix G
      (secondOrderDefectGraph G) o e) :
    ∃ k b : ℕ,
      e.supp.ncard = 3 * k ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) o e = 3 * b ∧
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        o.supp.ncard * b := by
  obtain ⟨k, hk⟩ := heDvd
  obtain ⟨b, hb⟩ := hqDvd
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hk, hb] at hbal
  have hreduced :
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        o.supp.ncard * b := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    calc
      3 * (k * componentQuotientMatrix G (secondOrderDefectGraph G) e o) =
          o.supp.ncard * (3 * b) := by simpa [mul_assoc] using hbal
      _ = 3 * (o.supp.ncard * b) := by ring
  exact ⟨k, b, hk, hb, hreduced⟩

/-- Reduced detailed balance when both component orders are 3-divisible in
the four-layer branch.  Writing the R and O orders as `3k` and `3m` leaves
`k Q(R,O) = m Q(O,R)`, so the remaining transport rows can be enumerated
using only the two reduced component orders. -/
theorem degree_sixteen_fourLayer_threeDivisible_orders_cut_reduced_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (e o : (secondOrderDefectGraph G).ConnectedComponent)
    (heDvd : 3 ∣ e.supp.ncard) (hoDvd : 3 ∣ o.supp.ncard) :
    ∃ k m : ℕ,
      e.supp.ncard = 3 * k ∧ o.supp.ncard = 3 * m ∧
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        m * componentQuotientMatrix G (secondOrderDefectGraph G) o e := by
  obtain ⟨k, hk⟩ := heDvd
  obtain ⟨m, hm⟩ := hoDvd
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard e o
  rw [hk, hm] at hbal
  have hreduced :
      k * componentQuotientMatrix G (secondOrderDefectGraph G) e o =
        m * componentQuotientMatrix G (secondOrderDefectGraph G) o e := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    simpa [mul_assoc] using hbal
  exact ⟨k, m, hk, hm, hreduced⟩

/-- Every orphan defect component has length at least four.  The inherited
d=4 child forces the global minimum component length to be three, and every
length-three component belongs to the minimum layer, disjoint from `O`. -/
theorem degree_sixteen_fourLayer_orphan_component_card_ge_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    4 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  obtain ⟨r, hr3, hre, _⟩ :=
    secondOrderDefect_component_resolvent_chebyshev
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        (D.connectedComponentMk z) 0
  have hthree : 3 ≤ (D.connectedComponentMk z).supp.ncard := by
    rw [← hre]
    exact hr3
  have hneThree : (D.connectedComponentMk z).supp.ncard ≠ 3 := by
    intro heq
    have hcompEq : (D.connectedComponentMk z).supp.ncard = c₀.supp.ncard := by
      rw [heq, hc₀three]
    let c : minimumLayerComponent D c₀ :=
      ⟨D.connectedComponentMk z, hcompEq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    have hzU : z ∈ U := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hzU
  change 4 ≤ (D.connectedComponentMk z).supp.ncard
  omega

/-- The 180 used exterior vertices are also closed under the defect graph.
The whole exterior is component-closed, and no defect edge can cross from
the already closed orphan set into its used-exterior complement. -/
theorem degree_sixteen_fourLayer_used_exterior_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let R := Finset.univ.biUnion E
    ∀ y ∈ R, D.neighborFinset y ⊆ R := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  have hRexterior : R ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  have hOclosed : ∀ z ∈ O, D.neighborFinset z ⊆ O :=
    degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild
  intro y hyR q hqy
  have hyExt := hRexterior hyR
  let yExt : minimumLayerExteriorVertex D c₀ :=
    ⟨y, (Finset.mem_sdiff.mp hyExt).2⟩
  have hyqAdj : D.Adj y q := (D.mem_neighborFinset y q).mp hqy
  have hqOutside : q ∉ U :=
    minimumLayerExterior_closed_under_reachable D c₀ yExt hyqAdj.reachable
  have hqNotO : q ∉ O := by
    intro hqO
    have hyO : y ∈ O := hOclosed q hqO
      ((D.mem_neighborFinset q y).mpr hyqAdj.symm)
    exact (Finset.mem_sdiff.mp hyO).2 hyR
  have hqExt : q ∈ Finset.univ \ U :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hqOutside⟩
  by_contra hqNotR
  exact hqNotO (Finset.mem_sdiff.mpr ⟨hqExt, hqNotR⟩)

/-- Along an actual edge of `G`, second-order defect adjacency is exactly
triangle-free adjacency: the antipodal half of the defect union consists of
nonedges. -/
theorem secondOrderDefect_adj_iff_triangleFree_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {x y : V} (hxy : G.Adj x y) :
    (secondOrderDefectGraph G).Adj x y ↔
      (triangleFreeEdgeGraph G).Adj x y := by
  constructor
  · intro hD
    change (antipodalGraph G).Adj x y ∨
      (triangleFreeEdgeGraph G).Adj x y at hD
    rcases hD with hanti | htri
    · exact ((mem_antipodalNeighbors G x y).mp hanti).2.1 hxy |>.elim
    · exact htri
  · intro htri
    change (antipodalGraph G).Adj x y ∨
      (triangleFreeEdgeGraph G).Adj x y
    exact Or.inr htri

/-- Restricting a commuting graph pair to a vertex set closed under the
second graph preserves adjacency-matrix commutation.  Closure kills every
summand indexed outside the restricted set on both sides. -/
theorem comap_adjMatrix_comm_of_right_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S : Finset V)
    (hclosed : ∀ x ∈ S, D.neighborFinset x ⊆ S)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ) :
    (G.comap (fun x : ↥S => x.1)).adjMatrix ℤ *
        (D.comap (fun x : ↥S => x.1)).adjMatrix ℤ =
      (D.comap (fun x : ↥S => x.1)).adjMatrix ℤ *
        (G.comap (fun x : ↥S => x.1)).adjMatrix ℤ := by
  classical
  ext x y
  have hxy := congrArg (fun M : Matrix V V ℤ => M x.1 y.1) hcomm
  simp only [Matrix.mul_apply] at hxy ⊢
  have hleft :
      (∑ z : V, G.adjMatrix ℤ x.1 z * D.adjMatrix ℤ z y.1) =
        ∑ z : ↥S,
          G.adjMatrix ℤ x.1 z.1 * D.adjMatrix ℤ z.1 y.1 := by
    calc
      (∑ z : V, G.adjMatrix ℤ x.1 z * D.adjMatrix ℤ z y.1) =
          ∑ z ∈ S, G.adjMatrix ℤ x.1 z * D.adjMatrix ℤ z y.1 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ S)
            intro z hzUniv hzNotS
            by_cases hzy : D.Adj z y.1
            · have hzS := hclosed y.1 y.2
                ((D.mem_neighborFinset y.1 z).mpr hzy.symm)
              exact (hzNotS hzS).elim
            · simp [SimpleGraph.adjMatrix_apply, hzy]
      _ = ∑ z : ↥S,
          G.adjMatrix ℤ x.1 z.1 * D.adjMatrix ℤ z.1 y.1 := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
  have hright :
      (∑ z : V, D.adjMatrix ℤ x.1 z * G.adjMatrix ℤ z y.1) =
        ∑ z : ↥S,
          D.adjMatrix ℤ x.1 z.1 * G.adjMatrix ℤ z.1 y.1 := by
    calc
      (∑ z : V, D.adjMatrix ℤ x.1 z * G.adjMatrix ℤ z y.1) =
          ∑ z ∈ S, D.adjMatrix ℤ x.1 z * G.adjMatrix ℤ z y.1 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ S)
            intro z hzUniv hzNotS
            by_cases hxz : D.Adj x.1 z
            · exact (hzNotS (hclosed x.1 x.2
                ((D.mem_neighborFinset x.1 z).mpr hxz))).elim
            · simp [SimpleGraph.adjMatrix_apply, hxz]
      _ = ∑ z : ↥S,
          D.adjMatrix ℤ x.1 z.1 * G.adjMatrix ℤ z.1 y.1 := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
  rw [hleft, hright] at hxy
  simpa only [SimpleGraph.adjMatrix_apply, SimpleGraph.comap_adj] using hxy

/-- A one-regular graph commuting with another graph acts on the latter by
graph automorphisms: matching partners of adjacent vertices are adjacent. -/
theorem oneRegular_matching_maps_adj_of_adjMatrix_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (M D : SimpleGraph V) [DecidableRel M.Adj] [DecidableRel D.Adj]
    (hdegree : ∀ x, M.degree x = 1)
    (hcomm : M.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * M.adjMatrix ℤ)
    {x x' y y' : V} (hxx' : M.Adj x x') (hyy' : M.Adj y y')
    (hxy : D.Adj x y) :
    D.Adj x' y' := by
  classical
  have neighbor_eq_singleton {a b : V} (hab : M.Adj a b) :
      M.neighborFinset b = {a} := by
    have haMem : a ∈ M.neighborFinset b :=
      (M.mem_neighborFinset b a).mpr hab.symm
    have hcard : (M.neighborFinset b).card = 1 := by
      rw [M.card_neighborFinset_eq_degree, hdegree b]
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
    have haq : a = q := by simpa [hq] using haMem
    simpa [haq] using hq
  have hxN := neighbor_eq_singleton hxx'
  have hyN := neighbor_eq_singleton hyy'.symm
  have hentry := congrFun (congrFun hcomm x') y
  rw [M.adjMatrix_mul_apply, M.mul_adjMatrix_apply, hxN, hyN] at hentry
  simp only [Finset.sum_singleton] at hentry
  by_contra hnot
  simp [SimpleGraph.adjMatrix_apply, hxy, hnot] at hentry

/-- Degree in the graph pulled back to a finset subtype is the number of
ambient neighbors that remain in that finset. -/
theorem finset_comap_degree_eq_inter_neighborFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (z : ↥S) :
    (G.comap (fun x : ↥S => x.1)).degree z =
      (S ∩ G.neighborFinset z.1).card := by
  classical
  rw [← (G.comap (fun x : ↥S => x.1)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hzy : G.Adj z.1 y.1 :=
      ((G.comap (fun x : ↥S => x.1)).mem_neighborFinset z y).mp hy
    exact Finset.mem_inter.mpr
      ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr hzy⟩
  · intro y hy y' hy' hyy'
    exact Subtype.ext hyy'
  · intro y hy
    let y' : ↥S := ⟨y, (Finset.mem_inter.mp hy).1⟩
    refine ⟨y', ?_, rfl⟩
    exact ((G.comap (fun x : ↥S => x.1)).mem_neighborFinset z y').mpr
      ((G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2)

/-- On the 48 orphan vertices, the perfect-matching adjacency operator
commutes with the restricted defect two-factor. -/
theorem degree_sixteen_fourLayer_orphan_adjMatrix_comm_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    (G.comap (fun z : ↥O => z.1)).adjMatrix ℤ *
        (D.comap (fun z : ↥O => z.1)).adjMatrix ℤ =
      (D.comap (fun z : ↥O => z.1)).adjMatrix ℤ *
        (G.comap (fun z : ↥O => z.1)).adjMatrix ℤ := by
  classical
  dsimp only
  apply comap_adjMatrix_comm_of_right_closed
  · exact degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild
  · exact adjMatrix_comm_secondOrderDefect_of_even
      G hfree (by norm_num) (by norm_num) hmin hcard

/-- The orphan matching transports every defect edge to a defect edge.
Equivalently, its fixed-point-free involution is an automorphism of the
orphan defect 2-factor, giving the component stay-or-pair dichotomy. -/
theorem degree_sixteen_fourLayer_orphan_matching_maps_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let M := G.comap (fun z : ↥O => z.1)
    let DO := D.comap (fun z : ↥O => z.1)
    ∀ {x x' y y' : ↥O}, M.Adj x x' → M.Adj y y' → DO.Adj x y →
      DO.Adj x' y' := by
  classical
  dsimp only
  intro x x' y y' hxx' hyy' hxy
  apply oneRegular_matching_maps_adj_of_adjMatrix_comm
    (G.comap (fun z : ↥((Finset.univ \
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) => z.1))
    ((secondOrderDefectGraph G).comap (fun z : ↥((Finset.univ \
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) => z.1))
  · intro z
    rw [finset_comap_degree_eq_inter_neighborFinset_card]
    exact degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z.1 z.2
  · exact degree_sixteen_fourLayer_orphan_adjMatrix_comm_defect
      G hfree hmin hcard c₀ hregChild hcardChild
  · exact hxx'
  · exact hyy'
  · exact hxy

/-- The diagonal component quotient on an orphan defect cycle records
exactly whether the orphan perfect matching preserves that component.  If
the unique matching partner stays in the same defect component the diagonal
entry is one; if it is sent to a paired component the entry is zero. -/
theorem degree_sixteen_fourLayer_orphan_diagonalQuotient_eq_ite_matching_stays
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    let D := secondOrderDefectGraph G
    let c := D.connectedComponentMk z
    componentQuotientMatrix G D c c =
      if D.connectedComponentMk z' = c then 1 else 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let c := D.connectedComponentMk z
  have hzc : z ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard) c c hzc
  rw [hQ]
  have hone : (O ∩ G.neighborFinset z).card = 1 :=
    degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hz'Mem : z' ∈ O ∩ G.neighborFinset z :=
    Finset.mem_inter.mpr
      ⟨hz', (G.mem_neighborFinset z z').mpr hzz'⟩
  have hmatch : O ∩ G.neighborFinset z = {z'} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
    have hz'w : z' = w := by simpa [hw] using hz'Mem
    simpa [hz'w] using hw
  by_cases hstay : D.connectedComponentMk z' = c
  · rw [if_pos hstay]
    have hcomponent : componentNeighborFinset G D c z = {z'} := by
      ext q
      constructor
      · intro hq
        have hqData := Finset.mem_filter.mp hq
        have hqSupp : q ∈ c.supp :=
          (ConnectedComponent.mem_supp_iff c q).mpr hqData.2
        have hqO := degree_sixteen_minimumLayer_orphan_component_subset
          G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
            (by norm_num; exact hcardChild) z hz hqSupp
        have hqMatch : q ∈ O ∩ G.neighborFinset z :=
          Finset.mem_inter.mpr ⟨hqO, hqData.1⟩
        simpa [hmatch] using hqMatch
      · intro hq
        have hqz' : q = z' := by simpa using hq
        subst q
        exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset z z').mpr hzz', hstay⟩
    rw [hcomponent]
    simp
  · rw [if_neg hstay, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqSupp : q ∈ c.supp :=
      (ConnectedComponent.mem_supp_iff c q).mpr hqData.2
    have hqO := degree_sixteen_minimumLayer_orphan_component_subset
      G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
        (by norm_num; exact hcardChild) z hz hqSupp
    have hqMatch : q ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hqO, hqData.1⟩
    have hqz' : q = z' := by simpa [hmatch] using hqMatch
    apply hstay
    simpa [hqz'] using hqData.2

/-- If an orphan matching edge stays within one defect component, that
component has even order.  Indeed its internal quotient degree is one, so
the handshake parity for the induced component graph is exactly parity of
the component order. -/
theorem degree_sixteen_fourLayer_matching_stable_orphan_component_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z')
    (hstay : (secondOrderDefectGraph G).connectedComponentMk z' =
      (secondOrderDefectGraph G).connectedComponentMk z) :
    Even ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  let D := secondOrderDefectGraph G
  let c := D.connectedComponentMk z
  have hdiag := degree_sixteen_fourLayer_orphan_diagonalQuotient_eq_ite_matching_stays
    G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz'
  have hdiagOne : componentQuotientMatrix G D c c = 1 := by
    simpa [D, c, hstay] using hdiag
  have heven := secondOrder_componentQuotientMatrix_diagonal_mul_even
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c
  rw [hdiagOne, mul_one] at heven
  exact heven

/-- If an orphan matching edge crosses between two defect components, those
components have equal order.  The matching is the unique orphan neighbor at
both endpoints, so both cross-quotient entries are one; detailed balance
then identifies the component orders. -/
theorem degree_sixteen_fourLayer_matched_orphan_component_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard =
      ((secondOrderDefectGraph G).connectedComponentMk z').supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let c := D.connectedComponentMk z
  let e := D.connectedComponentMk z'
  have hquotient (x x' : V) (hx : x ∈ O) (hx' : x' ∈ O)
      (hxx' : G.Adj x x') :
      componentQuotientMatrix G D (D.connectedComponentMk x)
          (D.connectedComponentMk x') = 1 := by
    have hxSupp : x ∈ (D.connectedComponentMk x).supp :=
      ConnectedComponent.connectedComponentMk_mem
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (D.connectedComponentMk x) (D.connectedComponentMk x') hxSupp]
    have hone : (O ∩ G.neighborFinset x).card = 1 :=
      degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
        G hfree hmin hcard c₀ hregChild hcardChild x hx
    have hx'Mem : x' ∈ O ∩ G.neighborFinset x :=
      Finset.mem_inter.mpr
        ⟨hx', (G.mem_neighborFinset x x').mpr hxx'⟩
    have hmatch : O ∩ G.neighborFinset x = {x'} := by
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
      have hx'w : x' = w := by simpa [hw] using hx'Mem
      simpa [hx'w] using hw
    have hcomponent :
        componentNeighborFinset G D (D.connectedComponentMk x') x = {x'} := by
      ext q
      constructor
      · intro hq
        have hqData := Finset.mem_filter.mp hq
        have hqSupp : q ∈ (D.connectedComponentMk x').supp :=
          (ConnectedComponent.mem_supp_iff (D.connectedComponentMk x') q).mpr
            hqData.2
        have hqO := degree_sixteen_fourLayer_orphan_component_subset
          G hfree hmin hcard c₀ hregChild hcardChild x' hx' hqSupp
        have hqMatch : q ∈ O ∩ G.neighborFinset x :=
          Finset.mem_inter.mpr ⟨hqO, hqData.1⟩
        simpa [hmatch] using hqMatch
      · intro hq
        have hqx' : q = x' := by simpa using hq
        subst q
        exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset x x').mpr hxx', rfl⟩
    rw [hcomponent]
    simp
  have hce : componentQuotientMatrix G D c e = 1 := by
    simpa [c, e] using hquotient z z' hz hz' hzz'
  have hec : componentQuotientMatrix G D e c = 1 := by
    simpa [c, e] using hquotient z' z hz' hz hzz'.symm
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e
  rw [hce, hec, mul_one, mul_one] at hbal
  exact hbal

/-- An odd-order orphan component cannot be fixed by the orphan matching.
Its matching partner lies in a distinct component (necessarily of the same
order by the preceding theorem), giving the odd-part pairing rule for the
`O48` partition. -/
theorem degree_sixteen_fourLayer_odd_orphan_component_matching_crosses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z')
    (hodd : Odd
      ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) :
    (secondOrderDefectGraph G).connectedComponentMk z' ≠
      (secondOrderDefectGraph G).connectedComponentMk z := by
  intro hstay
  have heven := degree_sixteen_fourLayer_matching_stable_orphan_component_even
    G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz' hstay
  exact Nat.not_even_iff_odd.mpr hodd heven

/-- Orphan components of different orders are anticomplete in `G`.  Any
orphan--orphan edge is an edge of the unique orphan perfect matching, and
the matching can only join defect components of equal order. -/
theorem degree_sixteen_fourLayer_unequal_orphan_components_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hne : ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard ≠
      ((secondOrderDefectGraph G).connectedComponentMk z').supp.ncard) :
    ¬G.Adj z z' := by
  intro hzz'
  exact hne (degree_sixteen_fourLayer_matched_orphan_component_card_eq
    G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz')

/-- Every orphan defect component in the four-layer branch has order
divisible by three.  Split an arbitrary quotient target by its
minimum/used/orphan cell.  Minimum and used components have three-divisible
order; unequal orphan components are anticomplete, while equal orphan
components contribute a matching quotient of at most one. -/
theorem degree_sixteen_fourLayer_orphan_component_card_dvd_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    3 ∣ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  let c := D.connectedComponentMk z
  have hbase : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hzc : z ∈ c.supp := by simp [c]
  have hregD : ∀ x : V, D.degree x = 2 := by
    simpa [D] using secondOrderDefectGraph_degree_eq_two G hfree
      (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ := by
    simpa [D] using adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  apply degree_sixteen_component_card_dvd_three_of_zero_equal_or_three
    G hfree hmin hcard c
  intro e
  let w := componentRepresentative D e
  have hwe : D.connectedComponentMk w = e :=
    (ConnectedComponent.mem_supp_iff e w).mp (componentRepresentative_mem D e)
  by_cases hwU : w ∈ U
  · right; right
    change w ∈ minimumLayerImageFinset D c₀ at hwU
    rw [minimumLayerImageFinset] at hwU
    obtain ⟨x, _hx, hxw⟩ := Finset.mem_image.mp hwU
    have hwx : D.connectedComponentMk w = x.1.1 :=
      (ConnectedComponent.mem_supp_iff x.1.1 w).mp (by
        change w ∈ x.1.1.supp
        rw [← hxw]
        exact x.2.2)
    rw [← hwe, hwx, x.1.2, hbase]
  by_cases hwR : w ∈ R
  · right; right
    have hdvd := degree_sixteen_fourLayer_used_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild w hwR
    rwa [hwe] at hdvd
  have hwO : w ∈ O := by
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwU⟩, hwR⟩
  have hesub : e.supp ⊆ (O : Set V) := by
    rw [← hwe]
    exact degree_sixteen_fourLayer_orphan_component_subset
      G hfree hmin hcard c₀ hregChild hcardChild w hwO
  by_cases hsize : c.supp.ncard = e.supp.ncard
  · right; left
    refine ⟨hsize, ?_⟩
    rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm c e hzc]
    calc
      (componentNeighborFinset G D e z).card ≤
          (O ∩ G.neighborFinset z).card := Finset.card_le_card (by
        intro q hq
        obtain ⟨hqG, hqe⟩ := Finset.mem_filter.mp hq
        apply Finset.mem_inter.mpr
        refine ⟨hesub ?_, hqG⟩
        exact (ConnectedComponent.mem_supp_iff e q).mpr hqe)
      _ = 1 := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
        G hfree hmin hcard c₀ hregChild hcardChild z hz
  · left
    rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm c e hzc]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    obtain ⟨hqG, hqe⟩ := Finset.mem_filter.mp hq
    have hqO : q ∈ O := hesub
      ((ConnectedComponent.mem_supp_iff e q).mpr hqe)
    have hqe' : (secondOrderDefectGraph G).connectedComponentMk q = e := by
      simpa [D] using hqe
    have hne' :
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard ≠
          ((secondOrderDefectGraph G).connectedComponentMk q).supp.ncard := by
      intro heqsize
      apply hsize
      simpa [c, D, hqe'] using heqsize
    exact degree_sixteen_fourLayer_unequal_orphan_components_not_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hqO hne'
        ((G.mem_neighborFinset z q).mp hqG)

/-- Every four-layer orphan component has order at least six: its order is
at least four and divisible by three. -/
theorem degree_sixteen_fourLayer_orphan_component_card_ge_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    6 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  have hfour := degree_sixteen_fourLayer_orphan_component_card_ge_four
    G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hthree := degree_sixteen_fourLayer_orphan_component_card_dvd_three
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild z hz
  obtain ⟨k, hk⟩ := hthree
  omega

/-- The orders of all four-layer orphan defect components sum to the exact
orphan-cell cardinality, forty-eight. -/
theorem degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O), c.supp.ncard) = 48 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  have hclosed : ∀ (c : D.ConnectedComponent) (z : V), z ∈ c.supp →
      (z ∈ O ↔ componentRepresentative D c ∈ O) := by
    intro c z hzc
    constructor
    · intro hzO
      have hsub := degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild z hzO
      have hcz : D.connectedComponentMk z = c :=
        (ConnectedComponent.mem_supp_iff c z).mp hzc
      rw [hcz] at hsub
      exact hsub (componentRepresentative_mem D c)
    · intro hrepO
      have hsub := degree_sixteen_fourLayer_orphan_component_subset
        G hfree hmin hcard c₀ hregChild hcardChild
          (componentRepresentative D c) hrepO
      have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
        (ConnectedComponent.mem_supp_iff c
          (componentRepresentative D c)).mp (componentRepresentative_mem D c)
      rw [hrep] at hsub
      exact hsub hzc
  calc
    (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
        componentRepresentative D c ∈ O), c.supp.ncard) = O.card :=
      sum_component_sizes_filter_eq_card_of_component_closed D O hclosed
    _ = 48 := degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild

/-- There are at most eight orphan defect components in the four-layer
branch: their orders sum to forty-eight and each is a multiple of three of
size at least four, hence at least six. -/
theorem degree_sixteen_fourLayer_orphan_component_count_le_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    (Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)).card ≤ 8 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply card_le_eight_of_sum_eq_fortyEight_of_six_le C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    have hfour := degree_sixteen_fourLayer_orphan_component_card_ge_four
      G hfree hmin hcard c₀ hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hthree := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    rw [hrep] at hfour hthree
    obtain ⟨k, hk⟩ := hthree
    omega

/-- Exact finite range for the four-layer orphan-component count.  The cell
has positive mass forty-eight, so the selected component family is nonempty;
the preceding size bound gives the upper endpoint eight. -/
theorem degree_sixteen_fourLayer_orphan_component_count_between_one_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    1 ≤ C.card ∧ C.card ≤ 8 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  have hsum :=
    degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  change (∑ c ∈ C, c.supp.ncard) = 48 at hsum
  have hpos : 0 < C.card := by
    by_contra h
    have hzero : C.card = 0 := Nat.eq_zero_of_not_pos h
    have hempty : C = ∅ := Finset.card_eq_zero.mp hzero
    rw [hempty] at hsum
    simp at hsum
  refine ⟨hpos, ?_⟩
  exact degree_sixteen_fourLayer_orphan_component_count_le_eight
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild

/-- If the four-layer orphan cell has eight defect components, all eight
have order six. -/
theorem degree_sixteen_fourLayer_eight_orphan_components_all_order_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 8) :
    ∀ c ∈ Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
          componentRepresentative (secondOrderDefectGraph G) c ∈
            (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
              Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
                (secondOrderDefectGraph G) c₀)),
      c.supp.ncard = 6 := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply all_eq_six_of_card_eq_eight_sum_eq_fortyEight_of_six_le C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge

/-- An odd local-excess ledger cannot be assembled from even component
contributions.  This tiny parity kernel is the arithmetic endpoint for the
order-six orphan elimination: its local excess is `6 - 3 = 3`, whereas the
minimum, used, and orphan target cells will each contribute even terms. -/
theorem false_of_localExcess_three_of_even_terms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ) (hsum : (∑ i, f i) = 3)
    (heven : ∀ i, Even (f i)) : False := by
  have htwo : (2 : ℤ) ∣ ∑ i, f i := by
    apply Finset.dvd_sum
    intro i _hi
    exact even_iff_two_dvd.mp (heven i)
  rw [hsum] at htwo
  norm_num at htwo

/-- A cut from an order-six source into a target of order at least six has
even local-excess contribution whenever a reverse multiple cover forces the
target order to divide six.  This is the used-cell arithmetic in the
order-six orphan contradiction. -/
theorem orderSix_localExcess_term_even_of_reverse_cover_divisibility
    (r a b : ℕ) (hr : 6 ≤ r) (hbal : 6 * a = r * b)
    (hdvd : 2 ≤ b → r ∣ 6) :
    Even ((a : ℤ) * (b : ℤ) - (a : ℤ)) := by
  by_cases hb : 2 ≤ b
  · have hrle : r ≤ 6 := Nat.le_of_dvd (by norm_num) (hdvd hb)
    have hre : r = 6 := by omega
    rw [hre] at hbal
    have hab : a = b := Nat.eq_of_mul_eq_mul_left (by norm_num) hbal
    rw [hab]
    convert Int.even_mul_pred_self (b : ℤ) using 1 <;> ring
  · have hble : b ≤ 1 := by omega
    interval_cases b
    · have ha : a = 0 := by omega
      simp [ha]
    · simp

/-- An orphan component has zero quotient into every minimum-layer
component.  Otherwise a witnessing ambient edge places the orphan endpoint
in the corresponding external-neighborhood row, contrary to the definition
of the orphan cell. -/
theorem degree_sixteen_fourLayer_orphan_to_minimum_quotient_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    {z : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (heU : componentRepresentative (secondOrderDefectGraph G) e ∈
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀) :
    componentQuotientMatrix G (secondOrderDefectGraph G)
      ((secondOrderDefectGraph G).connectedComponentMk z) e = 0 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let o := D.connectedComponentMk z
  have hregD : ∀ x : V, D.degree x = 2 := by
    simpa [D] using secondOrderDefectGraph_degree_eq_two G hfree
      (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ := by
    simpa [D] using adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hzo : z ∈ o.supp := ConnectedComponent.connectedComponentMk_mem
  rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm o e hzo]
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  obtain ⟨hqG, hqe⟩ := Finset.mem_filter.mp hq
  change componentRepresentative D e ∈ Finset.univ.image
    (minimumLayerVertexValue (D := D) (c₀ := c₀)) at heU
  obtain ⟨x, _hx, hxw⟩ := Finset.mem_image.mp heU
  have hwe : D.connectedComponentMk (componentRepresentative D e) = e :=
    (ConnectedComponent.mem_supp_iff e
      (componentRepresentative D e)).mp (componentRepresentative_mem D e)
  have hwx : D.connectedComponentMk (componentRepresentative D e) = x.1.1 :=
    (ConnectedComponent.mem_supp_iff x.1.1
      (componentRepresentative D e)).mp (by
        change componentRepresentative D e ∈ x.1.1.supp
        rw [← hxw]
        exact x.2.2)
  have hqSupp : q ∈ x.1.1.supp := by
    rw [ConnectedComponent.mem_supp_iff, ← hwx, hwe]
    exact hqe
  let y : minimumLayerVertex D c₀ :=
    ⟨x.1, ⟨q, hqSupp⟩⟩
  have hzU : z ∉ U := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzRow : z ∈ minimumLayerExternalNeighborFinset G D c₀ y := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(G.mem_neighborFinset q z).mpr ?_, hzU⟩
    exact ((G.mem_neighborFinset z q).mp hqG).symm
  have hzR : z ∈ R := Finset.mem_biUnion.mpr
    ⟨y, Finset.mem_univ _, hzRow⟩
  exact (Finset.mem_sdiff.mp hz).2 hzR

/-- **No order-six orphan component exists in the four-layer branch.**
The local excess of such a component is three.  Minimum-layer targets have
zero quotient, orphan targets contribute zero through the perfect matching,
and every used-target contribution is even by reverse-cover divisibility.
Thus the local-excess ledger would express three as a sum of even integers. -/
theorem false_of_degree_sixteen_fourLayer_orderSix_orphan
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (ho : ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard = 6) :
    False := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  let o := D.connectedComponentMk z
  let f : D.ConnectedComponent → ℤ := fun e =>
    (componentQuotientMatrix G D o e : ℤ) *
        (componentQuotientMatrix G D e o : ℤ) -
      (componentQuotientMatrix G D o e : ℤ)
  apply false_of_localExcess_three_of_even_terms f
  · have hlocal := secondOrder_componentQuotientMatrix_local_excess
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o
    change (∑ e, f e) = 3
    simpa [f, D, o, ho] using hlocal
  · intro e
    let w := componentRepresentative D e
    have hwe : D.connectedComponentMk w = e :=
      (ConnectedComponent.mem_supp_iff e w).mp (componentRepresentative_mem D e)
    by_cases hwU : w ∈ U
    · have hzero := degree_sixteen_fourLayer_orphan_to_minimum_quotient_eq_zero
        G hfree hmin hcard c₀ hz e (by simpa [D, U, w] using hwU)
      simp [f, D, o, hzero]
    by_cases hwR : w ∈ R
    · have hlower := degree_sixteen_fourLayer_used_component_card_lower
        G hfree hmin hcard c₀ hc₀min hregChild hcardChild e
          (by simpa [D, R, w] using hwR)
      have hbal := secondOrder_componentQuotientMatrix_balance
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard o e
      rw [ho] at hbal
      have heven := orderSix_localExcess_term_even_of_reverse_cover_divisibility
        e.supp.ncard
        (componentQuotientMatrix G D o e)
        (componentQuotientMatrix G D e o)
        hlower (by simpa [D, o] using hbal) (by
          intro htwo
          have hd := degree_sixteen_component_order_dvd_of_two_le_quotient
            G hfree hmin hcard e o htwo
          rw [ho] at hd
          exact hd)
      simpa [f, D, o] using heven
    · have hwO : w ∈ O := Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwU⟩, hwR⟩
      by_cases hsize : o.supp.ncard = e.supp.ncard
      · have hregD : ∀ x : V, D.degree x = 2 := by
          simpa [D] using secondOrderDefectGraph_degree_eq_two G hfree
            (d := 16) (by norm_num) (by norm_num) hmin hcard
        have hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
            D.adjMatrix ℝ * G.adjMatrix ℝ := by
          simpa [D] using adjMatrix_comm_secondOrderDefect_of_even_real
            G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        have hzo : z ∈ o.supp := ConnectedComponent.connectedComponentMk_mem
        have hesub : e.supp ⊆ (O : Set V) := by
          rw [← hwe]
          exact degree_sixteen_fourLayer_orphan_component_subset
            G hfree hmin hcard c₀ hregChild hcardChild w hwO
        have hle : componentQuotientMatrix G D o e ≤ 1 := by
          rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm o e hzo]
          calc
            (componentNeighborFinset G D e z).card ≤
                (O ∩ G.neighborFinset z).card := Finset.card_le_card (by
              intro q hq
              obtain ⟨hqG, hqe⟩ := Finset.mem_filter.mp hq
              exact Finset.mem_inter.mpr
                ⟨hesub ((ConnectedComponent.mem_supp_iff e q).mpr hqe), hqG⟩)
            _ = 1 := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
              G hfree hmin hcard c₀ hregChild hcardChild z hz
        have hzero := degree_sixteen_equalSize_localExcess_term_eq_zero_of_quotient_le_one
          G hfree hmin hcard o e hsize hle
        have hfe : f e = 0 := by simpa [f, D, o] using hzero
        rw [hfe]
        exact ⟨0, by norm_num⟩
      · have hzero : componentQuotientMatrix G D o e = 0 := by
          have hregD : ∀ x : V, D.degree x = 2 := by
            simpa [D] using secondOrderDefectGraph_degree_eq_two G hfree
              (d := 16) (by norm_num) (by norm_num) hmin hcard
          have hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
              D.adjMatrix ℝ * G.adjMatrix ℝ := by
            simpa [D] using adjMatrix_comm_secondOrderDefect_of_even_real
              G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
          have hzo : z ∈ o.supp := ConnectedComponent.connectedComponentMk_mem
          rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm o e hzo]
          apply Finset.card_eq_zero.mpr
          rw [Finset.eq_empty_iff_forall_notMem]
          intro q hq
          obtain ⟨hqG, hqe⟩ := Finset.mem_filter.mp hq
          have hesub : e.supp ⊆ (O : Set V) := by
            rw [← hwe]
            exact degree_sixteen_fourLayer_orphan_component_subset
              G hfree hmin hcard c₀ hregChild hcardChild w hwO
          have hqO := hesub ((ConnectedComponent.mem_supp_iff e q).mpr hqe)
          have hqcomp : D.connectedComponentMk q = e := hqe
          have hne : o.supp.ncard ≠ (D.connectedComponentMk q).supp.ncard := by
            simpa [hqcomp] using hsize
          exact degree_sixteen_fourLayer_unequal_orphan_components_not_adj
            G hfree hmin hcard c₀ hregChild hcardChild hz hqO hne
              ((G.mem_neighborFinset z q).mp hqG)
        simp [f, hzero]

/-- Once order-six orphan components are excluded, every orphan component
has order at least nine.  Hence the exact orphan mass forty-eight supports
at most five components. -/
theorem false_of_degree_sixteen_fourLayer_six_le_orphan_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount : 6 ≤
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card) : False := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  have hnine : ∀ c ∈ C, 9 ≤ c.supp.ncard := by
    intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rw [hrep] at hge hdvd
    by_contra hnot
    have hsix : c.supp.ncard = 6 := by
      obtain ⟨k, hk⟩ := hdvd
      omega
    exact false_of_degree_sixteen_fourLayer_orderSix_orphan
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild hrepO (by
        simpa [D, hrep] using hsix)
  have hlower : 9 * C.card ≤ ∑ c ∈ C, c.supp.ncard := by
    calc
      9 * C.card = ∑ _c ∈ C, 9 := by simp [mul_comm]
      _ ≤ ∑ c ∈ C, c.supp.ncard := by
        apply Finset.sum_le_sum
        intro c hc
        exact hnine c hc
  have hsum := degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
    G hfree hmin hcard c₀ hregChild hcardChild
  change (∑ c ∈ C, c.supp.ncard) = 48 at hsum
  change 6 ≤ C.card at hcount
  omega

/-- If the four-layer orphan cell has seven defect components, every order
is one of six, nine, or twelve. -/
theorem degree_sixteen_fourLayer_seven_orphan_component_orders
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 7) :
    ∀ c ∈ Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
          componentRepresentative (secondOrderDefectGraph G) c ∈
            (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
              Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
                (secondOrderDefectGraph G) c₀)),
      c.supp.ncard = 6 ∨ c.supp.ncard = 9 ∨ c.supp.ncard = 12 := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply seven_part_orders_eq_six_nine_or_twelve C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hdvd

/-- Exact multiset classification of the seven-component orphan branch. -/
theorem degree_sixteen_fourLayer_seven_orphan_component_count_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 7) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    let n₆ := (C.filter fun c => c.supp.ncard = 6).card
    let n₉ := (C.filter fun c => c.supp.ncard = 9).card
    let n₁₂ := (C.filter fun c => c.supp.ncard = 12).card
    (n₆ = 6 ∧ n₉ = 0 ∧ n₁₂ = 1) ∨
      (n₆ = 5 ∧ n₉ = 2 ∧ n₁₂ = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply seven_part_six_nine_twelve_count_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · exact degree_sixteen_fourLayer_seven_orphan_component_orders
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild hcount

/-- Odd orders occur with even multiplicity in the four-layer orphan
partition.  The union of all orphan components of a fixed order is preserved
by the orphan perfect matching, hence has even cardinality.  Its cardinality
is the component order times the number of selected components, and an odd
factor cannot account for that parity. -/
theorem degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (r : ℕ) (hrOdd : Odd r) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    Even ((Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O ∧ c.supp.ncard = r)).card) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O ∧ c.supp.ncard = r)
  let S := O.filter (fun z => (D.connectedComponentMk z).supp.ncard = r)
  have hcomponentClosed : ∀ (c : D.ConnectedComponent) (z : V), z ∈ c.supp →
      (z ∈ S ↔ componentRepresentative D c ∈ S) := by
    intro c z hzc
    have hcz : D.connectedComponentMk z = c :=
      (ConnectedComponent.mem_supp_iff c z).mp hzc
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    have hOclosed : z ∈ O ↔ componentRepresentative D c ∈ O := by
      constructor
      · intro hzO
        have hsub := degree_sixteen_fourLayer_orphan_component_subset
          G hfree hmin hcard c₀ hregChild hcardChild z hzO
        rw [hcz] at hsub
        exact hsub (componentRepresentative_mem D c)
      · intro hrepO
        have hsub := degree_sixteen_fourLayer_orphan_component_subset
          G hfree hmin hcard c₀ hregChild hcardChild
            (componentRepresentative D c) hrepO
        rw [hrep] at hsub
        exact hsub hzc
    simp only [S, Finset.mem_filter]
    rw [hcz, hrep, hOclosed]
  have hsum := sum_component_sizes_filter_eq_card_of_component_closed
    D S hcomponentClosed
  have hfilter : Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ S) = C := by
    ext c
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    simp [C, S, hrep]
  rw [hfilter] at hsum
  have hmass : S.card = r * C.card := by
    rw [← hsum]
    calc
      (∑ c ∈ C, c.supp.ncard) = ∑ _c ∈ C, r := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (Finset.mem_filter.mp hc).2.2
      _ = r * C.card := by simp [mul_comm]
  let H := G.induce (S : Set V)
  have hdegree : ∀ z : (S : Set V), H.degree z = 1 := by
    intro z
    have hzData := Finset.mem_filter.mp z.2
    have hzO : z.1 ∈ O := hzData.1
    have hzOrder : (D.connectedComponentMk z.1).supp.ncard = r := hzData.2
    have hcardO : (O ∩ G.neighborFinset z.1).card = 1 :=
      degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
        G hfree hmin hcard c₀ hregChild hcardChild z.1 hzO
    have hsets : S ∩ G.neighborFinset z.1 = O ∩ G.neighborFinset z.1 := by
      ext q
      constructor
      · intro hq
        have hqData := Finset.mem_inter.mp hq
        exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hqData.1).1, hqData.2⟩
      · intro hq
        have hqData := Finset.mem_inter.mp hq
        have hqOrder := degree_sixteen_fourLayer_matched_orphan_component_card_eq
          G hfree hmin hcard c₀ hregChild hcardChild hzO hqData.1
            ((G.mem_neighborFinset z.1 q).mp hqData.2)
        apply Finset.mem_inter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hqData.1, ?_⟩, hqData.2⟩
        simpa [D, hzOrder] using hqOrder.symm
    have hdegreeCard : H.degree z = (S ∩ G.neighborFinset z.1).card := by
      rw [← H.card_neighborFinset_eq_degree]
      apply Finset.card_bij (fun y _ => y.1)
      · intro y hy
        have hzy : G.Adj z.1 y.1 := (H.mem_neighborFinset z y).mp hy
        exact Finset.mem_inter.mpr
          ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr hzy⟩
      · intro y hy y' hy' hyy
        exact Subtype.ext hyy
      · intro y hy
        let y' : (S : Set V) := ⟨y, (Finset.mem_inter.mp hy).1⟩
        refine ⟨y', ?_, rfl⟩
        exact (H.mem_neighborFinset z y').mpr
          ((G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2)
    rw [hdegreeCard, hsets]
    exact hcardO
  have hsumDegrees : ∑ z : (S : Set V), H.degree z = S.card := by
    simp_rw [hdegree]
    simp
  have hSeven : Even S.card := by
    refine ⟨H.edgeFinset.card, ?_⟩
    rw [← hsumDegrees, H.sum_degrees_eq_twice_card_edges]
    simp [two_mul]
  rw [hmass] at hSeven
  rcases (Nat.even_mul.mp hSeven) with hrEven | hCEven
  · exact False.elim ((Nat.not_even_iff_odd.mpr hrOdd) hrEven)
  · exact hCEven

/- Retired with the cold-unverified n=3 census.
/-- Exact count classification of the three-component orphan branch. -/
theorem degree_sixteen_fourLayer_three_orphan_component_count_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 3) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    let n₆ := (C.filter fun c => c.supp.ncard = 6).card
    let n₉ := (C.filter fun c => c.supp.ncard = 9).card
    let n₁₂ := (C.filter fun c => c.supp.ncard = 12).card
    let n₁₅ := (C.filter fun c => c.supp.ncard = 15).card
    let n₁₈ := (C.filter fun c => c.supp.ncard = 18).card
    let n₂₁ := (C.filter fun c => c.supp.ncard = 21).card
    let n₂₄ := (C.filter fun c => c.supp.ncard = 24).card
    let n₂₇ := (C.filter fun c => c.supp.ncard = 27).card
    let n₃₀ := (C.filter fun c => c.supp.ncard = 30).card
    let n₃₃ := (C.filter fun c => c.supp.ncard = 33).card
    let n₃₆ := (C.filter fun c => c.supp.ncard = 36).card
    (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 1) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 2 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 2 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) ∨
    (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0 ∧ n₃₃ = 0 ∧ n₃₆ = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply three_part_three_divisible_count_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hdvd
  all_goals
    simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild _ (by norm_num))
-/

/-- Exact named classification of the two-component orphan branch. -/
theorem degree_sixteen_fourLayer_two_orphan_component_named_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 2) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    ∃ c d, c ≠ d ∧ C = {c, d} ∧
      ((c.supp.ncard = 6 ∧ d.supp.ncard = 42) ∨
       (c.supp.ncard = 42 ∧ d.supp.ncard = 6) ∨
       (c.supp.ncard = 12 ∧ d.supp.ncard = 36) ∨
       (c.supp.ncard = 36 ∧ d.supp.ncard = 12) ∨
       (c.supp.ncard = 18 ∧ d.supp.ncard = 30) ∨
       (c.supp.ncard = 30 ∧ d.supp.ncard = 18) ∨
       (c.supp.ncard = 24 ∧ d.supp.ncard = 24)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply two_part_three_divisible_named_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hdvd
  all_goals
    simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild _ (by norm_num))

/-- The transport gap eliminates both asymmetric extreme pairs in the named
two-orphan census.  Thus only `(12,36)`, its reverse, or `(24,24)` remain. -/
theorem degree_sixteen_fourLayer_two_orphan_remaining_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 2) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    ∃ c d, c ≠ d ∧ C = {c, d} ∧
      ((c.supp.ncard = 12 ∧ d.supp.ncard = 36) ∨
       (c.supp.ncard = 36 ∧ d.supp.ncard = 12) ∨
       (c.supp.ncard = 24 ∧ d.supp.ncard = 24)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  obtain ⟨c, d, hcd, hC, horders⟩ :=
    degree_sixteen_fourLayer_two_orphan_component_named_classification
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild hcount
  have hnonempty : Nonempty (minimumLayerVertex D c₀) :=
    Fintype.card_pos_iff.mp (by rw [hcardChild]; norm_num)
  let a : minimumLayerComponent D c₀ := (Classical.choice hnonempty).1
  let X := Finset.univ.filter
    (fun x : minimumLayerVertex D c₀ => x.1 = a)
  let B := X.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let E := Finset.univ.filter (fun e : D.ConnectedComponent =>
    componentRepresentative D e ∈ B)
  have hp := degree_sixteen_fourLayer_two_orphan_owner_bin_quotient_package
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild c d hcd hC a
  change C = {c, d} at hC
  have hCswap : C = {d, c} := by simpa [Finset.pair_comm] using hC
  have hpSwap := degree_sixteen_fourLayer_two_orphan_owner_bin_quotient_package
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild d c hcd.symm hCswap a
  refine ⟨c, d, hcd, hC, ?_⟩
  rcases horders with h6_42 | h42_6 | h12_36 | h36_12 | h18_30 | h30_18 | h24_24
  · exact (false_of_six_fortyTwo_transport_bin
      G hfree hmin hcard c d h6_42.1 h6_42.2 E hp.1 hp.2.1 hp.2.2).elim
  · exact (false_of_six_fortyTwo_transport_bin
      G hfree hmin hcard d c h42_6.2 h42_6.1 E hpSwap.1 hpSwap.2.1 hpSwap.2.2).elim
  · exact Or.inl h12_36
  · exact Or.inr (Or.inl h36_12)
  · exact (false_of_eighteen_thirty_transport_bin
      G hfree hmin hcard c d h18_30.1 h18_30.2 E hp.1 hp.2.1 hp.2.2).elim
  · exact (false_of_eighteen_thirty_transport_bin
      G hfree hmin hcard d c h30_18.2 h30_18.1 E hpSwap.1 hpSwap.2.1 hpSwap.2.2).elim
  · exact Or.inr (Or.inr h24_24)

/-- Exact classification of the singleton orphan branch. -/
theorem degree_sixteen_fourLayer_one_orphan_component_count_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 1) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    (C.filter fun c => c.supp.ncard = 48).card = 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply one_part_weight_count_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild

/- Retired with the cold-unverified n=4 census.
/-- Exact multiset classification of the four-component orphan branch. -/
theorem degree_sixteen_fourLayer_four_orphan_component_count_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 4) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    let n₆ := (C.filter fun c => c.supp.ncard = 6).card
    let n₉ := (C.filter fun c => c.supp.ncard = 9).card
    let n₁₂ := (C.filter fun c => c.supp.ncard = 12).card
    let n₁₅ := (C.filter fun c => c.supp.ncard = 15).card
    let n₁₈ := (C.filter fun c => c.supp.ncard = 18).card
    let n₂₁ := (C.filter fun c => c.supp.ncard = 21).card
    let n₂₄ := (C.filter fun c => c.supp.ncard = 24).card
    let n₂₇ := (C.filter fun c => c.supp.ncard = 27).card
    let n₃₀ := (C.filter fun c => c.supp.ncard = 30).card
    (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 1) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 2 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 1 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) ∨
      (n₆ = 0 ∧ n₉ = 0 ∧ n₁₂ = 4 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0 ∧ n₂₇ = 0 ∧ n₃₀ = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply four_part_three_divisible_count_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O := (Finset.mem_filter.mp hc).2
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hdvd
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 9 (by norm_num))
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 15 (by norm_num))
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 21 (by norm_num))
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 27 (by norm_num))

-/
/- Retired with the cold-unverified n=5 census.
/-- Exact multiset classification of the five-component orphan branch. -/
theorem degree_sixteen_fourLayer_five_orphan_component_count_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 5) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    let n₆ := (C.filter fun c => c.supp.ncard = 6).card
    let n₉ := (C.filter fun c => c.supp.ncard = 9).card
    let n₁₂ := (C.filter fun c => c.supp.ncard = 12).card
    let n₁₅ := (C.filter fun c => c.supp.ncard = 15).card
    let n₁₈ := (C.filter fun c => c.supp.ncard = 18).card
    let n₂₁ := (C.filter fun c => c.supp.ncard = 21).card
    let n₂₄ := (C.filter fun c => c.supp.ncard = 24).card
    (n₆ = 4 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 1) ∨
      (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 2 ∧ n₉ = 2 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 3 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 2 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 2 ∧ n₉ = 0 ∧ n₁₂ = 3 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 1 ∧ n₉ = 2 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) ∨
      (n₆ = 0 ∧ n₉ = 4 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0 ∧ n₂₁ = 0 ∧ n₂₄ = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply five_part_three_divisible_count_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hdvd
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 9 (by norm_num))
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 15 (by norm_num))
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 21 (by norm_num))

-/
/-- Exact multiset classification of the six-component orphan branch. -/
theorem degree_sixteen_fourLayer_six_orphan_component_count_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 6) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
      componentRepresentative D c ∈ O)
    let n₆ := (C.filter fun c => c.supp.ncard = 6).card
    let n₉ := (C.filter fun c => c.supp.ncard = 9).card
    let n₁₂ := (C.filter fun c => c.supp.ncard = 12).card
    let n₁₅ := (C.filter fun c => c.supp.ncard = 15).card
    let n₁₈ := (C.filter fun c => c.supp.ncard = 18).card
    (n₆ = 5 ∧ n₉ = 0 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 1) ∨
      (n₆ = 4 ∧ n₉ = 0 ∧ n₁₂ = 2 ∧ n₁₅ = 0 ∧ n₁₈ = 0) ∨
      (n₆ = 3 ∧ n₉ = 2 ∧ n₁₂ = 1 ∧ n₁₅ = 0 ∧ n₁₈ = 0) ∨
      (n₆ = 2 ∧ n₉ = 4 ∧ n₁₂ = 0 ∧ n₁₅ = 0 ∧ n₁₈ = 0) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent =>
    componentRepresentative D c ∈ O)
  apply six_part_three_divisible_count_classification C
    (fun c : D.ConnectedComponent => c.supp.ncard)
  · exact hcount
  · exact degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hge := degree_sixteen_fourLayer_orphan_component_card_ge_six
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hge
  · intro c hc
    have hrepO : componentRepresentative D c ∈ O :=
      (Finset.mem_filter.mp hc).2
    have hdvd := degree_sixteen_fourLayer_orphan_component_card_dvd_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        (componentRepresentative D c) hrepO
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    rwa [hrep] at hdvd
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 9 (by norm_num))
  · simpa [C, O, Finset.filter_filter] using
      (degree_sixteen_fourLayer_odd_orphan_order_multiplicity_even
        G hfree hmin hcard c₀ hregChild hcardChild 15 (by norm_num))

/-- **The `U/R/O` component-diagonal ledger at degree sixteen.**  Splitting
the nonsquare component-quotient trace by the three defect-closed residual
cells gives total diagonal mass exactly sixteen.  Representatives suffice
because each cell is a union of complete defect components. -/
theorem degree_sixteen_minimumLayer_component_diagonal_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    ((∑ c : D.ConnectedComponent,
        if componentRepresentative D c ∈ U then
          componentQuotientMatrix G D c c else 0) +
      (∑ c : D.ConnectedComponent,
        if componentRepresentative D c ∈ R then
          componentQuotientMatrix G D c c else 0)) +
      (∑ c : D.ConnectedComponent,
        if componentRepresentative D c ∈ O then
          componentQuotientMatrix G D c c else 0) = 16 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hRsub : R ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  let q : D.ConnectedComponent → ℕ :=
    fun c => componentQuotientMatrix G D c c
  have hsplit :
      ((∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ U then
            componentQuotientMatrix G D c c else 0) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ R then
            componentQuotientMatrix G D c c else 0)) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ O then
            componentQuotientMatrix G D c c else 0) =
        ∑ c : D.ConnectedComponent, componentQuotientMatrix G D c c := by
    change
      ((∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ U then q c else 0) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ R then q c else 0)) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ O then q c else 0) =
        ∑ c : D.ConnectedComponent, q c
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hxU : componentRepresentative D c ∈ U
    · have hxNotR : componentRepresentative D c ∉ R := by
        intro hxR
        exact (Finset.mem_sdiff.mp (hRsub hxR)).2 hxU
      have hxNotO : componentRepresentative D c ∉ O := by
        intro hxO
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxO).1).2 hxU
      simp [hxU, hxNotR, hxNotO]
    · by_cases hxR : componentRepresentative D c ∈ R
      · have hxNotO : componentRepresentative D c ∉ O :=
          fun hxO => (Finset.mem_sdiff.mp hxO).2 hxR
        simp [hxU, hxR, hxNotO]
      · have hxO : componentRepresentative D c ∈ O := Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxU⟩, hxR⟩
        simp [hxU, hxR, hxO]
  rw [hsplit]
  exact secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard (by norm_num)

/-- Each of the five minimum-layer defect triangles in the four-layer
branch contributes either zero or two to the component-diagonal ledger. -/
theorem degree_sixteen_fourLayer_minimumComponent_diagonal_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = c₀.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 ∨
      componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 := by
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hcOdd : Odd c.supp.ncard := by
    rw [hc, hc₀three]
    norm_num
  have heven := oddComponent_diagonalQuotient_even
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c hcOdd
  have hle := secondOrder_minimumLayer_diag_le_two
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      c₀ hc₀min c hc
  rcases heven with ⟨k, hk⟩
  interval_cases hq : componentQuotientMatrix G
    (secondOrderDefectGraph G) c c
  · exact Or.inl rfl
  · omega
  · exact Or.inr rfl

/-- **Orphan matching color classification.**  If `z-z'` is the unique
orphan matching edge at `z`, then it is a defect edge exactly when it is
triangle-free.  Every other defect edge at `z` is antipodal. -/
theorem degree_sixteen_fourLayer_orphan_matching_color
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ((triangleFreeEdgeGraph G).Adj z z' ↔
      (secondOrderDefectGraph G).Adj z z') ∧
    (∀ q, (secondOrderDefectGraph G).Adj z q → q ≠ z' →
      (antipodalGraph G).Adj z q) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hzO : z ∈ O := hz
  have hz'O : z' ∈ O := hz'
  refine ⟨(secondOrderDefect_adj_iff_triangleFree_of_adj G hzz').symm, ?_⟩
  intro q hzqD hqz'
  have hclosed := degree_sixteen_fourLayer_orphans_defect_closed
    G hfree hmin hcard c₀ hregChild hcardChild
  have hqO : q ∈ O := hclosed z hzO
    ((D.mem_neighborFinset z q).mpr hzqD)
  have hnG : ¬G.Adj z q := by
    intro hzqG
    have hone := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z hzO
    have hz'Mem : z' ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hz'O, (G.mem_neighborFinset z z').mpr hzz'⟩
    have hqMem : q ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hqO, (G.mem_neighborFinset z q).mpr hzqG⟩
    have hle : (O ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
    exact hqz' (Finset.card_le_one.mp hle q hqMem z' hz'Mem)
  change (antipodalGraph G).Adj z q ∨
    (triangleFreeEdgeGraph G).Adj z q at hzqD
  rcases hzqD with hanti | htri
  · exact hanti
  · exact (hnG ((mem_triangleFreeNeighbors G z q).mp htri).1).elim

/-- No orphan matching edge is a defect edge.  Otherwise that edge is
triangle-free while the other defect edge at the same orphan is antipodal,
contradicting exact-boundary monochromaticity of incident defect edges. -/
theorem degree_sixteen_fourLayer_orphan_matching_not_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ¬(secondOrderDefectGraph G).Adj z z' := by
  classical
  let D := secondOrderDefectGraph G
  intro hzz'D
  have hz'Mem : z' ∈ D.neighborFinset z :=
    (D.mem_neighborFinset z z').mpr hzz'D
  have hcardD : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree]
    exact secondOrderDefectGraph_degree_eq_two
      G hfree (by norm_num) (by norm_num) hmin hcard z
  have hcardErase : ((D.neighborFinset z).erase z').card = 1 := by
    rw [Finset.card_erase_of_mem hz'Mem, hcardD]
  obtain ⟨q, hqErase⟩ := Finset.card_eq_one.mp hcardErase
  have hqMemErase : q ∈ (D.neighborFinset z).erase z' := by simp [hqErase]
  have hqD : D.Adj z q :=
    (D.mem_neighborFinset z q).mp (Finset.mem_of_mem_erase hqMemErase)
  have hqne : q ≠ z' := (Finset.mem_erase.mp hqMemErase).1
  have hcolor := degree_sixteen_fourLayer_orphan_matching_color
    G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz'
  have hzqAnti : (antipodalGraph G).Adj z q := hcolor.2 q hqD hqne
  rcases secondOrderDefectGraph_incident_edges_monochromatic
      G hfree (by norm_num) (by norm_num) hmin hcard hzz'D hqD with
    hbothAnti | hbothTF
  · exact ((mem_antipodalNeighbors G z z').mp hbothAnti.1).2.1 hzz'
  · exact ((mem_antipodalNeighbors G z q).mp hzqAnti).2.1
      ((mem_triangleFreeNeighbors G z q).mp hbothTF.2).1

/-- Every orphan matching edge occupies exactly one service-block slot:
its endpoints have a common service point in a unique child row, and that
point is unique as well. -/
theorem degree_sixteen_fourLayer_orphan_matching_unique_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∃ y : V,
      y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u ∧
      G.Adj z y ∧ G.Adj z' y ∧
      ∀ v : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∀ y' : V,
        y' ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ v →
        G.Adj z y' → G.Adj z' y' → v = u ∧ y' = y := by
  classical
  have hne : z ≠ z' := G.ne_of_adj hzz'
  have hex : ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      ∃ y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u,
        G.Adj z y ∧ G.Adj z' y := by
    by_contra hnot
    push_neg at hnot
    have huncovered : ∀ u : minimumLayerVertex
        (secondOrderDefectGraph G) c₀,
        ∀ y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u,
          ¬(G.Adj z y ∧ G.Adj z' y) := by
      intro u y hy hpair
      exact hnot u y hy hpair.1 hpair.2
    have hD := degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hne huncovered
    exact degree_sixteen_fourLayer_orphan_matching_not_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz' hD
  obtain ⟨u, y, hyE, hzy, hz'y⟩ := hex
  refine ⟨u, y, hyE, hzy, hz'y, ?_⟩
  intro v y' hy'E hzy' hz'y'
  have huv := degree_sixteen_fourLayer_shared_service_row_unique
    G hfree hmin hcard c₀ hregChild hcardChild hne
      hyE hzy hz'y hy'E hzy' hz'y'
  have hcommon := common_le_one_of_not_containsC4 hfree z z' hne
  have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y).mpr hzy,
        (G.mem_neighborFinset z' y).mpr hz'y⟩
  have hy'Mem : y' ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y').mpr hzy',
        (G.mem_neighborFinset z' y').mpr hz'y'⟩
  exact ⟨huv.symm,
    Finset.card_le_one.mp hcommon y' hy'Mem y hyMem⟩

/-- Every defect edge inside the orphan subsystem is antipodal.  Its other
possible color would make it an orphan matching edge, which the preceding
theorem excludes from the defect graph. -/
theorem degree_sixteen_fourLayer_orphan_defect_adj_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z q : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzqD : (secondOrderDefectGraph G).Adj z q) :
    (antipodalGraph G).Adj z q := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  have hq : q ∈ O :=
    degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild z hz
        ((D.mem_neighborFinset z q).mpr hzqD)
  change (antipodalGraph G).Adj z q ∨
    (triangleFreeEdgeGraph G).Adj z q at hzqD
  rcases hzqD with hanti | htri
  · exact hanti
  · have hzqG : G.Adj z q :=
      ((mem_triangleFreeNeighbors G z q).mp htri).1
    exact (degree_sixteen_fourLayer_orphan_matching_not_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hq hzqG
        (Or.inr htri)).elim

/-- Every defect edge of an orphan component in the four-layer branch has
antipodal color.  This component-level wrapper eliminates all orphan color
choices from the structured encoding. -/
theorem degree_sixteen_fourLayer_orphan_component_all_edges_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    ∀ x ∈ ((secondOrderDefectGraph G).connectedComponentMk z).supp,
      ∀ y, (secondOrderDefectGraph G).Adj x y →
        (antipodalGraph G).Adj x y := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  have hsubset := degree_sixteen_fourLayer_orphan_component_subset
    G hfree hmin hcard c₀ hregChild hcardChild z hz
  intro x hx y hxy
  have hxO : x ∈ O := hsubset hx
  exact degree_sixteen_fourLayer_orphan_defect_adj_antipodal
    G hfree hmin hcard c₀ hregChild hcardChild hxO hxy

/-- **Exact collision/leave law.**  For distinct orphans, being an edge of
the defect 2-factor is equivalent to sharing no service point in any row.
Thus the 15 parallel classes cover every non-defect pair exactly once and
leave precisely `D[O]`. -/
theorem degree_sixteen_fourLayer_orphan_defect_adj_iff_no_shared_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : z ≠ z') :
    (secondOrderDefectGraph G).Adj z z' ↔
      ∀ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        ∀ y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u,
          ¬(G.Adj z y ∧ G.Adj z' y) := by
  classical
  constructor
  · intro hD u y hyE hpair
    have hanti := degree_sixteen_fourLayer_orphan_defect_adj_antipodal
      G hfree hmin hcard c₀ hregChild hcardChild hz hD
    have hzero := ((mem_antipodalNeighbors G z z').mp hanti).2.2
    have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z y).mpr hpair.1,
          (G.mem_neighborFinset z' y).mpr hpair.2⟩
    rw [Finset.card_eq_zero.mp hzero] at hyMem
    exact Finset.notMem_empty y hyMem
  · exact degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz'

/-- Complementary form of the exact leave law: every non-defect orphan
pair occurs together at one unique service point in one unique row. -/
theorem degree_sixteen_fourLayer_nondefect_orphans_unique_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : z ≠ z')
    (hnotD : ¬(secondOrderDefectGraph G).Adj z z') :
    ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∃ y : V,
      y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u ∧
      G.Adj z y ∧ G.Adj z' y ∧
      ∀ v : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∀ y' : V,
        y' ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ v →
        G.Adj z y' → G.Adj z' y' → v = u ∧ y' = y := by
  classical
  have hcollision : ¬(∀ u : minimumLayerVertex
      (secondOrderDefectGraph G) c₀,
      ∀ y ∈ minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u,
        ¬(G.Adj z y ∧ G.Adj z' y)) := by
    intro hnone
    exact hnotD ((degree_sixteen_fourLayer_orphan_defect_adj_iff_no_shared_service
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz').mpr hnone)
  push_neg at hcollision
  obtain ⟨u, y, hyE, hzy, hz'y⟩ := hcollision
  refine ⟨u, y, hyE, hzy, hz'y, ?_⟩
  intro v y' hy'E hzy' hz'y'
  have huv := degree_sixteen_fourLayer_shared_service_row_unique
    G hfree hmin hcard c₀ hregChild hcardChild hzz'
      hyE hzy hz'y hy'E hzy' hz'y'
  have hcommon := common_le_one_of_not_containsC4 hfree z z' hzz'
  have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y).mpr hzy,
        (G.mem_neighborFinset z' y).mpr hz'y⟩
  have hy'Mem : y' ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y').mpr hzy',
        (G.mem_neighborFinset z' y').mpr hz'y'⟩
  exact ⟨huv.symm, Finset.card_le_one.mp hcommon y' hy'Mem y hyMem⟩

/-- Exact service-cherry count on one named orphan component: service-centered
cherries with both endpoints in the component are in bijection with its
two-element non-defect subsets. -/
theorem degree_sixteen_fourLayer_orphan_component_service_cherries_eq_nondefect_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : componentRepresentative (secondOrderDefectGraph G) o ∈
      (Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀)
    let B := o.supp.toFinite.toFinset
    let good := fun e : Finset V =>
      ∀ z ∈ e, ∀ z' ∈ e, z ≠ z' → ¬D.Adj z z'
    (∑ y ∈ R, ((B ∩ G.neighborFinset y).card).choose 2) =
      ((B.powersetCard 2).filter good).card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion
    (minimumLayerExternalNeighborFinset G D c₀)
  let B := o.supp.toFinite.toFinset
  let good := fun e : Finset V =>
    ∀ z ∈ e, ∀ z' ∈ e, z ≠ z' → ¬D.Adj z z'
  have hsubO : o.supp ⊆
      (((Finset.univ \ minimumLayerImageFinset D c₀) \ R : Finset V) : Set V) := by
    have hrepComp : D.connectedComponentMk (componentRepresentative D o) = o :=
      (ConnectedComponent.mem_supp_iff o
        (componentRepresentative D o)).mp (componentRepresentative_mem D o)
    have hsub := degree_sixteen_fourLayer_orphan_component_subset
      G hfree hmin hcard c₀ hregChild hcardChild
        (componentRepresentative D o) ho
    simpa [hrepComp, D, R] using hsub
  apply sum_choose_inter_neighbor_eq_card_good_pairs_of_unique_center
    G R B good
  · intro y hyR e he
    intro z hz z' hz' hzz' hD
    have heData := Finset.mem_powersetCard.mp he
    have hzData := Finset.mem_inter.mp (heData.1 hz)
    have hz'Data := Finset.mem_inter.mp (heData.1 hz')
    have hzSupp : z ∈ o.supp := by simpa [B] using hzData.1
    have hz'Supp : z' ∈ o.supp := by simpa [B] using hz'Data.1
    have hzO := hsubO hzSupp
    have hz'O := hsubO hz'Supp
    obtain ⟨u, _hu, hyu⟩ := Finset.mem_biUnion.mp hyR
    have hnone :=
      (degree_sixteen_fourLayer_orphan_defect_adj_iff_no_shared_service
        G hfree hmin hcard c₀ hregChild hcardChild hzO hz'O hzz').mp hD
    exact hnone u y hyu
      ⟨((G.mem_neighborFinset y z).mp hzData.2).symm,
        ((G.mem_neighborFinset y z').mp hz'Data.2).symm⟩
  · intro e heB heGood
    obtain ⟨z, z', hzz', heq⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp heB).2
    have hzB : z ∈ B := (Finset.mem_powersetCard.mp heB).1 (by simp [heq])
    have hz'B : z' ∈ B := (Finset.mem_powersetCard.mp heB).1 (by simp [heq])
    have hzSupp : z ∈ o.supp := by simpa [B] using hzB
    have hz'Supp : z' ∈ o.supp := by simpa [B] using hz'B
    have hzO := hsubO hzSupp
    have hz'O := hsubO hz'Supp
    have hnotD : ¬D.Adj z z' :=
      heGood z (by simp [heq]) z' (by simp [heq]) hzz'
    obtain ⟨u, y, hyu, hzy, hz'y, hunique⟩ :=
      degree_sixteen_fourLayer_nondefect_orphans_unique_service
        G hfree hmin hcard c₀ hregChild hcardChild hzO hz'O hzz' hnotD
    refine ⟨y, ⟨Finset.mem_biUnion.mpr
      ⟨u, Finset.mem_univ _, hyu⟩, ?_⟩, ?_⟩
    · intro q hq
      rw [heq] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hq | hq
      · subst q
        exact (G.mem_neighborFinset y z).mpr hzy.symm
      · subst q
        exact (G.mem_neighborFinset y z').mpr hz'y.symm
    · intro y' hy'
      obtain ⟨v, _hv, hy'v⟩ := Finset.mem_biUnion.mp hy'.1
      have hzMem : z ∈ e := by simp [heq]
      have hz'Mem : z' ∈ e := by simp [heq]
      have hzy' : G.Adj z y' :=
        ((G.mem_neighborFinset y' z).mp (hy'.2 hzMem)).symm
      have hz'y' : G.Adj z' y' :=
        ((G.mem_neighborFinset y' z').mp (hy'.2 hz'Mem)).symm
      exact (hunique v y' hy'v hzy' hz'y').2

/-- Regrouping the service-centered cherries by used defect component gives
the weighted quotient cherry sum for a named orphan component. -/
theorem degree_sixteen_fourLayer_used_to_orphan_cherry_mass_eq_service_cherries
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    let B := o.supp.toFinite.toFinset
    (∑ e ∈ C, e.supp.ncard *
        (componentQuotientMatrix G D e o).choose 2) =
      ∑ y ∈ R, ((B ∩ G.neighborFinset y).card).choose 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion
    (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let B := o.supp.toFinite.toFinset
  have hclosed : ∀ (e : D.ConnectedComponent) (z : V), z ∈ e.supp →
      (z ∈ R ↔ componentRepresentative D e ∈ R) := by
    intro e z hze
    have hmk : D.connectedComponentMk z = e :=
      (ConnectedComponent.mem_supp_iff e z).mp hze
    constructor
    · intro hz
      have hsub := degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild) z hz
      rw [hmk] at hsub
      exact hsub (componentRepresentative_mem D e)
    · intro hrep
      have hsub := degree_sixteen_minimumLayer_used_component_subset
        G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
          (by norm_num; exact hcardChild)
          (componentRepresentative D e) hrep
      have hrepComp : D.connectedComponentMk (componentRepresentative D e) = e :=
        (ConnectedComponent.mem_supp_iff e
          (componentRepresentative D e)).mp (componentRepresentative_mem D e)
      rw [hrepComp] at hsub
      exact hsub hze
  have hregD : ∀ v : V, D.degree v = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hweighted := sum_component_sizes_mul_filter_eq_sum_of_component_closed
    D R hclosed (fun e ↦ (componentQuotientMatrix G D e o).choose 2)
  change (∑ e ∈ C, e.supp.ncard *
      (componentQuotientMatrix G D e o).choose 2) = _
  rw [hweighted]
  apply Finset.sum_congr rfl
  intro y hyR
  let e := D.connectedComponentMk y
  have hye : y ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  rw [componentQuotientMatrix_apply_eq G D 2 hregD hcomm e o hye]
  have hfin : componentNeighborFinset G D o y = B ∩ G.neighborFinset y := by
    ext z
    simp [B, D, componentNeighborFinset, ConnectedComponent.mem_supp_iff,
      Finset.mem_inter, and_comm]
  rw [hfin]

/-- Exact numerical cherry ledger for a named orphan component.  Its defect
component is two-regular, so the non-defect endpoint pairs are all unordered
pairs except the `|o|` defect edges. -/
theorem degree_sixteen_fourLayer_used_to_orphan_cherry_mass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : componentRepresentative (secondOrderDefectGraph G) o ∈
      (Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    (∑ e ∈ C, e.supp.ncard *
        (componentQuotientMatrix G D e o).choose 2) =
      o.supp.ncard.choose 2 - o.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion
    (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let B := o.supp.toFinite.toFinset
  have hregD : ∀ z : V, D.degree z = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard
  have hregroup :=
    degree_sixteen_fourLayer_used_to_orphan_cherry_mass_eq_service_cherries
      G hfree hmin hcard c₀ hregChild hcardChild o
  have hservice :=
    degree_sixteen_fourLayer_orphan_component_service_cherries_eq_nondefect_pairs
      G hfree hmin hcard c₀ hregChild hcardChild o ho
  have hnon := card_nonadjacent_pairs_component_twoRegular D hregD o
  have hcardB : B.card = o.supp.ncard := by
    simpa [B] using
      (Set.ncard_eq_toFinset_card o.supp o.supp.toFinite).symm
  change (∑ e ∈ C, e.supp.ncard *
      (componentQuotientMatrix G D e o).choose 2) = _
  calc
    (∑ e ∈ C, e.supp.ncard *
        (componentQuotientMatrix G D e o).choose 2) =
        ∑ y ∈ R, ((B ∩ G.neighborFinset y).card).choose 2 := by
          simpa [D, R, C, B] using hregroup
    _ = ((B.powersetCard 2).filter (fun e : Finset V ↦
        ∀ z ∈ e, ∀ z' ∈ e, z ≠ z' → ¬D.Adj z z')).card := by
          simpa [D, R, B] using hservice
    _ = B.card.choose 2 - B.card := by simpa [D, B] using hnon
    _ = o.supp.ncard.choose 2 - o.supp.ncard := by rw [hcardB]

/-- The complete reduced `S₀,…,S₄` ledger for a named orphan
component.  Used component orders are divided by three, and the numerical
mass, edge, and cherry identities are stratified by their quotient entry
into the orphan component. -/
theorem degree_sixteen_fourLayer_orphan_reduced_quotient_stratification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : componentRepresentative (secondOrderDefectGraph G) o ∈
      (Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    let w := fun e : D.ConnectedComponent ↦ e.supp.ncard / 3
    let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o
    let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then w e else 0
    S 0 + S 1 + S 2 + S 3 + S 4 = 60 ∧
      3 * (S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4) =
        o.supp.ncard * 15 ∧
      3 * (S 2 + 3 * S 3 + 6 * S 4) =
        o.supp.ncard.choose 2 - o.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion
    (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let w := fun e : D.ConnectedComponent ↦ e.supp.ncard / 3
  let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o
  let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then w e else 0
  obtain ⟨hmass, hdiv⟩ := degree_sixteen_fourLayer_used_component_order_package
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild
  have hedge := degree_sixteen_fourLayer_used_to_orphan_edge_mass
    G hfree hmin hcard c₀ hregChild hcardChild o ho
  have hcherry := degree_sixteen_fourLayer_used_to_orphan_cherry_mass
    G hfree hmin hcard c₀ hregChild hcardChild o ho
  have hregD : ∀ z : V, D.degree z = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hsubO : o.supp ⊆
      (((Finset.univ \ minimumLayerImageFinset D c₀) \ R : Finset V) : Set V) := by
    have hrepComp : D.connectedComponentMk (componentRepresentative D o) = o :=
      (ConnectedComponent.mem_supp_iff o
        (componentRepresentative D o)).mp (componentRepresentative_mem D o)
    have hsub := degree_sixteen_fourLayer_orphan_component_subset
      G hfree hmin hcard c₀ hregChild hcardChild
        (componentRepresentative D o) ho
    simpa [hrepComp, D, R] using hsub
  have hq : ∀ e ∈ C, q e ≤ 4 := by
    intro e he
    have hyR : componentRepresentative D e ∈ R :=
      (Finset.mem_filter.mp he).2
    obtain ⟨v, _hv, hyv⟩ := Finset.mem_biUnion.mp hyR
    have hQ := componentQuotientMatrix_apply_eq G D 2 hregD hcomm e o
      (componentRepresentative_mem D e)
    change componentQuotientMatrix G D e o ≤ 4
    rw [hQ]
    have hsubset : componentNeighborFinset G D o (componentRepresentative D e) ⊆
        ((Finset.univ \ minimumLayerImageFinset D c₀) \ R) ∩
          G.neighborFinset (componentRepresentative D e) := by
      intro z hz
      have hzData := Finset.mem_filter.mp hz
      have hzSupp : z ∈ o.supp :=
        (ConnectedComponent.mem_supp_iff o z).mpr hzData.2
      exact Finset.mem_inter.mpr ⟨hsubO hzSupp, hzData.1⟩
    calc
      (componentNeighborFinset G D o (componentRepresentative D e)).card ≤
          (((Finset.univ \ minimumLayerImageFinset D c₀) \ R) ∩
            G.neighborFinset (componentRepresentative D e)).card :=
        Finset.card_le_card hsubset
      _ = 4 := degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
        G hfree hmin hcard c₀ hregChild hcardChild v hyv
  simpa [D, R, C, w, q, S] using
    weighted_quotient_zero_four_stratification_div_three
      C (fun e ↦ e.supp.ncard) q hdiv hq
        (o.supp.ncard * 15) (o.supp.ncard.choose 2 - o.supp.ncard)
        hmass hedge hcherry

/-- Graph instantiation of the symmetric-orphan weighted count
decomposition. -/
theorem degree_sixteen_fourLayer_twentyfour_twentyfour_count_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁ ≠ o₂) (ho₁ : o₁.supp.ncard = 24)
    (ho₂ : o₂.supp.ncard = 24)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁, o₂}) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    let r := fun e : D.ConnectedComponent ↦ e.supp.ncard
    let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o₁
    let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then r e / 3 else 0
    let n₁ := (C.filter fun e ↦ q e = 1).card
    let n₃ := (C.filter fun e ↦ q e = 3).card
    let n₄₂ := (C.filter fun e ↦ q e = 2 ∧ r e = 12).card
    let n₈₂ := (C.filter fun e ↦ q e = 2 ∧ r e = 24).card
    S 1 = 8 * n₁ ∧ S 3 = 8 * n₃ ∧ S 2 = 4 * n₄₂ + 8 * n₈₂ := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let r := fun e : D.ConnectedComponent ↦ e.supp.ncard
  let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o₁
  apply twentyfour_twentyfour_weighted_count_decomposition C r q
  · intro e he hq
    exact (degree_sixteen_fourLayer_twentyfour_twentyfour_used_row_orders
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        o₁ o₂ hne ho₁ ho₂ hpair e (Finset.mem_filter.mp he).2).1 hq
  · intro e he hq
    exact (degree_sixteen_fourLayer_twentyfour_twentyfour_used_row_orders
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        o₁ o₂ hne ho₁ ho₂ hpair e (Finset.mem_filter.mp he).2).2.1 hq
  · intro e he hq
    exact (degree_sixteen_fourLayer_twentyfour_twentyfour_used_row_orders
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        o₁ o₂ hne ho₁ ho₂ hpair e (Finset.mem_filter.mp he).2).2.2 hq

/-- At most one used order-twelve component can double-cover a fixed
order-twenty-four orphan component. -/
theorem degree_sixteen_fourLayer_twentyfour_order_twelve_double_cover_count_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ o : (secondOrderDefectGraph G).ConnectedComponent)
    (ho : o.supp.ncard = 24) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    (C.filter fun e ↦ componentQuotientMatrix G D e o = 2 ∧
      e.supp.ncard = 12).card ≤ 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  apply Finset.card_le_one.mpr
  intro c₁ hc₁ c₂ hc₂
  have hc₁Data := (Finset.mem_filter.mp hc₁).2
  have hc₂Data := (Finset.mem_filter.mp hc₂).2
  have hone₁ : componentQuotientMatrix G D o c₁ = 1 := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₁ o
    dsimp only [D] at hbal ⊢
    rw [hc₁Data.2, hc₁Data.1, ho] at hbal
    omega
  have hone₂ : componentQuotientMatrix G D o c₂ = 1 := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₂ o
    dsimp only [D] at hbal ⊢
    rw [hc₂Data.2, hc₂Data.1, ho] at hbal
    omega
  apply secondOrder_multipleCover_target_source_unique_of_orders
    G hfree (d := 16) (m := 2) (by norm_num) (by norm_num) hmin hcard
      (by norm_num) c₁ c₂ o
  · omega
  · omega
  · exact hone₁
  · exact hone₂

/-- Across all five minimum-component owner bins, there are at most five
used defect components of order twenty-four.  Each 36-vertex bin contains at
most one such component. -/
theorem degree_sixteen_fourLayer_used_order_twentyfour_count_le_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    (C.filter fun e ↦ e.supp.ncard = 24).card ≤ 5 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Erow := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion Erow
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let X := fun a : minimumLayerComponent D c₀ ↦
    Finset.univ.filter (fun x : minimumLayerVertex D c₀ ↦ x.1 = a)
  let B := fun a : minimumLayerComponent D c₀ ↦ (X a).biUnion Erow
  let E := fun a : minimumLayerComponent D c₀ ↦
    Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ B a)
  let T := C.filter fun e ↦ e.supp.ncard = 24
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have howners : Fintype.card (minimumLayerComponent D c₀) = 5 := by
    have hv := card_minimumLayerVertex D c₀
    have hsub : Fintype.card (minimumLayerComponent D c₀) =
        (Finset.univ.filter
          (fun c : D.ConnectedComponent ↦ c.supp.ncard = c₀.supp.ncard)).card := by
      exact Fintype.card_subtype
        (fun c : D.ConnectedComponent ↦ c.supp.ncard = c₀.supp.ncard)
    rw [hc₀three] at hsub
    rw [hcardChild, hc₀three, ← hsub] at hv
    omega
  have hbin : ∀ a : minimumLayerComponent D c₀,
      ((E a).filter fun e ↦ e.supp.ncard = 24).card ≤ 1 := by
    intro a
    apply Finset.card_le_one.mpr
    intro e₁ he₁ e₂ he₂
    have he₁Data := Finset.mem_filter.mp he₁
    have he₂Data := Finset.mem_filter.mp he₂
    by_contra hne
    have hsum := (degree_sixteen_fourLayer_owner_bin_order_package
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild a).1
    change (∑ e ∈ E a, e.supp.ncard) = 36 at hsum
    have he₂Erase : e₂ ∈ (E a).erase e₁ :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, he₂Data.1⟩
    have he₂Le : e₂.supp.ncard ≤
        ∑ e ∈ (E a).erase e₁, e.supp.ncard := by
      exact Finset.single_le_sum
        (fun e he ↦ Nat.zero_le e.supp.ncard) he₂Erase
    have he₁Mem : e₁ ∈ E a := he₁Data.1
    have hfortyeight : 48 ≤ ∑ e ∈ E a, e.supp.ncard := by
      calc
        48 = e₁.supp.ncard + e₂.supp.ncard := by
          rw [he₁Data.2, he₂Data.2]
        _ ≤ e₁.supp.ncard + ∑ e ∈ (E a).erase e₁, e.supp.ncard :=
          Nat.add_le_add_left he₂Le _
        _ = ∑ e ∈ E a, e.supp.ncard := by
          rw [Nat.add_comm, Finset.sum_erase_add _ _ he₁Mem]
    omega
  have hcover : T ⊆ Finset.univ.biUnion
      (fun a : minimumLayerComponent D c₀ ↦
        (E a).filter fun e ↦ e.supp.ncard = 24) := by
    intro e he
    have heData := Finset.mem_filter.mp he
    have heR : componentRepresentative D e ∈ R :=
      (Finset.mem_filter.mp heData.1).2
    obtain ⟨x, _hx, hex⟩ := Finset.mem_biUnion.mp heR
    let a : minimumLayerComponent D c₀ := x.1
    have hrepB : componentRepresentative D e ∈ B a := by
      apply Finset.mem_biUnion.mpr
      refine ⟨x, ?_, hex⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, heData.2⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrepB⟩
  calc
    T.card ≤ (Finset.univ.biUnion
        (fun a : minimumLayerComponent D c₀ ↦
          (E a).filter fun e ↦ e.supp.ncard = 24)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ a : minimumLayerComponent D c₀,
        ((E a).filter fun e ↦ e.supp.ncard = 24).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a : minimumLayerComponent D c₀, 1 := by
      exact Finset.sum_le_sum fun a _ ↦ hbin a
    _ = 5 := by simp [howners]

/-- The symmetric `(24,24)` named orphan pair is impossible. -/
theorem degree_sixteen_fourLayer_false_of_twentyfour_twentyfour_orphan_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁ o₂ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁ ≠ o₂) (ho₁ : o₁.supp.ncard = 24)
    (ho₂ : o₂.supp.ncard = 24)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁, o₂}) : False := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \ R
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let r := fun e : D.ConnectedComponent ↦ e.supp.ncard
  let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o₁
  let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then r e / 3 else 0
  let n₁ := (C.filter fun e ↦ q e = 1).card
  let n₃ := (C.filter fun e ↦ q e = 3).card
  let n₄₂ := (C.filter fun e ↦ q e = 2 ∧ r e = 12).card
  let n₈₂ := (C.filter fun e ↦ q e = 2 ∧ r e = 24).card
  have ho₁O : componentRepresentative D o₁ ∈ O := by
    have hoMem : o₁ ∈ ({o₁, o₂} : Finset D.ConnectedComponent) := by simp
    rw [← hpair] at hoMem
    exact (Finset.mem_filter.mp hoMem).2
  obtain ⟨hmass, hedgesRaw, hcherriesRaw⟩ :=
    degree_sixteen_fourLayer_orphan_reduced_quotient_stratification
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild o₁ ho₁O
  have hmass' : S 0 + S 1 + S 2 + S 3 + S 4 = 60 := by
    simpa [S, q, r, C, R, D] using hmass
  have hedges : S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4 = 120 := by
    have hedgesRaw' : 3 * (S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4) =
        o₁.supp.ncard * 15 := by
      simpa [S, q, r, C, R, D] using hedgesRaw
    rw [ho₁] at hedgesRaw'
    omega
  have hcherries : S 2 + 3 * S 3 + 6 * S 4 = 84 := by
    have hcherriesRaw' : 3 * (S 2 + 3 * S 3 + 6 * S 4) =
        o₁.supp.ncard.choose 2 - o₁.supp.ncard := by
      simpa [S, q, r, C, R, D] using hcherriesRaw
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    calc
      3 * (S 2 + 3 * S 3 + 6 * S 4) =
          o₁.supp.ncard.choose 2 - o₁.supp.ncard := hcherriesRaw'
      _ = 3 * 84 := by rw [ho₁]; norm_num [Nat.choose]
  obtain ⟨hS₁, hS₃, hS₂⟩ :=
    degree_sixteen_fourLayer_twentyfour_twentyfour_count_decomposition
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        o₁ o₂ hne ho₁ ho₂ hpair
  have hn₄₂ : n₄₂ ≤ 1 := by
    exact degree_sixteen_fourLayer_twentyfour_order_twelve_double_cover_count_le_one
      G hfree hmin hcard c₀ o₁ ho₁
  have hall24 : (C.filter fun e ↦ r e = 24).card ≤ 5 := by
    exact degree_sixteen_fourLayer_used_order_twentyfour_count_le_five
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
  let F₁ := C.filter fun e ↦ q e = 1
  let F₃ := C.filter fun e ↦ q e = 3
  let F₈₂ := C.filter fun e ↦ q e = 2 ∧ r e = 24
  have hd₁₃ : Disjoint F₁ F₃ := by
    apply Finset.disjoint_left.mpr
    intro e he₁ he₃
    have hq₁ := (Finset.mem_filter.mp he₁).2
    have hq₃ := (Finset.mem_filter.mp he₃).2
    omega
  have hdU : Disjoint (F₁ ∪ F₃) F₈₂ := by
    apply Finset.disjoint_left.mpr
    intro e heU he₂
    have hq₂ := (Finset.mem_filter.mp he₂).2.1
    rcases Finset.mem_union.mp heU with he₁ | he₃
    · have hq₁ := (Finset.mem_filter.mp he₁).2
      omega
    · have hq₃ := (Finset.mem_filter.mp he₃).2
      omega
  have hselectedSub : (F₁ ∪ F₃) ∪ F₈₂ ⊆
      C.filter (fun e ↦ r e = 24) := by
    intro e he
    rcases Finset.mem_union.mp he with he13 | he82
    · rcases Finset.mem_union.mp he13 with he1 | he3
      · have heData := Finset.mem_filter.mp he1
        refine Finset.mem_filter.mpr ⟨heData.1, ?_⟩
        exact (degree_sixteen_fourLayer_twentyfour_twentyfour_used_row_orders
          G hfree hmin hcard c₀ hc₀min hregChild hcardChild
            o₁ o₂ hne ho₁ ho₂ hpair e
              (Finset.mem_filter.mp heData.1).2).1 heData.2
      · have heData := Finset.mem_filter.mp he3
        refine Finset.mem_filter.mpr ⟨heData.1, ?_⟩
        exact (degree_sixteen_fourLayer_twentyfour_twentyfour_used_row_orders
          G hfree hmin hcard c₀ hc₀min hregChild hcardChild
            o₁ o₂ hne ho₁ ho₂ hpair e
              (Finset.mem_filter.mp heData.1).2).2.2 heData.2
    · have heData := Finset.mem_filter.mp he82
      exact Finset.mem_filter.mpr ⟨heData.1, heData.2.2⟩
  have hcapacity : n₁ + n₃ + n₈₂ ≤ 5 := by
    have hcardSelected : ((F₁ ∪ F₃) ∪ F₈₂).card =
        n₁ + n₃ + n₈₂ := by
      rw [Finset.card_union_of_disjoint hdU,
        Finset.card_union_of_disjoint hd₁₃]
    have hle := Finset.card_le_card hselectedSub
    change ((F₁ ∪ F₃) ∪ F₈₂).card ≤
      (C.filter fun e ↦ r e = 24).card at hle
    rw [hcardSelected] at hle
    omega
  have hsignature := twentyfour_twentyfour_weighted_row_signature
    (S 0) (S 1) (S 2) (S 3) (S 4) n₁ n₃ n₄₂ n₈₂
      hmass' hedges hcherries hS₁ hS₃ hS₂ hn₄₂
  exact false_of_twentyfour_twentyfour_weighted_signature_capacity
    (S 1) (S 2) (S 3) n₁ n₃ n₄₂ n₈₂
      hS₁ hS₃ hS₂ hn₄₂ hcapacity hsignature

/-- The order-twelve member of a `(12,36)` orphan pair has the unique
remaining reduced quotient signature `(9,48,0,0,3)`. -/
theorem degree_sixteen_fourLayer_twelve_thirtysix_reduced_signature
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁₂ o₃₆ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁₂ ≠ o₃₆) (ho₁₂ : o₁₂.supp.ncard = 12)
    (ho₃₆ : o₃₆.supp.ncard = 36)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁₂, o₃₆}) :
    let D := secondOrderDefectGraph G
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
      componentRepresentative D e ∈ R)
    let w := fun e : D.ConnectedComponent ↦ e.supp.ncard / 3
    let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o₁₂
    let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then w e else 0
    S 0 = 9 ∧ S 1 = 48 ∧ S 2 = 0 ∧ S 3 = 0 ∧ S 4 = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let w := fun e : D.ConnectedComponent ↦ e.supp.ncard / 3
  let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o₁₂
  let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then w e else 0
  have ho : componentRepresentative D o₁₂ ∈
      (Finset.univ \ minimumLayerImageFinset D c₀) \ R := by
    have hm : o₁₂ ∈ ({o₁₂, o₃₆} : Finset D.ConnectedComponent) := by simp
    rw [← hpair] at hm
    exact (Finset.mem_filter.mp hm).2
  have hs := degree_sixteen_fourLayer_orphan_reduced_quotient_stratification
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild o₁₂ ho
  change S 0 + S 1 + S 2 + S 3 + S 4 = 60 ∧
      3 * (S 1 + 2 * S 2 + 3 * S 3 + 4 * S 4) =
        o₁₂.supp.ncard * 15 ∧
      3 * (S 2 + 3 * S 3 + 6 * S 4) =
        o₁₂.supp.ncard.choose 2 - o₁₂.supp.ncard at hs
  obtain ⟨hmass, hedge, hcherry⟩ := hs
  rw [ho₁₂] at hedge hcherry
  norm_num [Nat.choose] at hedge hcherry
  have hno : ∀ e ∈ C, q e ≠ 2 ∧ q e ≠ 3 := by
    intro e he
    exact degree_sixteen_fourLayer_twelve_thirtysix_no_two_or_three
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        o₁₂ o₃₆ hne ho₁₂ ho₃₆ hpair e
        (by exact (Finset.mem_filter.mp he).2)
  have htwo : S 2 = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp [S, q, (hno e he).1]
  have hthree : S 3 = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp [S, q, (hno e he).2]
  have hfour : S 4 ≠ 1 := by
    apply finset_sum_ne_one_of_eq_zero_or_two_le C
    intro e he
    by_cases hq : q e = 4
    · right
      have hlower := degree_sixteen_fourLayer_used_component_card_lower
        G hfree hmin hcard c₀ hc₀min hregChild hcardChild e
          (Finset.mem_filter.mp he).2
      have hdiv := (degree_sixteen_fourLayer_used_component_order_package
        G hfree hmin hcard c₀ hc₀min hregChild hcardChild).2 e he
      rcases hdiv with ⟨k, hk⟩
      simp [S, w, q, hq, hk]
      omega
    · left
      simp [S, q, hq]
  exact twelve_thirtysix_weighted_row_signature_of_no_two
    (S 0) (S 1) (S 2) (S 3) (S 4)
      hmass (by omega) (by omega) hthree hfour htwo

/-- The `(12,36)` two-orphan branch is impossible.  Its forced signature
has `S₄ = 3`, whereas periodicity makes every quotient-four row have used
order six or twelve, hence even reduced weight two or four. -/
theorem false_of_degree_sixteen_fourLayer_twelve_thirtysix_orphans
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (o₁₂ o₃₆ : (secondOrderDefectGraph G).ConnectedComponent)
    (hne : o₁₂ ≠ o₃₆) (ho₁₂ : o₁₂.supp.ncard = 12)
    (ho₃₆ : o₃₆.supp.ncard = 36)
    (hpair :
      Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \
            minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) = {o₁₂, o₃₆}) : False := by
  classical
  let D := secondOrderDefectGraph G
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun e : D.ConnectedComponent ↦
    componentRepresentative D e ∈ R)
  let w := fun e : D.ConnectedComponent ↦ e.supp.ncard / 3
  let q := fun e : D.ConnectedComponent ↦ componentQuotientMatrix G D e o₁₂
  let S := fun a : ℕ ↦ ∑ e ∈ C, if q e = a then w e else 0
  have hsig := degree_sixteen_fourLayer_twelve_thirtysix_reduced_signature
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild
      o₁₂ o₃₆ hne ho₁₂ ho₃₆ hpair
  change S 0 = 9 ∧ S 1 = 48 ∧ S 2 = 0 ∧ S 3 = 0 ∧ S 4 = 3 at hsig
  have heven : Even (S 4) := by
    apply Finset.even_sum _
    intro e he
    by_cases hq : q e = 4
    · have hqTwo : 2 ≤ componentQuotientMatrix G
          (secondOrderDefectGraph G) e o₁₂ := by
        simpa [q, D] using (show 2 ≤ q e by omega)
      have hdvd := degree_sixteen_component_order_dvd_of_two_le_quotient
        G hfree hmin hcard e o₁₂ hqTwo
      rw [ho₁₂] at hdvd
      have hupper : e.supp.ncard ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
      have hlower := degree_sixteen_fourLayer_used_component_card_lower
        G hfree hmin hcard c₀ hc₀min hregChild hcardChild e
          (Finset.mem_filter.mp he).2
      have hthree := (degree_sixteen_fourLayer_used_component_order_package
        G hfree hmin hcard c₀ hc₀min hregChild hcardChild).2 e he
      interval_cases horder : e.supp.ncard
      all_goals (try norm_num [horder] at hdvd)
      all_goals norm_num [S, w, q, hq, horder]
    · simp [S, q, hq]
  rw [hsig.2.2.2.2] at heven
  rcases heven with ⟨k, hk⟩
  omega

/-- The four-layer branch cannot have exactly two orphan defect
components. -/
theorem false_of_degree_sixteen_fourLayer_two_orphan_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 2) : False := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent ↦
    componentRepresentative D c ∈ O)
  obtain ⟨c, d, hcd, hC, horders⟩ :=
    degree_sixteen_fourLayer_two_orphan_remaining_classification
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild hcount
  change C = {c, d} at hC
  rcases horders with h12_36 | h36_12 | h24_24
  · exact false_of_degree_sixteen_fourLayer_twelve_thirtysix_orphans
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        c d hcd h12_36.1 h12_36.2 hC
  · have hCswap : C = {d, c} := by simpa [Finset.pair_comm] using hC
    exact false_of_degree_sixteen_fourLayer_twelve_thirtysix_orphans
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        d c hcd.symm h36_12.2 h36_12.1 hCswap
  · exact degree_sixteen_fourLayer_false_of_twentyfour_twentyfour_orphan_pair
      G hfree hmin hcard c₀ hc₀min hregChild hcardChild
        c d hcd h24_24.1 h24_24.2 hC

/-- The four-layer branch cannot have exactly one orphan defect component. -/
theorem false_of_degree_sixteen_fourLayer_one_orphan_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (hcount :
      (Finset.univ.filter (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentRepresentative (secondOrderDefectGraph G) c ∈
          (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
            Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀))).card = 1) : False := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let C := Finset.univ.filter (fun c : D.ConnectedComponent ↦
    componentRepresentative D c ∈ O)
  change C.card = 1 at hcount
  obtain ⟨o, hC⟩ := Finset.card_eq_one.mp hcount
  have hsum := degree_sixteen_fourLayer_orphan_component_order_sum_eq_fortyEight
    G hfree hmin hcard c₀ hregChild hcardChild
  change (∑ c ∈ C, c.supp.ncard) = 48 at hsum
  rw [hC] at hsum
  have ho : o.supp.ncard = 48 := by simpa using hsum
  exact degree_sixteen_fourLayer_false_of_one_order_fortyeight_orphan
    G hfree hmin hcard c₀ hc₀min hregChild hcardChild o ho hC

/-- Every edge incident to an orphan lies in a triangle; equivalently its
open neighborhood is a perfect matching.  This is the child-side pairing
structure left after the all-antipodal defect closure. -/
theorem degree_sixteen_fourLayer_orphan_localNeighborhood_oneRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    (triangleFreeNeighbors G z).card = 0 ∧
      ∀ y : {q : V // q ∈ G.neighborSet z},
        (G.induce (G.neighborSet z)).degree y = 1 := by
  classical
  have hzero : (triangleFreeNeighbors G z).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hqTF
    have hqData := (mem_triangleFreeNeighbors G z q).mp hqTF
    have hzqD : (secondOrderDefectGraph G).Adj z q := Or.inr hqTF
    have hqO := degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild z hz
        (((secondOrderDefectGraph G).mem_neighborFinset z q).mpr hzqD)
    exact degree_sixteen_fourLayer_orphan_matching_not_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hqO hqData.1 hzqD
  refine ⟨hzero, ?_⟩
  intro y
  have hle : (G.induce (G.neighborSet z)).degree y ≤ 1 := by
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree z y.1 (G.ne_of_adj y.2)
  have hne : (G.induce (G.neighborSet z)).degree y ≠ 0 := by
    intro hdegzero
    have hcommonzero :
        (G.neighborFinset z ∩ G.neighborFinset y.1).card = 0 := by
      rwa [degree_induce_neighborSet_eq_card_common] at hdegzero
    have hyTF : y.1 ∈ triangleFreeNeighbors G z :=
      (mem_triangleFreeNeighbors G z y.1).mpr ⟨y.2, hcommonzero⟩
    rw [Finset.card_eq_zero] at hzero
    exact Finset.notMem_empty y.1 (hzero ▸ hyTF)
  omega

/-- A nonshared service of a matched orphan has its local-triangle partner
at a service in a distinct child-nonadjacent row.  These seven pairings are
the near-perfect matching of the child complement selected by each orphan. -/
theorem degree_sixteen_fourLayer_orphan_nonshared_service_partner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z')
    (u : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyE : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ u)
    (hzy : G.Adj z y) (hnotShared : ¬G.Adj z' y) :
    ∃ v : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∃ y' : V,
      y' ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ v ∧
      v ≠ u ∧
      ¬(minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj v u ∧
      G.Adj z y' ∧ G.Adj y y' ∧ ¬G.Adj z' y' ∧
      ∀ w : V, G.Adj z w → G.Adj y w → w = y' := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  let yy : {q : V // q ∈ G.neighborSet z} := ⟨y, hzy⟩
  have hlocal :=
    (degree_sixteen_fourLayer_orphan_localNeighborhood_oneRegular
      G hfree hmin hcard c₀ hregChild hcardChild z hz).2 yy
  have hcardLocal :
      ((G.induce (G.neighborSet z)).neighborFinset yy).card = 1 := by
    rw [(G.induce (G.neighborSet z)).card_neighborFinset_eq_degree, hlocal]
  obtain ⟨ww, hww⟩ := Finset.card_eq_one.mp hcardLocal
  have hwwMem : ww ∈ (G.induce (G.neighborSet z)).neighborFinset yy := by
    simp [hww]
  have hyw : G.Adj y ww.1 :=
    ((G.induce (G.neighborSet z)).mem_neighborFinset yy ww).mp hwwMem
  have hzw : G.Adj z ww.1 := ww.2
  have hwne : ww.1 ≠ z' := by
    intro hwz'
    apply hnotShared
    rw [← hwz']
    exact hyw.symm
  have hzOutside : z ∉ U :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzUnused : z ∉ R := (Finset.mem_sdiff.mp hz).2
  have hwOutside : ww.1 ∉ U := by
    intro hwU
    obtain ⟨a, _ha, haw⟩ := Finset.mem_image.mp hwU
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨?_, hzOutside⟩⟩
    change a.2.1 = ww.1 at haw
    exact (G.mem_neighborFinset a.2.1 z).mpr (by simpa [haw] using hzw.symm)
  have hwR : ww.1 ∈ R := by
    by_contra hwNotR
    have hwO : ww.1 ∈ O := Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwOutside⟩, hwNotR⟩
    have hone := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z hz
    have hz'Mem : z' ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hz', (G.mem_neighborFinset z z').mpr hzz'⟩
    have hwMem : ww.1 ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hwO, (G.mem_neighborFinset z ww.1).mpr hzw⟩
    have hle : (O ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
    exact hwne (Finset.card_le_one.mp hle ww.1 hwMem z' hz'Mem)
  obtain ⟨v, _hv, hwE⟩ := Finset.mem_biUnion.mp hwR
  have hvu : v ≠ u := by
    intro hvu
    subst v
    have hone := minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused u
    have hyMem : y ∈ E u ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hyE, (G.mem_neighborFinset z y).mpr hzy⟩
    have hwMem : ww.1 ∈ E u ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hwE, (G.mem_neighborFinset z ww.1).mpr hzw⟩
    have hle : (E u ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
    have hywEq := Finset.card_le_one.mp hle y hyMem ww.1 hwMem
    exact G.loopless.irrefl y (hywEq ▸ hyw)
  have hnotH : ¬(minimumLayerGraph G D c₀).Adj v u := by
    intro hvuH
    have hblock := degree_sixteen_fourLayer_used_exterior_row_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild v u hyE
    rw [if_pos hvuH] at hblock
    have hwMem : ww.1 ∈ E v ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨hwE, (G.mem_neighborFinset y ww.1).mpr hyw⟩
    rw [Finset.card_eq_zero.mp hblock] at hwMem
    exact Finset.notMem_empty ww.1 hwMem
  have hnotShared' : ¬G.Adj z' ww.1 := by
    intro hz'w
    have hzy'ne : z ≠ ww.1 := G.ne_of_adj hzw
    have hcommon := common_le_one_of_not_containsC4 hfree z ww.1 hzy'ne
    have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset ww.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z y).mpr hzy,
          (G.mem_neighborFinset ww.1 y).mpr hyw.symm⟩
    have hz'Mem : z' ∈ G.neighborFinset z ∩ G.neighborFinset ww.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z z').mpr hzz',
          (G.mem_neighborFinset ww.1 z').mpr hz'w.symm⟩
    have hyz' : y = z' :=
      Finset.card_le_one.mp hcommon y hyMem z' hz'Mem
    have hyR : y ∈ R := Finset.mem_biUnion.mpr
      ⟨u, Finset.mem_univ _, hyE⟩
    exact (Finset.mem_sdiff.mp hz').2 (hyz' ▸ hyR)
  refine ⟨v, ww.1, hwE, hvu, hnotH, hzw, hyw, hnotShared', ?_⟩
  intro w hzw' hyw'
  have hzyne : z ≠ y := G.ne_of_adj hzy
  have hcommon := common_le_one_of_not_containsC4 hfree z y hzyne
  have hwMem : w ∈ G.neighborFinset z ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z w).mpr hzw',
        (G.mem_neighborFinset y w).mpr hyw'⟩
  have hpartnerMem : ww.1 ∈ G.neighborFinset z ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z ww.1).mpr hzw,
        (G.mem_neighborFinset y ww.1).mpr hyw⟩
  exact Finset.card_le_one.mp hcommon w hwMem ww.1 hpartnerMem

end

end Erdos85
