import Proofs.Erdos85OrderSixtyFourOutsideCnfSemantics
import Proofs.Erdos85SizeTwoEigenlineEightEightLowExteriorModel
import Proofs.Erdos85SizeTwoUnorderedPairServiceCount
import Proofs.Erdos85EightEightLowOwnerCnf
import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection

/-!
# Transporting exterior-owner clause semantics to finite coordinates

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The checked low-`8+8` owner certificate is stated on a fixed finite owner
type, while the graph-facing routing laws naturally live on the subtype of
vertices exterior to the size-two component.  This file supplies the
equivalence transport layer.  It is deliberately independent of a DIMACS
variable numbering, so the same bridge can be consumed by a regenerated or
minimized certificate.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The generator's endpoint table is in range on all forty-eight genuine
owner indices. -/
theorem eightEightOwnerAt_lt_sixteen (e : Fin 48) :
    (eightEightOwnerAt e).1 < 16 ∧ (eightEightOwnerAt e).2 < 16 := by
  revert e
  decide

/-- First endpoint of a generated owner as a vertex of the fixed internal
`Fin 16` model. -/
def eightEightOwnerFirst (e : Fin 48) : Fin 16 :=
  ⟨(eightEightOwnerAt e).1, (eightEightOwnerAt_lt_sixteen e).1⟩

/-- Second endpoint of a generated owner as a vertex of the fixed internal
`Fin 16` model. -/
def eightEightOwnerSecond (e : Fin 48) : Fin 16 :=
  ⟨(eightEightOwnerAt e).2, (eightEightOwnerAt_lt_sixteen e).2⟩

/-- The unordered internal pair represented by a generated owner index. -/
def eightEightOwnerSym2 (e : Fin 48) : Sym2 (Fin 16) :=
  s(eightEightOwnerFirst e, eightEightOwnerSecond e)

/-- The generated list has no duplicate unordered owner pairs. -/
theorem eightEightOwnerSym2_injective :
    Function.Injective eightEightOwnerSym2 := by
  decide

/-- Canonical equivalence between the generator's `Fin 48` owner indices
and the range of its typed unordered-pair table. -/
noncomputable def eightEightOwnerRangeEquiv :
    Fin 48 ≃ Set.range eightEightOwnerSym2 :=
  Equiv.ofInjective eightEightOwnerSym2 eightEightOwnerSym2_injective

@[simp] theorem eightEightOwnerRangeEquiv_apply_val (e : Fin 48) :
    (eightEightOwnerRangeEquiv e).1 = eightEightOwnerSym2 e := rfl

/-- The fixed exterior-pair graph represented by the low-`8+8` generator. -/
def eightEightLowExteriorPairGraph : SimpleGraph (Fin 16) where
  Adj a b := eightEightLowOwnerPair a b = true ∨
    eightEightLowOwnerPair b a = true
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by intro a h; simp [eightEightLowOwnerPair] at h⟩

instance : DecidableRel eightEightLowExteriorPairGraph.Adj := by
  intro a b
  change Decidable
    (eightEightLowOwnerPair a b = true ∨ eightEightLowOwnerPair b a = true)
  infer_instance

/-- First-shore embedding of cyclic `ZMod 8` coordinates into the fixed
sixteen-vertex model. -/
def zmodEightLeftFin16 (i : ZMod 8) : Fin 16 :=
  Fin.castAdd 8 ((ZMod.finEquiv 8).symm i)

/-- Second-shore embedding of cyclic `ZMod 8` coordinates into the fixed
sixteen-vertex model. -/
def zmodEightRightFin16 (i : ZMod 8) : Fin 16 :=
  Fin.natAdd 8 ((ZMod.finEquiv 8).symm i)

theorem eightEightLowExteriorPairGraph_left (i j : ZMod 8) :
    eightEightLowExteriorPairGraph.Adj
      (zmodEightLeftFin16 i) (zmodEightLeftFin16 j) ↔
        j - i = 3 ∨ j - i = 5 := by
  revert i j
  decide

theorem eightEightLowExteriorPairGraph_right (i j : ZMod 8) :
    eightEightLowExteriorPairGraph.Adj
      (zmodEightRightFin16 i) (zmodEightRightFin16 j) ↔
        j - i = 3 ∨ j - i = 5 := by
  revert i j
  decide

theorem eightEightLowExteriorPairGraph_cross (i j : ZMod 8) :
    eightEightLowExteriorPairGraph.Adj
      (zmodEightLeftFin16 i) (zmodEightRightFin16 j) ↔
        ((ZMod.finEquiv 8).symm i).val % 2 ≠
          ((ZMod.finEquiv 8).symm j).val % 2 := by
  revert i j
  decide

theorem eightEightOwnerSym2_mem_edgeFinset (e : Fin 48) :
    eightEightOwnerSym2 e ∈ eightEightLowExteriorPairGraph.edgeFinset := by
  revert e
  decide

/-- A generated owner index as an edge of the fixed exterior-pair graph. -/
def eightEightOwnerEdge (e : Fin 48) :
    eightEightLowExteriorPairGraph.edgeFinset :=
  ⟨eightEightOwnerSym2 e, eightEightOwnerSym2_mem_edgeFinset e⟩

theorem eightEightOwnerEdge_bijective :
    Function.Bijective eightEightOwnerEdge := by
  decide

/-- Canonical enumeration of all forty-eight edges of the fixed low-`8+8`
exterior-pair graph, in exactly the order used by the CNF generator. -/
def eightEightOwnerEdgeEquiv :
    Fin 48 ≃ eightEightLowExteriorPairGraph.edgeFinset :=
  Equiv.ofBijective eightEightOwnerEdge eightEightOwnerEdge_bijective

@[simp] theorem eightEightOwnerEdgeEquiv_apply_val (e : Fin 48) :
    (eightEightOwnerEdgeEquiv e).1 = eightEightOwnerSym2 e := rfl

/-- The finset subtype and set subtype of edges are canonically equivalent. -/
def edgeFinsetEquivEdgeSet
    {W : Type*} [Fintype W] [DecidableEq W]
    (R : SimpleGraph W) [DecidableRel R.Adj] :
    R.edgeFinset ≃ R.edgeSet where
  toFun e := ⟨e.1, SimpleGraph.mem_edgeFinset.mp e.2⟩
  invFun e := ⟨e.1, SimpleGraph.mem_edgeFinset.mpr e.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Package a pointwise coordinate description of the actual exterior-pair
relation as the graph isomorphism consumed by the owner-index transport. -/
noncomputable def lowEightExteriorPairModelIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (coord : c.supp ≃ Fin 16)
    (hmodel : ∀ x y : c.supp,
      (exteriorPairGraph G c).Adj x y ↔
        eightEightLowExteriorPairGraph.Adj (coord x) (coord y)) :
    exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph where
  toEquiv := coord
  map_rel_iff' := by
    intro x y
    exact (hmodel x y).symm

/-- Assemble the pointwise fixed low-`8+8` exterior-pair model from its two
cyclic shores.  The statement isolates the purely coordinate bookkeeping
from the graph-specific theorems which provide the three displayed
relations. -/
theorem lowEightExteriorPair_pointwise_model_of_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a b : (G.induce c.supp).ConnectedComponent)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp)
    (hvrange : Set.range v = b.supp)
    (hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp)
    (coord : c.supp ≃ Fin 16)
    (hcoordu : ∀ i, coord (u i) = zmodEightLeftFin16 i)
    (hcoordv : ∀ j, coord (v j) = zmodEightRightFin16 j)
    (hleft : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 5)
    (hright : ∀ i j,
      (exteriorPairGraph G c).Adj (v i) (v j) ↔
        j - i = 3 ∨ j - i = 5)
    (hcross : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        ((ZMod.finEquiv 8).symm i).val % 2 ≠
          ((ZMod.finEquiv 8).symm j).val % 2) :
    ∀ x y : c.supp,
      (exteriorPairGraph G c).Adj x y ↔
        eightEightLowExteriorPairGraph.Adj (coord x) (coord y) := by
  intro x y
  rcases hcover x with hxa | hxb <;>
    rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [hcoordu, hcoordu, hleft,
      eightEightLowExteriorPairGraph_left]
  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    rw [hcoordu, hcoordv, hcross,
      eightEightLowExteriorPairGraph_cross]
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨j, rfl⟩ := hxb
    obtain ⟨i, rfl⟩ := hya
    rw [(exteriorPairGraph G c).adj_comm,
      hcoordv, hcoordu, eightEightLowExteriorPairGraph.adj_comm,
      hcross, eightEightLowExteriorPairGraph_cross]
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [hcoordv, hcoordv, hright,
      eightEightLowExteriorPairGraph_right]

/-- Once the actual exterior-pair graph is identified with the fixed low
`8+8` model, the canonical outside-pair bijection and the generator's exact
edge enumeration compose to label every exterior vertex by `Fin 48`. -/
noncomputable def outsideLowEightOwnerIndexEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (modelIso : exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph) :
    {x : V // x ∉ c.supp} ≃ Fin 48 :=
  (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
      hcard hinc hqcard hRedges).trans
    ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c)).trans
      (modelIso.mapEdgeSet.trans
        ((edgeFinsetEquivEdgeSet eightEightLowExteriorPairGraph).symm.trans
          eightEightOwnerEdgeEquiv.symm)))

/-- Membership in the generated pair is exactly the generator's Boolean
incidence predicate. -/
theorem mem_eightEightOwnerSym2_iff (e : Fin 48) (v : Fin 16) :
    v ∈ (eightEightOwnerSym2 e).toFinset ↔
      eightEightOwnerContains e v := by
  revert e v
  decide

/-- Clause semantics are invariant under relabeling the exterior vertices.
The transported graph is the comap along the inverse equivalence, and both
incidence and target tables are relabeled by the same inverse. -/
theorem OutsideCClauseSemantics.comap_equiv
    {U E E' : Type*} [Fintype E] [Fintype E']
    (C : SimpleGraph E)
    (incident : U → E → Prop)
    (target : U → E → Nat)
    (h : OutsideCClauseSemantics C incident target)
    (e : E ≃ E') :
    OutsideCClauseSemantics (C.comap e.symm)
      (fun u z ↦ incident u (e.symm z))
      (fun u z ↦ target u (e.symm z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u z ht f hzf huf
    exact h.zero_service u (e.symm z) ht (e.symm f) hzf huf
  · intro u z ht
    obtain ⟨f, hzf, huf⟩ := h.one_service_exists u (e.symm z) ht
    exact ⟨e f, by simpa, by simp [huf]⟩
  · intro u z ht f g hzf huf hzg hug
    apply e.symm.injective
    exact h.one_service_unique u (e.symm z) ht
      (e.symm f) (e.symm g) hzf huf hzg hug
  · intro a b c d hab hcd hac hbc had hbd
    apply h.no_two_common (e.symm a) (e.symm b) (e.symm c) (e.symm d)
    · exact fun heq => hab (e.symm.injective heq)
    · exact fun heq => hcd (e.symm.injective heq)
    · exact hac
    · exact hbc
    · exact had
    · exact hbd

/-- Ambient C4-freeness therefore supplies the complete abstract owner-CNF
semantics after any chosen finite relabeling of the exterior subtype. -/
theorem outsideCClauseSemantics_ownerCoordinates
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (e : {x : V // x ∉ c.supp} ≃ E) :
    OutsideCClauseSemantics
      ((G.induce c.suppᶜ).comap e.symm)
      (fun u z ↦ G.Adj u.1 (e.symm z).1)
      (fun u z ↦ outsideCertificateTarget G c u (e.symm z)) := by
  exact OutsideCClauseSemantics.comap_equiv
    (G.induce c.suppᶜ)
    (fun u z ↦ G.Adj u.1 z.1)
    (outsideCertificateTarget G c)
    (outsideCClauseSemantics_of_ambient G hfree c) e

/-- Two distinct exterior owners whose internal pairs intersect cannot have
an exterior common neighbor.  This is the stronger capacity-zero clause
used by the checked owner CNF: the shared internal endpoint is already one
common neighbor, so another would create a `C4`. -/
theorem outsidePair_intersects_no_exterior_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (a b k : {x : V // x ∉ c.supp}) (hab : a ≠ b)
    (hint : ∃ u : c.supp,
      u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard a).toFinset ∧
      u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard b).toFinset)
    (hak : G.Adj a.1 k.1) (hbk : G.Adj b.1 k.1) : False := by
  obtain ⟨u, hua, hub⟩ := hint
  have hau : G.Adj a.1 u.1 :=
    ((mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard a u).mp hua).symm
  have hbu : G.Adj b.1 u.1 :=
    ((mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard b u).mp hub).symm
  have habval : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have hau_ne : a.1 ≠ u.1 := fun h => a.2 (h ▸ u.2)
  have hbu_ne : b.1 ≠ u.1 := fun h => b.2 (h ▸ u.2)
  have hku_ne : k.1 ≠ u.1 := fun h => k.2 (h ▸ u.2)
  apply hfree
  refine ⟨![a.1, u.1, b.1, k.1], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [C4, SimpleGraph.Adj.symm]

end

end Erdos85

#print axioms Erdos85.OutsideCClauseSemantics.comap_equiv
#print axioms Erdos85.eightEightOwnerAt_lt_sixteen
#print axioms Erdos85.eightEightOwnerSym2_injective
#print axioms Erdos85.mem_eightEightOwnerSym2_iff
#print axioms Erdos85.lowEightExteriorPair_pointwise_model_of_shores
#print axioms Erdos85.outsideCClauseSemantics_ownerCoordinates
#print axioms Erdos85.outsidePair_intersects_no_exterior_common
