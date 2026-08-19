import Proofs.Erdos85OrderSixtyFourOutsideCnfSemantics
import Proofs.Erdos85SizeTwoEigenlineSixTenMixedExteriorModel
import Proofs.Erdos85SizeTwoUnorderedPairServiceCount
import Proofs.Erdos85SixTenMixedOwnerCnf
import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection
import Proofs.Erdos85SixTenMixedOwnerCnfSemantics

/-!
# Transporting exterior-owner clause semantics to finite coordinates

Node: `SIZE-TWO-EIGENLINE(8)/6+10` beneath outline F.3.

The checked mixed-`6+10` owner certificate is stated on a fixed finite owner
type, while the graph-facing routing laws naturally live on the subtype of
vertices exterior to the size-two component.  This file supplies the
equivalence transport layer.  It is deliberately independent of a DIMACS
variable numbering, so the same bridge can be consumed by a regenerated or
minimized certificate.
-/

open SimpleGraph
open Std Sat

namespace Erdos85

namespace SixTenMixedOwnerBridge

noncomputable section

set_option maxHeartbeats 0

/-- The generator's endpoint table is in range on all forty-eight genuine
owner indices. -/
theorem sixTenMixedOwnerAt_lt_sixteen (e : Fin 48) :
    (sixTenMixedOwnerAt e).1 < 16 ∧ (sixTenMixedOwnerAt e).2 < 16 := by
  revert e
  decide

/-- First endpoint of a generated owner as a vertex of the fixed internal
`Fin 16` model. -/
def sixTenMixedOwnerFirst (e : Fin 48) : Fin 16 :=
  ⟨(sixTenMixedOwnerAt e).1, (sixTenMixedOwnerAt_lt_sixteen e).1⟩

/-- Second endpoint of a generated owner as a vertex of the fixed internal
`Fin 16` model. -/
def sixTenMixedOwnerSecond (e : Fin 48) : Fin 16 :=
  ⟨(sixTenMixedOwnerAt e).2, (sixTenMixedOwnerAt_lt_sixteen e).2⟩

/-- The unordered internal pair represented by a generated owner index. -/
def sixTenMixedOwnerSym2 (e : Fin 48) : Sym2 (Fin 16) :=
  s(sixTenMixedOwnerFirst e, sixTenMixedOwnerSecond e)

/-- The generated list has no duplicate unordered owner pairs. -/
theorem sixTenMixedOwnerSym2_injective :
    Function.Injective sixTenMixedOwnerSym2 := by
  decide

/-- Canonical equivalence between the generator's `Fin 48` owner indices
and the range of its typed unordered-pair table. -/
noncomputable def sixTenMixedOwnerRangeEquiv :
    Fin 48 ≃ Set.range sixTenMixedOwnerSym2 :=
  Equiv.ofInjective sixTenMixedOwnerSym2 sixTenMixedOwnerSym2_injective

@[simp] theorem sixTenMixedOwnerRangeEquiv_apply_val (e : Fin 48) :
    (sixTenMixedOwnerRangeEquiv e).1 = sixTenMixedOwnerSym2 e := rfl

/-- The fixed exterior-pair graph represented by the mixed-`6+10` generator. -/
def sixTenMixedExteriorPairGraph : SimpleGraph (Fin 16) where
  Adj a b := sixTenMixedOwnerPair a b = true ∨
    sixTenMixedOwnerPair b a = true
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by intro a h; simp [sixTenMixedOwnerPair] at h⟩

instance : DecidableRel sixTenMixedExteriorPairGraph.Adj := by
  intro a b
  change Decidable
    (sixTenMixedOwnerPair a b = true ∨ sixTenMixedOwnerPair b a = true)
  infer_instance

/-- First-shore embedding of cyclic `ZMod 6` coordinates into the fixed
sixteen-vertex model. -/
def zmodSixLeftFin16 (i : ZMod 6) : Fin 16 :=
  Fin.castAdd 10 ((ZMod.finEquiv 6).symm i)

/-- Second-shore embedding of cyclic `ZMod 10` coordinates into the fixed
sixteen-vertex model. -/
def zmodTenRightFin16 (i : ZMod 10) : Fin 16 :=
  Fin.natAdd 6 ((ZMod.finEquiv 10).symm i)

theorem sixTenMixedExteriorPairGraph_left (i j : ZMod 6) :
    sixTenMixedExteriorPairGraph.Adj
      (zmodSixLeftFin16 i) (zmodSixLeftFin16 j) ↔
        j - i = 3 := by
  revert i j
  decide

theorem sixTenMixedExteriorPairGraph_right (i j : ZMod 10) :
    sixTenMixedExteriorPairGraph.Adj
      (zmodTenRightFin16 i) (zmodTenRightFin16 j) ↔
        j - i = 1 ∨ j - i = 5 ∨ j - i = 9 := by
  revert i j
  decide

theorem sixTenMixedExteriorPairGraph_cross (i : ZMod 6) (j : ZMod 10) :
    sixTenMixedExteriorPairGraph.Adj
      (zmodSixLeftFin16 i) (zmodTenRightFin16 j) ↔
        ((ZMod.finEquiv 6).symm i).val % 2 ≠
          ((ZMod.finEquiv 10).symm j).val % 2 := by
  revert i j
  decide

theorem sixTenMixedOwnerSym2_mem_edgeFinset (e : Fin 48) :
    sixTenMixedOwnerSym2 e ∈ sixTenMixedExteriorPairGraph.edgeFinset := by
  revert e
  decide

/-- A generated owner index as an edge of the fixed exterior-pair graph. -/
def sixTenMixedOwnerEdge (e : Fin 48) :
    sixTenMixedExteriorPairGraph.edgeFinset :=
  ⟨sixTenMixedOwnerSym2 e, sixTenMixedOwnerSym2_mem_edgeFinset e⟩

theorem sixTenMixedOwnerEdge_bijective :
    Function.Bijective sixTenMixedOwnerEdge := by
  decide

/-- Canonical enumeration of all forty-eight edges of the fixed mixed-`6+10`
exterior-pair graph, in exactly the order used by the CNF generator. -/
def sixTenMixedOwnerEdgeEquiv :
    Fin 48 ≃ sixTenMixedExteriorPairGraph.edgeFinset :=
  Equiv.ofBijective sixTenMixedOwnerEdge sixTenMixedOwnerEdge_bijective

@[simp] theorem sixTenMixedOwnerEdgeEquiv_apply_val (e : Fin 48) :
    (sixTenMixedOwnerEdgeEquiv e).1 = sixTenMixedOwnerSym2 e := rfl

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
noncomputable def sixTenMixedExteriorPairModelIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (coord : c.supp ≃ Fin 16)
    (hmodel : ∀ x y : c.supp,
      (exteriorPairGraph G c).Adj x y ↔
        sixTenMixedExteriorPairGraph.Adj (coord x) (coord y)) :
    exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph where
  toEquiv := coord
  map_rel_iff' := by
    intro x y
    exact (hmodel x y).symm

/-- Assemble the pointwise fixed mixed-`6+10` exterior-pair model from its two
cyclic shores.  The statement isolates the purely coordinate bookkeeping
from the graph-specific theorems which provide the three displayed
relations. -/
theorem sixTenMixedExteriorPair_pointwise_model_of_shores
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a b : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (hurange : Set.range u = a.supp)
    (hvrange : Set.range v = b.supp)
    (hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp)
    (coord : c.supp ≃ Fin 16)
    (hcoordu : ∀ i, coord (u i) = zmodSixLeftFin16 i)
    (hcoordv : ∀ j, coord (v j) = zmodTenRightFin16 j)
    (hleft : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (u j) ↔
        j - i = 3)
    (hright : ∀ i j,
      (exteriorPairGraph G c).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 5 ∨ j - i = 9)
    (hcross : ∀ i j,
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        ((ZMod.finEquiv 6).symm i).val % 2 ≠
          ((ZMod.finEquiv 10).symm j).val % 2) :
    ∀ x y : c.supp,
      (exteriorPairGraph G c).Adj x y ↔
        sixTenMixedExteriorPairGraph.Adj (coord x) (coord y) := by
  intro x y
  rcases hcover x with hxa | hxb <;>
    rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [hcoordu, hcoordu, hleft,
      sixTenMixedExteriorPairGraph_left]
  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    rw [hcoordu, hcoordv, hcross,
      sixTenMixedExteriorPairGraph_cross]
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨j, rfl⟩ := hxb
    obtain ⟨i, rfl⟩ := hya
    rw [(exteriorPairGraph G c).adj_comm,
      hcoordv, hcoordu, sixTenMixedExteriorPairGraph.adj_comm,
      hcross, sixTenMixedExteriorPairGraph_cross]
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [hcoordv, hcoordv, hright,
      sixTenMixedExteriorPairGraph_right]

/-- Once the actual exterior-pair graph is identified with the fixed low
`8+8` model, the canonical outside-pair bijection and the generator's exact
edge enumeration compose to label every exterior vertex by `Fin 48`. -/
noncomputable def outsideSixTenMixedOwnerIndexEquiv
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
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph) :
    {x : V // x ∉ c.supp} ≃ Fin 48 :=
  (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
      hcard hinc hqcard hRedges).trans
    ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c)).trans
      (modelIso.mapEdgeSet.trans
        ((edgeFinsetEquivEdgeSet sixTenMixedExteriorPairGraph).symm.trans
          sixTenMixedOwnerEdgeEquiv.symm)))

/-- The composite owner enumeration really sends an outside vertex's owned
pair to the generated pair at its finite index.  This is the key equality
used to rewrite both incidence and target tables below. -/
theorem outsidePair_map_modelIso_eq_ownerSym2
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
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (z : {x : V // x ∉ c.supp}) :
    (outsidePair G (secondOrderDefectGraph G) c hcard z).map modelIso =
      sixTenMixedOwnerSym2
        (outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso z) := by
  have h := congrArg Subtype.val
    (sixTenMixedOwnerEdgeEquiv.apply_symm_apply
      ((edgeFinsetEquivEdgeSet sixTenMixedExteriorPairGraph).symm
        (modelIso.mapEdgeSet
          ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c))
            (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
              hcard hinc hqcard hRedges z)))))
  change ((modelIso.mapEdgeSet
      ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c))
        (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
          hcard hinc hqcard hRedges z))).1) =
    (sixTenMixedOwnerEdge
      (outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso z)).1
  exact h.symm

/-- Membership in the generated pair is exactly the generator's Boolean
incidence predicate. -/
theorem mem_sixTenMixedOwnerSym2_iff (e : Fin 48) (v : Fin 16) :
    v ∈ (sixTenMixedOwnerSym2 e).toFinset ↔
      sixTenMixedOwnerContains e v := by
  revert e v
  decide

/-- A target-table entry is true precisely far enough from both endpoints
that no endpoint can be an internal common neighbor. -/
theorem sixTenMixedOwnerTarget_not_cycleAdj_of_contains
    (e : Fin 48) (v w : Fin 16)
    (htarget : sixTenMixedOwnerTargetContains e v = true)
    (hmem : sixTenMixedOwnerContains e w = true) :
    sixTenCycleAdj v w = false := by
  revert e v w
  decide

/-- The generator's Boolean intersection test is exactly nonempty
intersection of the two typed unordered owner pairs. -/
theorem sixTenMixedOwnersIntersect_iff_sym2
    (e f : Fin 48) :
    sixTenMixedOwnersIntersect e f = true ↔
      ∃ v : Fin 16, v ∈ sixTenMixedOwnerSym2 e ∧
        v ∈ sixTenMixedOwnerSym2 f := by
  revert e f
  decide

/-- Typed characterization of the generator's compatibility filter. -/
theorem sixTenMixedOwnerCompatible_iff_endpoints
    (e f : Fin 48) :
    sixTenMixedOwnerCompatible e f = true ↔
      e ≠ f ∧ ∀ u v : Fin 16,
        u ∈ sixTenMixedOwnerSym2 e → v ∈ sixTenMixedOwnerSym2 f →
          sixTenCycleAdj u v = false := by
  revert e f
  native_decide

/-- In transported owner coordinates, ambient incidence with an exterior
vertex is exactly the generator's endpoint-incidence table. -/
theorem outsideOwnerCoordinates_incident_iff
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
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (e : Fin 48) (v : Fin 16) :
    G.Adj (modelIso.symm v).1
        ((outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
          modelIso).symm e).1 ↔
      sixTenMixedOwnerContains e v = true := by
  let idx := outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  let z := idx.symm e
  have hpair := outsidePair_map_modelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges modelIso z
  have hidx : idx z = e := idx.apply_symm_apply e
  calc
    G.Adj (modelIso.symm v).1 z.1 ↔
        modelIso.symm v ∈
          outsidePair G (secondOrderDefectGraph G) c hcard z := by
      rw [← Sym2.mem_toFinset]
      exact (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard z (modelIso.symm v)).symm
    _ ↔ v ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).map
          modelIso := by
      rw [Sym2.mem_map]
      constructor
      · intro hv
        exact ⟨modelIso.symm v, hv, modelIso.apply_symm_apply v⟩
      · rintro ⟨u, hu, huv⟩
        have : u = modelIso.symm v := modelIso.injective
          (huv.trans (modelIso.apply_symm_apply v).symm)
        simpa [this] using hu
    _ ↔ v ∈ sixTenMixedOwnerSym2 e := by
      rw [hpair, hidx]
    _ ↔ sixTenMixedOwnerContains e v = true := by
      rw [← Sym2.mem_toFinset]
      exact mem_sixTenMixedOwnerSym2_iff e v

/-- The generator target `true` rewrites to certificate target one once the
chosen internal coordinates identify ambient adjacency with the two fixed
eight-cycles. -/
theorem outsideOwnerCoordinates_target_eq_one
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
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ sixTenCycleAdj (modelIso x).val (modelIso y).val = true)
    (e : Fin 48) (v : Fin 16)
    (htarget : sixTenMixedOwnerTargetContains e v = true) :
    outsideCertificateTarget G c (modelIso.symm v)
        ((outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
          modelIso).symm e) = 1 := by
  classical
  let idx := outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  let z := idx.symm e
  unfold outsideCertificateTarget
  have empty_target (s : Finset V) (hs : s = ∅) : 1 - s.card = 1 := by
    simp [hs]
  apply empty_target
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwdata : w ∈
      (G.neighborFinset (modelIso.symm v).1 ∩ G.neighborFinset z.1) ∧
      w ∈ c.supp := by
    simpa only [Finset.mem_filter] using hw
  have hwcommon := Finset.mem_inter.mp hwdata.1
  have hwsupp : w ∈ c.supp := hwdata.2
  let ws : c.supp := ⟨w, hwsupp⟩
  have hvw : G.Adj (modelIso.symm v).1 ws.1 :=
    (G.mem_neighborFinset (modelIso.symm v).1 w).mp hwcommon.1
  have hzw : G.Adj z.1 ws.1 :=
    (G.mem_neighborFinset z.1 w).mp (by simpa [z, idx] using hwcommon.2)
  have hwinc : sixTenMixedOwnerContains e (modelIso ws) = true := by
    have := (outsideOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges modelIso e (modelIso ws)).mp
      (by simpa [idx, z] using hzw.symm)
    simpa using this
  have hfalse := sixTenMixedOwnerTarget_not_cycleAdj_of_contains
    e v (modelIso ws) htarget hwinc
  have htrue : sixTenCycleAdj v (modelIso ws) = true := by
    simpa using (hcycle (modelIso.symm v) ws).mp hvw
  simp_all

/-- High-level finite semantics of the checked owner instance, before any
DIMACS numbering.  This is the clean handshake between graph transport and
the generator-local literal bookkeeping. -/
structure SixTenMixedOwnerFiniteSemantics
    (X : Fin 48 → Fin 48 → Prop) : Prop where
  service_exists : ∀ e : Fin 48, ∀ v : Fin 16,
    sixTenMixedOwnerTargetContains e v = true →
      ∃ f : Fin 48, X e f ∧ sixTenMixedOwnerContains f v = true
  service_unique : ∀ e : Fin 48, ∀ v : Fin 16,
    sixTenMixedOwnerTargetContains e v = true →
      ∀ f g : Fin 48, X e f → sixTenMixedOwnerContains f v = true →
        X e g → sixTenMixedOwnerContains g v = true → f = g
  intersecting_no_common : ∀ e f : Fin 48,
    e ≠ f → sixTenMixedOwnersIntersect e f = true →
      ∀ k : Fin 48, X e k → X f k → False
  no_two_common : ∀ e f : Fin 48, e ≠ f →
    ∀ k l : Fin 48, k ≠ l →
      X e k → X f k → X e l → X f l → False

/-- Truth assignment induced directly by a finite owner adjacency relation.
Using an existential decoder keeps the definition independent of an
arbitrary orientation of the unordered generator variables. -/
def sixTenMixedOwnerValOfRelation
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X] : DimacsValuation :=
  fun id ↦ decide (∃ e f : Fin 48,
    sixTenMixedOwnerVariable? e f = some id ∧ X e f)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Compatible distinct owners always have a generated DIMACS variable. -/
theorem sixTenMixedOwnerVariable?_exists
    (e f : Fin 48) (hef : e ≠ f)
    (hcompat : sixTenMixedOwnerCompatible e f = true) :
    ∃ id : Nat, sixTenMixedOwnerVariable? e f = some id := by
  have hsome : (sixTenMixedOwnerVariable? e f).isSome = true := by
    revert e f
    native_decide
  cases hopt : sixTenMixedOwnerVariable? e f with
  | none => simp [hopt] at hsome
  | some id => exact ⟨id, rfl⟩

/-- A generated variable identifier determines its unordered owner pair. -/
theorem sixTenMixedOwnerVariable?_eq_injective
    (e f a b : Fin 48)
    (hsome : (sixTenMixedOwnerVariable? e f).isSome = true)
    (heq : sixTenMixedOwnerVariable? e f = sixTenMixedOwnerVariable? a b) :
    (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
  let p : Nat × Nat := if e.val < f.val then (e.val, f.val) else (f.val, e.val)
  let q : Nat × Nat := if a.val < b.val then (a.val, b.val) else (b.val, a.val)
  have heqIdx : sixTenMixedOwnerVariables.idxOf? p =
      sixTenMixedOwnerVariables.idxOf? q := by
    simpa only [sixTenMixedOwnerVariable?, p, q] using
      Option.map_injective (f := fun n : Nat ↦ n + 1)
        (fun _ _ h ↦ Nat.add_right_cancel h) heq
  have hpSome : (sixTenMixedOwnerVariables.idxOf? p).isSome = true := by
    simpa only [sixTenMixedOwnerVariable?, p, Option.isSome_map] using hsome
  cases hp : sixTenMixedOwnerVariables.idxOf? p with
  | none => simp [hp] at hpSome
  | some i =>
      have hq : sixTenMixedOwnerVariables.idxOf? q = some i := by
        rw [← heqIdx, hp]
      obtain ⟨hi, hgetp, _⟩ := List.idxOf?_eq_some_iff.mp hp
      obtain ⟨_, hgetq, _⟩ := List.idxOf?_eq_some_iff.mp hq
      have hpq : p = q := hgetp.symm.trans hgetq
      dsimp [p, q] at hpq
      split at hpq <;> split at hpq
      <;> simp only [Prod.mk.injEq] at hpq
      <;> omega

theorem sixTenMixedOwnerValOfRelation_true_iff
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X] (id : Nat) :
    sixTenMixedOwnerValOfRelation X id = true ↔
      ∃ e f : Fin 48, sixTenMixedOwnerVariable? e f = some id ∧ X e f := by
  simp [sixTenMixedOwnerValOfRelation]

theorem sixTenMixedOwnerValOfRelation_true_of
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X]
    {e f : Fin 48} {id : Nat}
    (hvar : sixTenMixedOwnerVariable? e f = some id) (hX : X e f) :
    sixTenMixedOwnerValOfRelation X id = true :=
  (sixTenMixedOwnerValOfRelation_true_iff X id).mpr ⟨e, f, hvar, hX⟩

theorem sixTenMixedOwnerRelation_of_val_true
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    {e f : Fin 48} {id : Nat}
    (hvar : sixTenMixedOwnerVariable? e f = some id)
    (hval : sixTenMixedOwnerValOfRelation X id = true) : X e f := by
  obtain ⟨a, b, hab, hX⟩ :=
    (sixTenMixedOwnerValOfRelation_true_iff X id).mp hval
  have hpairs := sixTenMixedOwnerVariable?_eq_injective e f a b
    (by simp [hvar]) (hvar.trans hab.symm)
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hX
  · exact hsymm _ _ hX

/-- Decode membership in a generated service-variable row back to its
finite owner endpoint and literal identifier. -/
theorem mem_sixTenMixedOwnerServiceVariables_iff
    (e : Fin 48) (v : Fin 16) (lit : Int) :
    lit ∈ sixTenMixedOwnerServiceVariables e v ↔
      ∃ f : Fin 48, f ≠ e ∧ sixTenMixedOwnerContains f v = true ∧
        sixTenMixedOwnerLiteral? e f = some lit := by
  simp only [sixTenMixedOwnerServiceVariables, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨f, hf48, hflit⟩
    split at hflit
    · next hcond =>
      have hc : f ≠ e.val ∧ sixTenMixedOwnerContains f v = true := by
        simpa using hcond
      refine ⟨⟨f, hf48⟩, ?_, ?_, ?_⟩
      · intro h
        exact hc.1 (congrArg Fin.val h)
      · simpa using hc.2
      · simpa using hflit
    · simp at hflit
  · rintro ⟨f, hfe, hcontains, hlit⟩
    refine ⟨f, f.2, ?_⟩
    rw [if_pos]
    · exact hlit
    · have hne : f.val ≠ e.val := fun h ↦ hfe (Fin.ext h)
      simp [hne, hcontains]

theorem sixTenMixedOwnerVariable?_positive
    {e f : Fin 48} {id : Nat}
    (hvar : sixTenMixedOwnerVariable? e f = some id) : 0 < id := by
  unfold sixTenMixedOwnerVariable? at hvar
  split at hvar
  · cases hidx : sixTenMixedOwnerVariables.idxOf? (e.val, f.val) <;>
      simp [hidx] at hvar
    omega
  · cases hidx : sixTenMixedOwnerVariables.idxOf? (f.val, e.val) <;>
      simp [hidx] at hvar
    omega

theorem sixTenMixedOwnerLiteral?_eq_some
    {e f : Fin 48} {lit : Int}
    (hlit : sixTenMixedOwnerLiteral? e f = some lit) :
    ∃ id : Nat, sixTenMixedOwnerVariable? e f = some id ∧ lit = Int.ofNat id := by
  unfold sixTenMixedOwnerLiteral? at hlit
  cases hvar : sixTenMixedOwnerVariable? e f with
  | none => simp [hvar] at hlit
  | some id =>
      simp [hvar] at hlit
      exact ⟨id, rfl, hlit.symm⟩

/-- The positive exact-service clause is satisfied by an actual relation
edge supplied by the high-level finite semantics. -/
theorem sixTenMixedOwnerServiceClauseSatisfied_of_relation
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X]
    (hsem : SixTenMixedOwnerFiniteSemantics X)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f → sixTenMixedOwnerCompatible e f = true)
    (e v : Nat) (he : e < 48) (hv : v < 16)
    (htarget : sixTenMixedOwnerTargetContains e v = true) :
    dimacsClauseSatisfied (sixTenMixedOwnerValOfRelation X)
      (sixTenMixedOwnerServiceVariables e v) := by
  let ef : Fin 48 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  obtain ⟨f, hX, hcontains⟩ := hsem.service_exists ef vf (by simpa using htarget)
  have hfe : f ≠ ef := by
    intro h
    subst f
    exact hirr ef hX
  obtain ⟨id, hvar⟩ := sixTenMixedOwnerVariable?_exists ef f hfe.symm
    (hcompat ef f hX)
  have hlit : sixTenMixedOwnerLiteral? ef f = some (Int.ofNat id) := by
    simp [sixTenMixedOwnerLiteral?, hvar]
  have hmem : Int.ofNat id ∈ sixTenMixedOwnerServiceVariables e v :=
    (mem_sixTenMixedOwnerServiceVariables_iff ef vf (Int.ofNat id)).mpr
      ⟨f, hfe, hcontains, hlit⟩
  refine ⟨Int.ofNat id, hmem, ?_⟩
  have hval := sixTenMixedOwnerValOfRelation_true_of X hvar hX
  have hid := sixTenMixedOwnerVariable?_positive hvar
  simp [dimacsLitValue, hid, hval]

/-- Pairwise-negative service clauses follow from uniqueness of the owner
serving the selected internal vertex. -/
theorem sixTenMixedOwnerServiceUniqueClauseSatisfied_of_relation
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X]
    (hsem : SixTenMixedOwnerFiniteSemantics X)
    (hsymm : ∀ e f, X e f → X f e)
    (e v : Nat) (he : e < 48) (hv : v < 16)
    (htarget : sixTenMixedOwnerTargetContains e v = true)
    (clause : DimacsClause)
    (hclause : clause ∈ eightEightPairwiseNegativeClauses
      (sixTenMixedOwnerServiceVariables e v)) :
    dimacsClauseSatisfied (sixTenMixedOwnerValOfRelation X) clause := by
  simp only [eightEightPairwiseNegativeClauses, List.mem_flatMap,
    List.mem_map, List.mem_filter] at hclause
  obtain ⟨x, hxrow, y, ⟨hyrow, hxy⟩, rfl⟩ := hclause
  let ef : Fin 48 := ⟨e, he⟩
  let vf : Fin 16 := ⟨v, hv⟩
  obtain ⟨f, hfe, hfcontains, hfx⟩ :=
    (mem_sixTenMixedOwnerServiceVariables_iff ef vf x).mp hxrow
  obtain ⟨g, hge, hgcontains, hgy⟩ :=
    (mem_sixTenMixedOwnerServiceVariables_iff ef vf y).mp hyrow
  obtain ⟨ix, hvarx, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hfx
  obtain ⟨iy, hvary, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hgy
  have hix := sixTenMixedOwnerVariable?_positive hvarx
  have hiy := sixTenMixedOwnerVariable?_positive hvary
  by_cases hxval : sixTenMixedOwnerValOfRelation X ix = true
  · have hXf := sixTenMixedOwnerRelation_of_val_true X hsymm hvarx hxval
    have hyfalse : sixTenMixedOwnerValOfRelation X iy = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hyval
      have hXg := sixTenMixedOwnerRelation_of_val_true X hsymm hvary hyval
      have hfg := hsem.service_unique ef vf (by simpa using htarget)
        f g hXf hfcontains hXg hgcontains
      subst g
      have : ix = iy := by simpa [hvarx] using hvary
      subst iy
      simp at hxy
    refine ⟨-Int.ofNat iy, by simp, ?_⟩
    simp [dimacsLitValue, hiy, hyfalse]
  · have hxf : sixTenMixedOwnerValOfRelation X ix = false :=
      Bool.eq_false_of_not_eq_true hxval
    refine ⟨-Int.ofNat ix, by simp, ?_⟩
    simp [dimacsLitValue, hix, hxf]

/-- Intersecting-owner negative clauses follow from their high-level
capacity-zero property. -/
theorem sixTenMixedOwnerNoCommonClauseSatisfied_of_relation
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X]
    (hsem : SixTenMixedOwnerFiniteSemantics X)
    (hsymm : ∀ e f, X e f → X f e)
    (e f : Nat) (hef : e < f) (hf48 : f < 48)
    (hintersect : sixTenMixedOwnersIntersect e f = true)
    (clause : DimacsClause)
    (hclause : clause ∈ sixTenMixedOwnerNoCommonClauses e f) :
    dimacsClauseSatisfied (sixTenMixedOwnerValOfRelation X) clause := by
  simp only [sixTenMixedOwnerNoCommonClauses, List.mem_filterMap] at hclause
  obtain ⟨k, hkcand, hclause⟩ := hclause
  simp only [sixTenMixedOwnerCommonCandidates, List.mem_filter,
    List.mem_range] at hkcand
  have hk48 := hkcand.1
  cases hxe : sixTenMixedOwnerLiteral? e k with
  | none => simp [hxe] at hclause
  | some x =>
    cases hyf : sixTenMixedOwnerLiteral? f k with
    | none => simp [hxe, hyf] at hclause
    | some y =>
      simp [hxe, hyf] at hclause
      subst clause
      let ef : Fin 48 := ⟨e, by omega⟩
      let ff : Fin 48 := ⟨f, hf48⟩
      let kf : Fin 48 := ⟨k, hk48⟩
      have hxe' : sixTenMixedOwnerLiteral? ef kf = some x := by
        simpa [ef, kf] using hxe
      have hyf' : sixTenMixedOwnerLiteral? ff kf = some y := by
        simpa [ff, kf] using hyf
      obtain ⟨ix, hvarx, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hxe'
      obtain ⟨iy, hvary, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hyf'
      by_cases hxval : sixTenMixedOwnerValOfRelation X ix = true
      · have hXek := sixTenMixedOwnerRelation_of_val_true X hsymm hvarx hxval
        have hyfalse : sixTenMixedOwnerValOfRelation X iy = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hyval
          have hXfk := sixTenMixedOwnerRelation_of_val_true X hsymm hvary hyval
          exact hsem.intersecting_no_common ef ff (by
            intro h
            have := congrArg Fin.val h
            dsimp [ef, ff] at this
            omega)
            (by simpa using hintersect) kf hXek hXfk
        refine ⟨-Int.ofNat iy, by simp, ?_⟩
        simp [dimacsLitValue, hyfalse]
      · have hxf : sixTenMixedOwnerValOfRelation X ix = false :=
          Bool.eq_false_of_not_eq_true hxval
        refine ⟨-Int.ofNat ix, by simp, ?_⟩
        simp [dimacsLitValue, hxf]

/-- Four-literal ordinary C4 clauses follow from the high-level assertion
that two distinct owners cannot have two distinct common neighbors. -/
theorem sixTenMixedOwnerAtMostOneCommonClauseSatisfied_of_relation
    (X : Fin 48 → Fin 48 → Prop) [DecidableRel X]
    (hsem : SixTenMixedOwnerFiniteSemantics X)
    (hsymm : ∀ e f, X e f → X f e)
    (e f : Nat) (hef : e < f) (hf48 : f < 48)
    (clause : DimacsClause)
    (hclause : clause ∈ sixTenMixedOwnerAtMostOneCommonClauses e f) :
    dimacsClauseSatisfied (sixTenMixedOwnerValOfRelation X) clause := by
  simp only [sixTenMixedOwnerAtMostOneCommonClauses, List.mem_flatMap,
    List.mem_filterMap, List.mem_filter] at hclause
  obtain ⟨k, hkcand, l, ⟨hlcand, hkl⟩, hclause⟩ := hclause
  have hk48 : k < 48 := by
    have hkdata := hkcand
    simp only [sixTenMixedOwnerCommonCandidates, List.mem_filter,
      List.mem_range] at hkdata
    exact hkdata.1
  have hl48 : l < 48 := by
    have hldata := hlcand
    simp only [sixTenMixedOwnerCommonCandidates, List.mem_filter,
      List.mem_range] at hldata
    exact hldata.1
  have hklNat : k < l := by simpa using hkl
  cases hxek : sixTenMixedOwnerLiteral? e k with
  | none => simp [hxek] at hclause
  | some xek =>
    cases hxfk : sixTenMixedOwnerLiteral? f k with
    | none => simp [hxek, hxfk] at hclause
    | some xfk =>
      cases hxel : sixTenMixedOwnerLiteral? e l with
      | none => simp [hxek, hxfk, hxel] at hclause
      | some xel =>
        cases hxfl : sixTenMixedOwnerLiteral? f l with
        | none => simp [hxek, hxfk, hxel, hxfl] at hclause
        | some xfl =>
          simp [hxek, hxfk, hxel, hxfl] at hclause
          subst clause
          let ef : Fin 48 := ⟨e, by omega⟩
          let ff : Fin 48 := ⟨f, hf48⟩
          let kf : Fin 48 := ⟨k, hk48⟩
          let lf : Fin 48 := ⟨l, hl48⟩
          have hxek' : sixTenMixedOwnerLiteral? ef kf = some xek := by
            simpa [ef, kf] using hxek
          have hxfk' : sixTenMixedOwnerLiteral? ff kf = some xfk := by
            simpa [ff, kf] using hxfk
          have hxel' : sixTenMixedOwnerLiteral? ef lf = some xel := by
            simpa [ef, lf] using hxel
          have hxfl' : sixTenMixedOwnerLiteral? ff lf = some xfl := by
            simpa [ff, lf] using hxfl
          obtain ⟨iek, hvek, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hxek'
          obtain ⟨ifk, hvfk, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hxfk'
          obtain ⟨iel, hvel, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hxel'
          obtain ⟨ifl, hvfl, rfl⟩ := sixTenMixedOwnerLiteral?_eq_some hxfl'
          by_cases hekval : sixTenMixedOwnerValOfRelation X iek = true
          · by_cases hfkval : sixTenMixedOwnerValOfRelation X ifk = true
            · by_cases helval : sixTenMixedOwnerValOfRelation X iel = true
              · have hflfalse : sixTenMixedOwnerValOfRelation X ifl = false := by
                  apply Bool.eq_false_of_not_eq_true
                  intro hflval
                  have hXek := sixTenMixedOwnerRelation_of_val_true X hsymm hvek hekval
                  have hXfk := sixTenMixedOwnerRelation_of_val_true X hsymm hvfk hfkval
                  have hXel := sixTenMixedOwnerRelation_of_val_true X hsymm hvel helval
                  have hXfl := sixTenMixedOwnerRelation_of_val_true X hsymm hvfl hflval
                  exact hsem.no_two_common ef ff (by
                    intro h
                    have := congrArg Fin.val h
                    dsimp [ef, ff] at this
                    omega) kf lf (by
                      intro h
                      have := congrArg Fin.val h
                      dsimp [kf, lf] at this
                      exact (Nat.ne_of_lt hklNat) this) hXek hXfk hXel hXfl
                refine ⟨-Int.ofNat ifl, by simp, ?_⟩
                simp [dimacsLitValue, hflfalse]
              · have hfalse := Bool.eq_false_of_not_eq_true helval
                refine ⟨-Int.ofNat iel, by simp, ?_⟩
                simp [dimacsLitValue, hfalse]
            · have hfalse := Bool.eq_false_of_not_eq_true hfkval
              refine ⟨-Int.ofNat ifk, by simp, ?_⟩
              simp [dimacsLitValue, hfalse]
          · have hfalse := Bool.eq_false_of_not_eq_true hekval
            refine ⟨-Int.ofNat iek, by simp, ?_⟩
            simp [dimacsLitValue, hfalse]

/-- Generator-local adapter from the clean finite relation semantics to the
four DIMACS clause families consumed by the checked certificate. -/
theorem SixTenMixedOwnerFiniteSemantics.to_constraintSemantics
    {X : Fin 48 → Fin 48 → Prop} [DecidableRel X]
    (hsem : SixTenMixedOwnerFiniteSemantics X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f → sixTenMixedOwnerCompatible e f = true) :
    SixTenMixedOwnerConstraintSemantics
      (sixTenMixedOwnerValOfRelation X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sixTenMixedOwnerServiceClauseSatisfied_of_relation
      X hsem hirr hcompat
  · intro e v clause he hv ht hc
    exact sixTenMixedOwnerServiceUniqueClauseSatisfied_of_relation
      X hsem hsymm e v he hv ht clause hc
  · intro e f clause hef hf hi hc
    exact sixTenMixedOwnerNoCommonClauseSatisfied_of_relation
      X hsem hsymm e f hef hf hi clause hc
  · intro e f clause hef hf48 _hdisjoint hclause
    exact sixTenMixedOwnerAtMostOneCommonClauseSatisfied_of_relation
      X hsem hsymm e f hef hf48 clause hclause

/-- The high-level finite owner constraints are themselves contradictory
whenever the relation is a simple compatible owner graph. -/
theorem SixTenMixedOwnerFiniteSemantics.false
    {X : Fin 48 → Fin 48 → Prop} [DecidableRel X]
    (hsem : SixTenMixedOwnerFiniteSemantics X)
    (hsymm : ∀ e f, X e f → X f e)
    (hirr : ∀ e, ¬ X e e)
    (hcompat : ∀ e f, X e f → sixTenMixedOwnerCompatible e f = true) : False :=
  sixTenMixedOwnerConstraintSemantics_false
    (hsem.to_constraintSemantics hsymm hirr hcompat)

/-- Convert the generic exact-service/C4 semantic package into the fixed
high-level owner interface.  Only two coordinate rewrites are required:
generator targets must select target value one, and fixed incidence must
agree with the abstract incidence relation.  The stronger zero-common rule
for intersecting owners is supplied separately. -/
theorem SixTenMixedOwnerFiniteSemantics.of_clauseSemantics
    {U : Type*}
    (C : SimpleGraph (Fin 48))
    (incident : U → Fin 48 → Prop)
    (target : U → Fin 48 → Nat)
    (coord : U ≃ Fin 16)
    (h : OutsideCClauseSemantics C incident target)
    (htarget : ∀ e : Fin 48, ∀ v : Fin 16,
      sixTenMixedOwnerTargetContains e v = true →
        target (coord.symm v) e = 1)
    (hincident : ∀ e : Fin 48, ∀ v : Fin 16,
      incident (coord.symm v) e ↔ sixTenMixedOwnerContains e v = true)
    (hintersect : ∀ e f : Fin 48,
      e ≠ f → sixTenMixedOwnersIntersect e f = true →
        ∀ k : Fin 48, C.Adj e k → C.Adj f k → False) :
    SixTenMixedOwnerFiniteSemantics C.Adj := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e v hev
    obtain ⟨f, hef, hvf⟩ :=
      h.one_service_exists (coord.symm v) e (htarget e v hev)
    exact ⟨f, hef, (hincident f v).mp hvf⟩
  · intro e v hev f g hef hvf heg hvg
    exact h.one_service_unique (coord.symm v) e (htarget e v hev)
      f g hef ((hincident f v).mpr hvf) heg ((hincident g v).mpr hvg)
  · exact hintersect
  · intro e f hef k l hkl hek hfk hel hfl
    exact h.no_two_common e f k l hef hkl hek hfk hel hfl

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
    [DecidablePred (· ∈ c.supp)]
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

/-- Intersecting generated owners transport to genuinely intersecting
actual outside pairs, so ambient C4-freeness supplies their capacity-zero
common-neighbor clause. -/
theorem outsideOwnerCoordinates_intersecting_no_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (e f : Fin 48) (hef : e ≠ f)
    (hintersect : sixTenMixedOwnersIntersect e f = true)
    (k : Fin 48)
    (hek : ((G.induce c.suppᶜ).comap
      (outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
        modelIso).symm).Adj e k)
    (hfk : ((G.induce c.suppᶜ).comap
      (outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
        modelIso).symm).Adj f k) : False := by
  let idx := outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  let a := idx.symm e
  let b := idx.symm f
  let x := idx.symm k
  have hab : a ≠ b := by
    intro h
    apply hef
    exact idx.symm.injective (by simpa [a, b] using h)
  obtain ⟨v, hve, hvf⟩ :=
    (sixTenMixedOwnersIntersect_iff_sym2 e f).mp hintersect
  let u : c.supp := modelIso.symm v
  have hpaira := outsidePair_map_modelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges modelIso a
  have hpairb := outsidePair_map_modelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges modelIso b
  have hia : outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
      modelIso a = e := by
    simpa [idx, a] using idx.apply_symm_apply e
  have hib : outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
      modelIso b = f := by
    simpa [idx, b] using idx.apply_symm_apply f
  have hua : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard a).toFinset := by
    rw [Sym2.mem_toFinset]
    have hvmap : v ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard a).map modelIso := by
      rw [hpaira, hia]
      exact hve
    rw [Sym2.mem_map] at hvmap
    obtain ⟨w, hw, hwv⟩ := hvmap
    have hwu : w = u := modelIso.injective
      (hwv.trans (modelIso.apply_symm_apply v).symm)
    simpa [hwu] using hw
  have hub : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard b).toFinset := by
    rw [Sym2.mem_toFinset]
    have hvmap : v ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard b).map modelIso := by
      rw [hpairb, hib]
      exact hvf
    rw [Sym2.mem_map] at hvmap
    obtain ⟨w, hw, hwv⟩ := hvmap
    have hwu : w = u := modelIso.injective
      (hwv.trans (modelIso.apply_symm_apply v).symm)
    simpa [hwu] using hw
  apply outsidePair_intersects_no_exterior_common
    G hfree c hcard a b x hab ⟨u, hua, hub⟩
  · exact hek
  · exact hfk

/-- Complete graph-facing finite semantics for the fixed mixed-`6+10` owner
instance.  All DIMACS numbering is absent: the result speaks only about
the transported exterior adjacency relation on `Fin 48`. -/
theorem sixTenMixedOwnerFiniteSemantics_of_modelIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ sixTenCycleAdj (modelIso x).val (modelIso y).val = true) :
    SixTenMixedOwnerFiniteSemantics
      (((G.induce c.suppᶜ).comap
        (outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
          modelIso).symm).Adj) := by
  let idx := outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  apply SixTenMixedOwnerFiniteSemantics.of_clauseSemantics
    ((G.induce c.suppᶜ).comap idx.symm)
    (fun u e ↦ G.Adj u.1 (idx.symm e).1)
    (fun u e ↦ outsideCertificateTarget G c u (idx.symm e))
    modelIso.toEquiv
    (outsideCClauseSemantics_ownerCoordinates G hfree c idx)
  · intro e v htarget
    exact outsideOwnerCoordinates_target_eq_one
      G c hcard hinc hqcard hRedges modelIso hcycle e v htarget
  · intro e v
    exact outsideOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges modelIso e v
  · intro e f hef hintersect k hek hfk
    exact outsideOwnerCoordinates_intersecting_no_common
      G hfree c hcard hinc hqcard hRedges modelIso
      e f hef hintersect k hek hfk

/-- Adjacent exterior owners are mutually compatible: no endpoint of one
owned pair is ambient-adjacent to an endpoint of the other.  Such an edge
would complete a `C4` through the two exterior owners. -/
theorem adjacent_outsidePair_endpoint_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (a b : {x : V // x ∉ c.supp}) (hab : G.Adj a.1 b.1)
    (u v : c.supp)
    (hua : u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard a).toFinset)
    (hvb : v ∈ (outsidePair G (secondOrderDefectGraph G) c hcard b).toFinset) :
    ¬ G.Adj u.1 v.1 := by
  intro huv
  have hau : G.Adj a.1 u.1 :=
    ((mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard a u).mp hua).symm
  have hbv : G.Adj b.1 v.1 :=
    ((mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard b v).mp hvb).symm
  have habne : a.1 ≠ b.1 := G.ne_of_adj hab
  have huvne : u.1 ≠ v.1 := G.ne_of_adj huv
  have haune : a.1 ≠ u.1 := fun h => a.2 (h ▸ u.2)
  have havne : a.1 ≠ v.1 := fun h => a.2 (h ▸ v.2)
  have hbune : b.1 ≠ u.1 := fun h => b.2 (h ▸ u.2)
  have hbvne : b.1 ≠ v.1 := fun h => b.2 (h ▸ v.2)
  apply hfree
  refine ⟨![a.1, u.1, v.1, b.1], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [C4, SimpleGraph.Adj.symm]

/-- Every transported exterior adjacency survives the generator's
compatibility filter. -/
theorem outsideOwnerCoordinates_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ sixTenCycleAdj (modelIso x).val (modelIso y).val = true)
    (e f : Fin 48)
    (hef : ((G.induce c.suppᶜ).comap
      (outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges
        modelIso).symm).Adj e f) :
    sixTenMixedOwnerCompatible e f = true := by
  let idx := outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  let a := idx.symm e
  let b := idx.symm f
  have hab : G.Adj a.1 b.1 := hef
  apply (sixTenMixedOwnerCompatible_iff_endpoints e f).mpr
  refine ⟨?_, ?_⟩
  · intro h
    subst f
    exact G.loopless.irrefl a.1 hab
  · intro u v hue hvf
    let us : c.supp := modelIso.symm u
    let vs : c.supp := modelIso.symm v
    have hua : us ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard a).toFinset := by
      apply (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard a us).mpr
      have hincu := (outsideOwnerCoordinates_incident_iff
        G c hcard hinc hqcard hRedges modelIso e u).mpr
        ((mem_sixTenMixedOwnerSym2_iff e u).mp
          (Sym2.mem_toFinset.mpr hue))
      simpa [idx, a, us] using hincu
    have hvb : vs ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard b).toFinset := by
      apply (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard b vs).mpr
      have hincv := (outsideOwnerCoordinates_incident_iff
        G c hcard hinc hqcard hRedges modelIso f v).mpr
        ((mem_sixTenMixedOwnerSym2_iff f v).mp
          (Sym2.mem_toFinset.mpr hvf))
      simpa [idx, b, vs] using hincv
    have hnot := adjacent_outsidePair_endpoint_not_adj
      G hfree c hcard a b hab us vs hua hvb
    cases hcv : sixTenCycleAdj u v with
    | false => rfl
    | true =>
      exfalso
      apply hnot
      apply (hcycle us vs).mpr
      simpa [us, vs] using hcv

/-- Checked mixed-`6+10` terminal: no C4-free ambient graph can realize the
fixed exterior-pair model together with its two-cycle internal model. -/
theorem sixTenMixedExteriorPairModel_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (modelIso : exteriorPairGraph G c ≃g sixTenMixedExteriorPairGraph)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ sixTenCycleAdj (modelIso x).val (modelIso y).val = true) :
    False := by
  let idx := outsideSixTenMixedOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  let C := (G.induce c.suppᶜ).comap idx.symm
  have hsem : SixTenMixedOwnerFiniteSemantics C.Adj :=
    sixTenMixedOwnerFiniteSemantics_of_modelIso
      G hfree c hcard hinc hqcard hRedges modelIso hcycle
  apply hsem.false
  · intro e f hef
    exact (C.adj_comm e f).mp hef
  · intro e hee
    exact C.loopless.irrefl e hee
  · intro e f hef
    exact outsideOwnerCoordinates_compatible
      G hfree c hcard hinc hqcard hRedges modelIso hcycle e f hef

end

end SixTenMixedOwnerBridge

end Erdos85

#print axioms Erdos85.SixTenMixedOwnerBridge.SixTenMixedOwnerFiniteSemantics.to_constraintSemantics
#print axioms Erdos85.SixTenMixedOwnerBridge.sixTenMixedExteriorPairModel_false
