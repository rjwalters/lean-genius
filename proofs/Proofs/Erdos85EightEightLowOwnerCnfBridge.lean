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
    (modelIso : exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph)
    (z : {x : V // x ∉ c.supp}) :
    (outsidePair G (secondOrderDefectGraph G) c hcard z).map modelIso =
      eightEightOwnerSym2
        (outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso z) := by
  have h := congrArg Subtype.val
    (eightEightOwnerEdgeEquiv.apply_symm_apply
      ((edgeFinsetEquivEdgeSet eightEightLowExteriorPairGraph).symm
        (modelIso.mapEdgeSet
          ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c))
            (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
              hcard hinc hqcard hRedges z)))))
  change ((modelIso.mapEdgeSet
      ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c))
        (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
          hcard hinc hqcard hRedges z))).1) =
    (eightEightOwnerEdge
      (outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso z)).1
  exact h.symm

/-- Membership in the generated pair is exactly the generator's Boolean
incidence predicate. -/
theorem mem_eightEightOwnerSym2_iff (e : Fin 48) (v : Fin 16) :
    v ∈ (eightEightOwnerSym2 e).toFinset ↔
      eightEightOwnerContains e v := by
  revert e v
  decide

/-- A target-table entry is true precisely far enough from both endpoints
that no endpoint can be an internal common neighbor. -/
theorem eightEightOwnerTarget_not_cycleAdj_of_contains
    (e : Fin 48) (v w : Fin 16)
    (htarget : eightEightOwnerTargetContains e v = true)
    (hmem : eightEightOwnerContains e w = true) :
    eightEightCycleAdj v w = false := by
  revert e v w
  decide

/-- The generator's Boolean intersection test is exactly nonempty
intersection of the two typed unordered owner pairs. -/
theorem eightEightOwnersIntersect_iff_sym2
    (e f : Fin 48) :
    eightEightOwnersIntersect e f = true ↔
      ∃ v : Fin 16, v ∈ eightEightOwnerSym2 e ∧
        v ∈ eightEightOwnerSym2 f := by
  revert e f
  decide

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
    (modelIso : exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph)
    (e : Fin 48) (v : Fin 16) :
    G.Adj (modelIso.symm v).1
        ((outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
          modelIso).symm e).1 ↔
      eightEightOwnerContains e v = true := by
  let idx := outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
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
    _ ↔ v ∈ eightEightOwnerSym2 e := by
      rw [hpair, hidx]
    _ ↔ eightEightOwnerContains e v = true := by
      rw [← Sym2.mem_toFinset]
      exact mem_eightEightOwnerSym2_iff e v

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
    (modelIso : exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ eightEightCycleAdj (modelIso x).val (modelIso y).val = true)
    (e : Fin 48) (v : Fin 16)
    (htarget : eightEightOwnerTargetContains e v = true) :
    outsideCertificateTarget G c (modelIso.symm v)
        ((outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
          modelIso).symm e) = 1 := by
  classical
  let idx := outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
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
  have hwinc : eightEightOwnerContains e (modelIso ws) = true := by
    have := (outsideOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges modelIso e (modelIso ws)).mp
      (by simpa [idx, z] using hzw.symm)
    simpa using this
  have hfalse := eightEightOwnerTarget_not_cycleAdj_of_contains
    e v (modelIso ws) htarget hwinc
  have htrue : eightEightCycleAdj v (modelIso ws) = true := by
    simpa using (hcycle (modelIso.symm v) ws).mp hvw
  simp_all

/-- High-level finite semantics of the checked owner instance, before any
DIMACS numbering.  This is the clean handshake between graph transport and
the generator-local literal bookkeeping. -/
structure EightEightLowOwnerFiniteSemantics
    (X : Fin 48 → Fin 48 → Prop) : Prop where
  service_exists : ∀ e : Fin 48, ∀ v : Fin 16,
    eightEightOwnerTargetContains e v = true →
      ∃ f : Fin 48, X e f ∧ eightEightOwnerContains f v = true
  service_unique : ∀ e : Fin 48, ∀ v : Fin 16,
    eightEightOwnerTargetContains e v = true →
      ∀ f g : Fin 48, X e f → eightEightOwnerContains f v = true →
        X e g → eightEightOwnerContains g v = true → f = g
  intersecting_no_common : ∀ e f : Fin 48,
    e ≠ f → eightEightOwnersIntersect e f = true →
      ∀ k : Fin 48, X e k → X f k → False
  no_two_common : ∀ e f : Fin 48, e ≠ f →
    ∀ k l : Fin 48, k ≠ l →
      X e k → X f k → X e l → X f l → False

/-- Convert the generic exact-service/C4 semantic package into the fixed
high-level owner interface.  Only two coordinate rewrites are required:
generator targets must select target value one, and fixed incidence must
agree with the abstract incidence relation.  The stronger zero-common rule
for intersecting owners is supplied separately. -/
theorem EightEightLowOwnerFiniteSemantics.of_clauseSemantics
    {U : Type*}
    (C : SimpleGraph (Fin 48))
    (incident : U → Fin 48 → Prop)
    (target : U → Fin 48 → Nat)
    (coord : U ≃ Fin 16)
    (h : OutsideCClauseSemantics C incident target)
    (htarget : ∀ e : Fin 48, ∀ v : Fin 16,
      eightEightOwnerTargetContains e v = true →
        target (coord.symm v) e = 1)
    (hincident : ∀ e : Fin 48, ∀ v : Fin 16,
      incident (coord.symm v) e ↔ eightEightOwnerContains e v = true)
    (hintersect : ∀ e f : Fin 48,
      e ≠ f → eightEightOwnersIntersect e f = true →
        ∀ k : Fin 48, C.Adj e k → C.Adj f k → False) :
    EightEightLowOwnerFiniteSemantics C.Adj := by
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
    (modelIso : exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph)
    (e f : Fin 48) (hef : e ≠ f)
    (hintersect : eightEightOwnersIntersect e f = true)
    (k : Fin 48)
    (hek : ((G.induce c.suppᶜ).comap
      (outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
        modelIso).symm).Adj e k)
    (hfk : ((G.induce c.suppᶜ).comap
      (outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
        modelIso).symm).Adj f k) : False := by
  let idx := outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  let a := idx.symm e
  let b := idx.symm f
  let x := idx.symm k
  have hab : a ≠ b := by
    intro h
    apply hef
    exact idx.symm.injective (by simpa [a, b] using h)
  obtain ⟨v, hve, hvf⟩ :=
    (eightEightOwnersIntersect_iff_sym2 e f).mp hintersect
  let u : c.supp := modelIso.symm v
  have hpaira := outsidePair_map_modelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges modelIso a
  have hpairb := outsidePair_map_modelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges modelIso b
  have hia : outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
      modelIso a = e := by
    simpa [idx, a] using idx.apply_symm_apply e
  have hib : outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
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

/-- Complete graph-facing finite semantics for the fixed low-`8+8` owner
instance.  All DIMACS numbering is absent: the result speaks only about
the transported exterior adjacency relation on `Fin 48`. -/
theorem lowEightOwnerFiniteSemantics_of_modelIso
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
    (modelIso : exteriorPairGraph G c ≃g eightEightLowExteriorPairGraph)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ eightEightCycleAdj (modelIso x).val (modelIso y).val = true) :
    EightEightLowOwnerFiniteSemantics
      (((G.induce c.suppᶜ).comap
        (outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges
          modelIso).symm).Adj) := by
  let idx := outsideLowEightOwnerIndexEquiv G c hcard hinc hqcard hRedges modelIso
  apply EightEightLowOwnerFiniteSemantics.of_clauseSemantics
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

end

end Erdos85

#print axioms Erdos85.OutsideCClauseSemantics.comap_equiv
#print axioms Erdos85.eightEightOwnerAt_lt_sixteen
#print axioms Erdos85.eightEightOwnerSym2_injective
#print axioms Erdos85.outsidePair_map_modelIso_eq_ownerSym2
#print axioms Erdos85.mem_eightEightOwnerSym2_iff
#print axioms Erdos85.outsideOwnerCoordinates_incident_iff
#print axioms Erdos85.outsideOwnerCoordinates_target_eq_one
#print axioms Erdos85.lowEightExteriorPair_pointwise_model_of_shores
#print axioms Erdos85.outsideCClauseSemantics_ownerCoordinates
#print axioms Erdos85.outsidePair_intersects_no_exterior_common
#print axioms Erdos85.outsideOwnerCoordinates_intersecting_no_common
#print axioms Erdos85.lowEightOwnerFiniteSemantics_of_modelIso
#print axioms Erdos85.adjacent_outsidePair_endpoint_not_adj
