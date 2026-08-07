import Proofs.Erdos85OrderFortyNineGraphPrefixNormalization
import Proofs.Erdos85OrderFortyNineRowSemantics

/-!
# Canonical triple-support systems at order 49

This file composes the graph-facing prefix normalization with the semantic
content of the finite witness tables.  Its output is coordinate-free: after
one further permutation of the nine high labels, the graph's complete family
of three-point high supports is exactly one of the canonical representative
systems used by the certified SAT instances.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

open OrderFortyNineWitnessTable

/-- Equal cardinalities of every fiber are enough to relabel one finite
function as another.  This is the abstract mechanism used below to turn a
support census into a full vertex labeling. -/
noncomputable def equivOfFiberCardEq
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → γ) (g : β → γ)
    (hcard : ∀ c, Fintype.card {a // f a = c} =
      Fintype.card {b // g b = c}) : α ≃ β :=
  Equiv.ofFiberEquiv fun c =>
    (Fintype.equivFinOfCardEq (hcard c)).trans
      (Fintype.equivFinOfCardEq rfl).symm

theorem equivOfFiberCardEq_map
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → γ) (g : β → γ)
    (hcard : ∀ c, Fintype.card {a // f a = c} =
      Fintype.card {b // g b = c}) (a : α) :
    g (equivOfFiberCardEq f g hcard a) = f a :=
  Equiv.ofFiberEquiv_map _ _

/-- The finite support represented by one entry of a canonical mask array. -/
def orderFortyNineMaskSupport (masks : Array Nat) (i : Fin 49) :
    Finset (Fin 9) :=
  Finset.univ.filter fun w =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

/-- Once the graph and a canonical mask array have equally large fibers for
every high support, a full `V ≃ Fin 49` labeling preserving all supports is
automatic.  This isolates the remaining mathematical obligation as a pure
fiber-cardinality census. -/
theorem exists_orderFortyNine_vertexLabeling_of_supportFiberCardEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat)
    (hcard : ∀ S : Finset (Fin 9),
      Fintype.card {x : V // orderFortyNineLabeledHighSupport G e x = S} =
      Fintype.card {i : Fin 49 // orderFortyNineMaskSupport masks i = S}) :
    ∃ E : V ≃ Fin 49, ∀ x,
      orderFortyNineMaskSupport masks (E x) =
        orderFortyNineLabeledHighSupport G e x := by
  let E := equivOfFiberCardEq
    (orderFortyNineLabeledHighSupport G e)
    (orderFortyNineMaskSupport masks) hcard
  exact ⟨E, fun x => equivOfFiberCardEq_map _ _ hcard x⟩

/-- Relabeling the high coordinates acts on every labeled support by the
corresponding `Finset.map`. -/
theorem orderFortyNineLabeledHighSupport_trans
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (σ : Equiv.Perm (Fin 9)) (x : V) :
    orderFortyNineLabeledHighSupport G (e.trans σ) x =
      (orderFortyNineLabeledHighSupport G e x).map σ.toEmbedding := by
  unfold orderFortyNineLabeledHighSupport
  rw [Finset.map_map]
  rfl

/-- In a `C₄`-free graph, a labeled high support of size at least two
determines its vertex uniquely.  This supplies the multiplicity-one part of
the canonical pair/triple profile without any finite enumeration. -/
theorem orderFortyNineLabeledHighSupport_injective_of_two_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    {x y : V}
    (hx : 2 ≤ (orderFortyNineLabeledHighSupport G e x).card)
    (hxy : orderFortyNineLabeledHighSupport G e x =
      orderFortyNineLabeledHighSupport G e y) : x = y := by
  by_contra hne
  have hle := orderFortyNine_card_inter_highSupport_le_one G hfree hne
  have hinter := card_inter_orderFortyNineLabeledHighSupport G e x y
  have hcards := congrArg Finset.card hxy
  rw [hxy, Finset.inter_self] at hinter
  omega

/-- Consequently every support of size at least two has a singleton fiber. -/
theorem orderFortyNine_card_labeledHighSupportFiber_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V)
    (hx : 2 ≤ (orderFortyNineLabeledHighSupport G e x).card) :
    Fintype.card {y : V // orderFortyNineLabeledHighSupport G e y =
      orderFortyNineLabeledHighSupport G e x} = 1 := by
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : V =>
      orderFortyNineLabeledHighSupport G e y =
        orderFortyNineLabeledHighSupport G e x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hy
      exact (orderFortyNineLabeledHighSupport_injective_of_two_le
        G hfree e hx hy.symm).symm
    · rintro rfl
      rfl
  rw [hfilter]
  simp

/-- Vertices carrying one prescribed labeled high support. -/
def orderFortyNineLabeledSupportFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (S : Finset (Fin 9)) : Finset V :=
  Finset.univ.filter fun x => orderFortyNineLabeledHighSupport G e x = S

theorem card_orderFortyNineLabeledSupportFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (S : Finset (Fin 9)) :
    (orderFortyNineLabeledSupportFiber G e S).card =
      Fintype.card {x : V // orderFortyNineLabeledHighSupport G e x = S} := by
  rw [Fintype.card_subtype]
  rfl

/-- Membership in a labeled support is adjacency to the corresponding high
vertex. -/
theorem mem_orderFortyNineLabeledHighSupport_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V) (w : Fin 9) :
    w ∈ orderFortyNineLabeledHighSupport G e x ↔
      G.Adj x (e.symm w).1 := by
  constructor
  · intro hw
    obtain ⟨v, hv, hev⟩ := Finset.mem_map.mp hw
    have hvSupport : v.1 ∈ orderFortyNineHighSupport G x :=
      (mem_finsetInSubtype_iff.mp hv)
    have hvAdj := (Finset.mem_inter.mp hvSupport).1
    have hve : v = e.symm w := by
      apply e.injective
      simpa using hev
    simpa [hve, SimpleGraph.mem_neighborFinset] using hvAdj
  · intro hxw
    apply Finset.mem_map.mpr
    refine ⟨e.symm w, ?_, by simp⟩
    apply mem_finsetInSubtype_iff.mpr
    exact Finset.mem_inter.mpr
      ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxw,
       (e.symm w).2⟩

theorem orderFortyNineLabeledHighSupport_eq_singleton_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V) (w : Fin 9) :
    orderFortyNineLabeledHighSupport G e x = {w} ↔
      G.Adj x (e.symm w).1 ∧ (orderFortyNineHighSupport G x).card = 1 := by
  constructor
  · intro hsupport
    have hw : w ∈ orderFortyNineLabeledHighSupport G e x := by
      rw [hsupport]
      simp
    refine ⟨(mem_orderFortyNineLabeledHighSupport_iff G e x w).mp hw, ?_⟩
    rw [← card_orderFortyNineLabeledHighSupport G e x, hsupport]
    simp
  · rintro ⟨hadj, hcard⟩
    have hw : w ∈ orderFortyNineLabeledHighSupport G e x :=
      (mem_orderFortyNineLabeledHighSupport_iff G e x w).mpr hadj
    have hcard' : (orderFortyNineLabeledHighSupport G e x).card = 1 := by
      rw [card_orderFortyNineLabeledHighSupport, hcard]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard'
    have : w = u := by
      rw [hu] at hw
      simpa using hw
    simpa [this] using hu

/-- In labeled coordinates, singleton-support multiplicity at a high point
equals the number of triple supports through that point. -/
theorem orderFortyNine_card_singletonFiber_eq_tripleIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (w : Fin 9) :
    (orderFortyNineLabeledSupportFiber G e {w}).card =
      (Finset.univ.filter fun x =>
        (orderFortyNineLabeledHighSupport G e x).card = 3 ∧
          w ∈ orderFortyNineLabeledHighSupport G e x).card := by
  let v : V := (e.symm w).1
  have hv : v ∈ orderFortyNineHighVertices G := (e.symm w).2
  have hlocal := orderFortyNine_singletonMultiplicity_eq_tripleMultiplicity
    G hfree hmin hcard hHigh hv
  have hone : orderFortyNineLabeledSupportFiber G e {w} =
      (G.neighborFinset v).filter fun x =>
        (orderFortyNineHighSupport G x).card = 1 := by
    ext x
    simp only [orderFortyNineLabeledSupportFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    rw [orderFortyNineLabeledHighSupport_eq_singleton_iff]
    change (G.Adj x v ∧ _) ↔ (G.Adj v x ∧ _)
    rw [G.adj_comm]
  have hthree : (Finset.univ.filter fun x =>
      (orderFortyNineLabeledHighSupport G e x).card = 3 ∧
        w ∈ orderFortyNineLabeledHighSupport G e x) =
      (G.neighborFinset v).filter fun x =>
        (orderFortyNineHighSupport G x).card = 3 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    rw [card_orderFortyNineLabeledHighSupport,
      mem_orderFortyNineLabeledHighSupport_iff]
    change (_ ∧ G.Adj x v) ↔ (G.Adj v x ∧ _)
    rw [G.adj_comm]
    tauto
  rw [hone, hthree]
  exact hlocal

/-- Every labeled pair of high points lies in a unique size-two or size-three
support block. -/
theorem orderFortyNine_existsUnique_labeled_pairBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    {a b : Fin 9} (hab : a ≠ b) :
    ∃! x : V, ({a, b} : Finset (Fin 9)) ⊆
        orderFortyNineLabeledHighSupport G e x ∧
      ((orderFortyNineLabeledHighSupport G e x).card = 2 ∨
       (orderFortyNineLabeledHighSupport G e x).card = 3) := by
  let va := e.symm a
  let vb := e.symm b
  have hvab : va.1 ≠ vb.1 := by
    intro h
    apply hab
    have : va = vb := Subtype.ext h
    simpa [va, vb] using congrArg e this
  obtain ⟨x, hx, huniq⟩ := orderFortyNine_existsUnique_pairBlock_of_highs
    G hfree hmin hcard va.2 vb.2 hvab
  refine ⟨x, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwa | hwb
      · subst w
        apply (mem_orderFortyNineLabeledHighSupport_iff G e x _).mpr
        simpa [va, G.adj_comm] using hx.1
      · subst w
        apply (mem_orderFortyNineLabeledHighSupport_iff G e x _).mpr
        simpa [vb, G.adj_comm] using hx.2.1
    · simpa [card_orderFortyNineLabeledHighSupport] using hx.2.2.2
  · intro y hy
    apply huniq y
    have haMem := hy.1 (by simp : a ∈ ({a, b} : Finset (Fin 9)))
    have hbMem := hy.1 (by simp : b ∈ ({a, b} : Finset (Fin 9)))
    have hvaAdj : G.Adj va.1 y := by
      simpa [va, G.adj_comm] using
        (mem_orderFortyNineLabeledHighSupport_iff G e y a).mp haMem
    have hvbAdj : G.Adj vb.1 y := by
      simpa [vb, G.adj_comm] using
        (mem_orderFortyNineLabeledHighSupport_iff G e y b).mp hbMem
    refine ⟨hvaAdj, hvbAdj, ?_, ?_⟩
    · exact orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin hcard (Finset.mem_filter.mp va.2).2 hvaAdj
    · rcases hy.2 with h2 | h3
      · left
        simpa [card_orderFortyNineLabeledHighSupport] using h2
      · right
        simpa [card_orderFortyNineLabeledHighSupport] using h3

/-- Exact pair-support multiplicity is one precisely when the pair is not
already covered by a triple support. -/
theorem orderFortyNine_card_pairFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    {a b : Fin 9} (hab : a ≠ b) :
    (orderFortyNineLabeledSupportFiber G e {a, b}).card =
      if ∃ x : V,
          (orderFortyNineLabeledHighSupport G e x).card = 3 ∧
          ({a, b} : Finset (Fin 9)) ⊆
            orderFortyNineLabeledHighSupport G e x
        then 0 else 1 := by
  obtain ⟨x, hx, huniq⟩ := orderFortyNine_existsUnique_labeled_pairBlock
    G hfree hmin hcard e hab
  by_cases htriple : ∃ z : V,
      (orderFortyNineLabeledHighSupport G e z).card = 3 ∧
      ({a, b} : Finset (Fin 9)) ⊆
        orderFortyNineLabeledHighSupport G e z
  · rw [if_pos htriple, Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨y, hy⟩ := hnonempty
    have hyEq : orderFortyNineLabeledHighSupport G e y = {a, b} :=
      (Finset.mem_filter.mp hy).2
    have hyCard : (orderFortyNineLabeledHighSupport G e y).card = 2 := by
      rw [hyEq]
      simp [hab]
    have hyQual : ({a, b} : Finset (Fin 9)) ⊆
          orderFortyNineLabeledHighSupport G e y ∧
        ((orderFortyNineLabeledHighSupport G e y).card = 2 ∨
         (orderFortyNineLabeledHighSupport G e y).card = 3) := by
      refine ⟨by rw [hyEq], Or.inl hyCard⟩
    obtain ⟨z, hzCard, hzSub⟩ := htriple
    have hzQual : ({a, b} : Finset (Fin 9)) ⊆
          orderFortyNineLabeledHighSupport G e z ∧
        ((orderFortyNineLabeledHighSupport G e z).card = 2 ∨
         (orderFortyNineLabeledHighSupport G e z).card = 3) :=
      ⟨hzSub, Or.inr hzCard⟩
    have hyx := huniq y hyQual
    have hzx := huniq z hzQual
    have hyz : y = z := hyx.trans hzx.symm
    have hcards := congrArg
      (fun u => (orderFortyNineLabeledHighSupport G e u).card) hyz
    omega
  · rw [if_neg htriple]
    have hxCard : (orderFortyNineLabeledHighSupport G e x).card = 2 := by
      rcases hx.2 with h2 | h3
      · exact h2
      · exact False.elim (htriple ⟨x, h3, hx.1⟩)
    have hpairCard : ({a, b} : Finset (Fin 9)).card = 2 := by simp [hab]
    have hxEq : orderFortyNineLabeledHighSupport G e x = {a, b} :=
      (Finset.eq_of_subset_of_card_le hx.1 (by omega)).symm
    have hone := orderFortyNine_card_labeledHighSupportFiber_eq_one
      G hfree e x (by omega)
    rw [← card_orderFortyNineLabeledSupportFiber G e
      (orderFortyNineLabeledHighSupport G e x)] at hone
    simpa [hxEq] using hone

theorem orderFortyNineLabeledHighSupport_eq_empty_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (x : V) :
    orderFortyNineLabeledHighSupport G e x = ∅ ↔
      (orderFortyNineHighSupport G x).card = 0 := by
  rw [← card_orderFortyNineLabeledHighSupport G e x]
  exact Finset.card_eq_zero.symm

/-- The empty labeled-support fiber consists of all high vertices together
with the low vertices counted by incidence class zero. -/
theorem orderFortyNine_card_emptySupportFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9) :
    (orderFortyNineLabeledSupportFiber G e ∅).card =
      (orderFortyNineHighVertices G).card +
        orderFortyNineHighIncidenceCount G 0 := by
  let H := orderFortyNineHighVertices G
  let L0 := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 0
  have hfiber : orderFortyNineLabeledSupportFiber G e ∅ = H ∪ L0 := by
    ext x
    simp only [orderFortyNineLabeledSupportFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union]
    rw [orderFortyNineLabeledHighSupport_eq_empty_iff]
    constructor
    · intro hx0
      by_cases hxH : x ∈ H
      · exact Or.inl hxH
      · exact Or.inr (by
          refine Finset.mem_filter.mpr ⟨?_, hx0⟩
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxH⟩)
    · rintro (hxH | hxL0)
      · exact orderFortyNine_highNeighborCount_eq_zero_of_high
          G hfree hmin hcard hxH
      · exact (Finset.mem_filter.mp hxL0).2
  have hdisjoint : Disjoint H L0 := by
    rw [Finset.disjoint_left]
    intro x hxH hxL0
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxL0).1).2 hxH
  rw [hfiber, Finset.card_union_of_disjoint hdisjoint]
  rfl

/-- The graph's three-point high supports, in a chosen labeling, are exactly
the triples of `rep` (viewed as ordinary finite sets of natural numbers). -/
def OrderFortyNineCanonicalTripleSystemSpec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System) : Prop :=
  let X := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 3
  (∀ x ∈ X, ∃ T ∈ h9SystemTriples rep,
    (orderFortyNineLabeledHighSupport G e x).image Fin.val = T.toFinset) ∧
  (∀ T ∈ h9SystemTriples rep, ∃ x ∈ X,
    (orderFortyNineLabeledHighSupport G e x).image Fin.val = T.toFinset)

/-- The set of natural-number triples encoded by the graph's size-three
supports. -/
def orderFortyNineLabeledTripleSupportSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9) :
    Finset (Finset Nat) :=
  ((orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 3).image fun x =>
      (orderFortyNineLabeledHighSupport G e x).image Fin.val

/-- The underlying set of triples of a canonical representative. -/
def orderFortyNineRepresentativeTripleSet
    (rep : OrderFortyNineH9System) : Finset (Finset Nat) :=
  (h9SystemTriples rep).toFinset.image List.toFinset

/-- A canonical-system specification is equivalently equality of the two
finite triple-support sets. -/
theorem OrderFortyNineCanonicalTripleSystemSpec.tripleSupportSet_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System)
    (hcanon : OrderFortyNineCanonicalTripleSystemSpec G e rep) :
    orderFortyNineLabeledTripleSupportSet G e =
      orderFortyNineRepresentativeTripleSet rep := by
  ext S
  constructor
  · intro hS
    obtain ⟨x, hx, hxS⟩ := Finset.mem_image.mp hS
    obtain ⟨T, hT, hEq⟩ := hcanon.1 x hx
    apply Finset.mem_image.mpr
    refine ⟨T, List.mem_toFinset.mpr hT, ?_⟩
    exact hEq.symm.trans hxS
  · intro hS
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hS
    obtain ⟨x, hx, hEq⟩ := hcanon.2 T (List.mem_toFinset.mp hT)
    apply Finset.mem_image.mpr
    refine ⟨x, hx, ?_⟩
    exact hEq.trans hTS

/-- A semantic table witness for a list enumerating all triple-support
vertices produces a canonical graph labeling. -/
theorem exists_canonicalTripleSystem_of_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {reps : Array OrderFortyNineH9System} {row : Row}
    (hspec : RowSemanticSpec reps row)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (xs : List V)
    (hX : (orderFortyNineLowVertices G).filter (fun x =>
      (orderFortyNineHighSupport G x).card = 3) = xs.toFinset)
    (hrow : row.1 = xs.map fun x =>
      tripleDigits (orderFortyNineLabeledHighSupport G e x)) :
    ∃ rep, ∃ e' : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      reps[row.2.1]? = some rep ∧
      OrderFortyNineCanonicalTripleSystemSpec G e' rep := by
  let supports := xs.map fun x => orderFortyNineLabeledHighSupport G e x
  have hrow' : row.1 = supports.map tripleDigits := by
    dsimp only [supports]
    rw [List.map_map]
    simpa only [Function.comp_def] using hrow
  obtain ⟨rep, σ, hrep, hforward, hback⟩ :=
    OrderFortyNineWitnessTable.RowSemanticSpec.transport_supports
      hspec supports hrow'
  refine ⟨rep, e.trans σ, hrep, ?_, ?_⟩
  · intro x hx
    have hxin : x ∈ xs := by
      rw [hX] at hx
      simpa using hx
    have hsupport : orderFortyNineLabeledHighSupport G e x ∈ supports :=
      List.mem_map.mpr ⟨x, hxin, rfl⟩
    obtain ⟨T, hT, hEq⟩ := hforward _ hsupport
    refine ⟨T, hT, ?_⟩
    rw [orderFortyNineLabeledHighSupport_trans]
    exact hEq
  · intro T hT
    obtain ⟨S, hS, hEq⟩ := hback T hT
    obtain ⟨x, hx, hxS⟩ := List.mem_map.mp hS
    refine ⟨x, ?_, ?_⟩
    · rw [hX]
      simpa using hx
    · subst S
      rw [orderFortyNineLabeledHighSupport_trans]
      exact hEq

/-- Every graph in the two-triple, nine-high stratum has a canonical
representative support system. -/
theorem orderFortyNine_exists_canonicalT2System
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ row ∈ tableT2, ∃ rep,
      orderFortyNineH9T2Systems[row.2.1]? = some rep ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        OrderFortyNineCanonicalTripleSystemSpec G e rep := by
  obtain ⟨x, y, hX, hxy, e, row, hrowmem, hrow⟩ :=
    orderFortyNine_exists_tableT2_row_of_tripleSupportCount_two
      G hfree hHigh hcount
  have hXlist : (orderFortyNineLowVertices G).filter (fun z =>
      (orderFortyNineHighSupport G z).card = 3) = [x, y].toFinset := by
    simpa [hxy] using hX
  obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
    G (exists_rep_rowPerm_systemSpec_of_mem_tableT2 hrowmem) e [x, y]
      hXlist (by simpa using hrow)
  exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩

/-- Every graph in the three-triple, nine-high stratum has a canonical
representative support system. -/
theorem orderFortyNine_exists_canonicalT3System
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ row ∈ tableT3, ∃ rep,
      orderFortyNineH9T3Systems[row.2.1]? = some rep ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        OrderFortyNineCanonicalTripleSystemSpec G e rep := by
  obtain ⟨x, y, z, hX, e, row, hrowmem, hrow⟩ :=
    orderFortyNine_exists_tableT3_row_of_tripleSupportCount_three
      G hfree hHigh hcount
  have hXlist : (orderFortyNineLowVertices G).filter (fun u =>
      (orderFortyNineHighSupport G u).card = 3) = [x, y, z].toFinset := by
    simpa using hX
  obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
    G (exists_rep_rowPerm_systemSpec_of_mem_tableT3 hrowmem) e [x, y, z]
      hXlist (by simpa using hrow)
  exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩

/-- Every graph in the four-triple, nine-high stratum has a canonical
representative support system.  The residual ordering chosen by L1 is
irrelevant because the semantic specification is setwise. -/
theorem orderFortyNine_exists_canonicalT4System
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ row ∈ tableT4, ∃ rep,
      orderFortyNineH9T4Systems[row.2.1]? = some rep ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        OrderFortyNineCanonicalTripleSystemSpec G e rep := by
  obtain ⟨x, y, z, w, hX, e, row, hrowmem, hrow | hrow⟩ :=
    orderFortyNine_exists_tableT4_row_of_tripleSupportCount_four
      G hfree hHigh hcount
  · have hXlist : (orderFortyNineLowVertices G).filter (fun u =>
        (orderFortyNineHighSupport G u).card = 3) = [x, y, z, w].toFinset := by
      simpa using hX
    obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
      G (exists_rep_rowPerm_systemSpec_of_mem_tableT4 hrowmem) e [x, y, z, w]
        hXlist (by simpa using hrow)
    exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩
  · have hXlist : (orderFortyNineLowVertices G).filter (fun u =>
        (orderFortyNineHighSupport G u).card = 3) = [x, y, w, z].toFinset := by
      rw [hX]
      ext u
      simp only [List.mem_toFinset, List.mem_cons,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
      G (exists_rep_rowPerm_systemSpec_of_mem_tableT4 hrowmem) e [x, y, w, z]
        hXlist (by simpa using hrow)
    exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩

end

end Erdos85
