import Proofs.Erdos85OrderFortyNineFullCanonicalLabeling
import Proofs.Erdos85OrderFortyNineBooleanTerminal
import Proofs.Erdos85Relabel

/-!
# From exact canonical labels to the order-49 Boolean terminal

The aligned key remembers the literal label of every high vertex.  This file
extracts the two pointwise facts needed for graph relabeling: exact placement
of high vertices and preservation of every high-support bit.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem orderFortyNine_alignedLabeling_high_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (w : Fin 9) : E (e.symm w).1 = ⟨w.val, by omega⟩ := by
  have hfirst := congrArg Prod.fst (hE (e.symm w).1)
  have hsome :
      (if h : (E (e.symm w).1).val < 9
        then some (⟨(E (e.symm w).1).val, h⟩ : Fin 9)
        else none) = some w := by
    simpa [orderFortyNineMaskAlignedVertexKey,
      orderFortyNineGraphAlignedVertexKey] using hfirst
  by_cases hlt : (E (e.symm w).1).val < 9
  · simp [hlt] at hsome
    apply Fin.ext
    simpa using congrArg Fin.val hsome
  · simp [hlt] at hsome

theorem orderFortyNine_alignedLabeling_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (x : V) :
    orderFortyNineMaskSupport masks (E x) =
      orderFortyNineLabeledHighSupport G e x := by
  simpa [orderFortyNineMaskAlignedVertexKey,
    orderFortyNineGraphAlignedVertexKey] using congrArg Prod.snd (hE x)

theorem orderFortyNine_alignedLabeling_high_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (x : V) :
    (E x).val < 9 ↔ x ∈ orderFortyNineHighVertices G := by
  have hfirst := congrArg Prod.fst (hE x)
  by_cases hi : (E x).val < 9 <;>
    by_cases hx : x ∈ orderFortyNineHighVertices G <;>
    simp [orderFortyNineMaskAlignedVertexKey,
      orderFortyNineGraphAlignedVertexKey, hi, hx] at hfirst ⊢

/-- Relabel `G` by an exact canonical vertex equivalence. -/
def orderFortyNineRelabeledGraph
    {V : Type*} (G : SimpleGraph V) (E : V ≃ Fin 49) :
    SimpleGraph (Fin 49) :=
  SimpleGraph.comap E.symm G

instance orderFortyNineRelabeledGraph_decidableAdj
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : V ≃ Fin 49) : DecidableRel (orderFortyNineRelabeledGraph G E).Adj :=
  fun i j => inferInstanceAs (Decidable (G.Adj (E.symm i) (E.symm j)))

theorem orderFortyNineRelabeledGraph_adj
    {V : Type*} (G : SimpleGraph V) (E : V ≃ Fin 49)
    (i j : Fin 49) :
    (orderFortyNineRelabeledGraph G E).Adj i j ↔
      G.Adj (E.symm i) (E.symm j) := by
  rfl

theorem orderFortyNineRelabeledGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : V ≃ Fin 49) (i : Fin 49) :
    (orderFortyNineRelabeledGraph G E).degree i = G.degree (E.symm i) := by
  classical
  exact (SimpleGraph.Iso.comap E.symm G).degree_eq i |>.symm

theorem orderFortyNineRelabeledGraph_not_containsC4
    {V : Type*} (G : SimpleGraph V) (E : V ≃ Fin 49)
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 (Fin 49) (orderFortyNineRelabeledGraph G E) := by
  exact fun h => hfree ((containsC4_iff_of_iso
    (SimpleGraph.Iso.comap E.symm G)).mp h)

theorem orderFortyNineRelabeledGraph_degree_seven_or_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (i : Fin 49) :
    (orderFortyNineRelabeledGraph G E).degree i =
      if i.val < 9 then 8 else 7 := by
  rw [orderFortyNineRelabeledGraph_degree]
  have hhigh := orderFortyNine_alignedLabeling_high_iff
    G e masks E hE (E.symm i)
  simp only [E.apply_symm_apply] at hhigh
  by_cases hi : i.val < 9
  · rw [if_pos hi]
    exact (Finset.mem_filter.mp (hhigh.mp hi)).2
  · rw [if_neg hi]
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard (E.symm i) with h7 | h8
    · exact h7
    · exfalso
      apply hi
      apply hhigh.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h8⟩

/-- Exact high-label alignment turns support preservation into the fixed-edge
condition expected by the Boolean terminal. -/
theorem orderFortyNineRelabeledGraph_highAdj_eq_supportBit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (i : Fin 49) (w : Fin 9) :
    decide ((orderFortyNineRelabeledGraph G E).Adj
      i ⟨w.val, by omega⟩) =
      (orderFortyNineSupportMask masks i).getLsbD w.val := by
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have hhigh : E (e.symm w).1 = wi :=
    orderFortyNine_alignedLabeling_high_image G e masks E hE w
  have hhighSymm : E.symm wi = (e.symm w).1 := by
    apply E.injective
    simp [hhigh]
  have hs := orderFortyNine_alignedLabeling_support
    G e masks E hE (E.symm i)
  have hs' : orderFortyNineMaskSupport masks i =
      orderFortyNineLabeledHighSupport G e (E.symm i) := by
    simpa using hs
  have hadjmem : G.Adj (E.symm i) (e.symm w).1 ↔
      w ∈ orderFortyNineMaskSupport masks i := by
    rw [hs']
    exact (mem_orderFortyNineLabeledHighSupport_iff
      G e (E.symm i) w).symm
  rw [Bool.eq_iff_iff]
  simpa [wi, orderFortyNineRelabeledGraph_adj,
    hhighSymm, orderFortyNineMaskSupport] using hadjmem

theorem orderFortyNineRelabeledGraph_low_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x)
    (i : Fin 49) (hi : 9 ≤ i.val) (w : Fin 9) :
    ((orderFortyNineRelabeledGraph G E).neighborFinset i ∩
      orderFortyNineSupportFiber masks w).card = 1 := by
  let H := orderFortyNineRelabeledGraph G E
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have hiNot : ¬ i.val < 9 := by omega
  have hy : G.degree (E.symm i) = 7 := by
    have hd := orderFortyNineRelabeledGraph_degree_seven_or_eight
      G hfree hmin hcard e masks E hE i
    rw [orderFortyNineRelabeledGraph_degree, if_neg hiNot] at hd
    exact hd
  obtain ⟨x, hx, huniq⟩ :=
    orderFortyNine_low_neighborhood_partitions_highs
      G hfree hmin hcard hy (e.symm w).2
  have hhigh : E (e.symm w).1 = wi :=
    orderFortyNine_alignedLabeling_high_image G e masks E hE w
  have hhighSymm : E.symm wi = (e.symm w).1 := by
    apply E.injective
    simp [hhigh]
  have hset : H.neighborFinset i ∩ orderFortyNineSupportFiber masks w =
      {E x} := by
    ext k
    constructor
    · intro hk
      have hkN : H.Adj i k := by
        simpa [H, SimpleGraph.mem_neighborFinset] using
          (Finset.mem_inter.mp hk).1
      have hkBit :
          (orderFortyNineSupportMask masks k).getLsbD w.val = true := by
        simpa [orderFortyNineSupportFiber] using
          (Finset.mem_inter.mp hk).2
      have hkHighBool := orderFortyNineRelabeledGraph_highAdj_eq_supportBit
        G e masks E hE k w
      have hkHighH : H.Adj k wi := by
        apply of_decide_eq_true
        rw [hkHighBool]
        exact hkBit
      have hkOrigN : E.symm k ∈ G.neighborFinset (E.symm i) := by
        simpa [H, orderFortyNineRelabeledGraph,
          SimpleGraph.mem_neighborFinset] using hkN
      have hkOrigHigh : G.Adj (E.symm k) (e.symm w).1 := by
        simpa [H, orderFortyNineRelabeledGraph, wi, hhighSymm] using hkHighH
      have hek : E.symm k = x := huniq (E.symm k) ⟨hkOrigN, hkOrigHigh⟩
      have : k = E x := by
        apply E.symm.injective
        simpa using hek
      simpa [this]
    · intro hk
      have hkEq : k = E x := by simpa using hk
      subst k
      apply Finset.mem_inter.mpr
      constructor
      · have : H.Adj i (E x) := by
          simpa [H, orderFortyNineRelabeledGraph,
            SimpleGraph.mem_neighborFinset] using hx.1
        simpa [SimpleGraph.mem_neighborFinset] using this
      · have hAdjH : H.Adj (E x) wi := by
          simpa [H, orderFortyNineRelabeledGraph, wi, hhighSymm] using hx.2
        have hbit := orderFortyNineRelabeledGraph_highAdj_eq_supportBit
          G e masks E hE (E x) w
        have hbitTrue :
            (orderFortyNineSupportMask masks (E x)).getLsbD w.val = true := by
          rw [← hbit]
          exact decide_eq_true hAdjH
        simpa [orderFortyNineSupportFiber] using hbitTrue
  rw [hset]
  simp

/-- The complete graph-facing faithfulness bridge: an aligned canonical
labeling produces a satisfying assignment for the exact Boolean terminal. -/
theorem orderFortyNineBooleanConstraints_of_alignedLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (masks : Array Nat) (hsize : masks.size = 49)
    (E : V ≃ Fin 49)
    (hE : ∀ x,
      orderFortyNineMaskAlignedVertexKey masks (E x) =
        orderFortyNineGraphAlignedVertexKey G e x) :
    orderFortyNineBooleanConstraints 9 masks
      (orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E)) := by
  apply orderFortyNineGraphEdges_satisfy
    (orderFortyNineRelabeledGraph G E) 9 masks hsize (by omega)
  · exact orderFortyNineRelabeledGraph_degree_seven_or_eight
      G hfree hmin hcard e masks E hE
  · exact orderFortyNineRelabeledGraph_not_containsC4 G E hfree
  · intro i w _hw
    exact orderFortyNineRelabeledGraph_highAdj_eq_supportBit
      G e masks E hE i w
  · intro i hi w _hw
    exact orderFortyNineRelabeledGraph_low_partition
      G hfree hmin hcard e masks E hE i hi w

theorem orderFortyNine_exists_booleanTerminal_t2
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ rep ∈ orderFortyNineH9T2Systems, ∃ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 9
        (orderFortyNineH9ProfileMasks rep) edges := by
  obtain ⟨rep, hrep, e, E, hE⟩ :=
    orderFortyNine_exists_alignedCanonicalT2Labeling
      G hfree hmin hcard hHigh hcount
  refine ⟨rep, hrep,
    orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E), ?_⟩
  exact orderFortyNineBooleanConstraints_of_alignedLabeling
    G hfree hmin hcard e (orderFortyNineH9ProfileMasks rep)
      (orderFortyNineH9T2_profileMasks_size rep hrep) E hE

theorem orderFortyNine_exists_booleanTerminal_t3
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ rep ∈ orderFortyNineH9T3Systems, ∃ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 9
        (orderFortyNineH9ProfileMasks rep) edges := by
  obtain ⟨rep, hrep, e, E, hE⟩ :=
    orderFortyNine_exists_alignedCanonicalT3Labeling
      G hfree hmin hcard hHigh hcount
  refine ⟨rep, hrep,
    orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E), ?_⟩
  exact orderFortyNineBooleanConstraints_of_alignedLabeling
    G hfree hmin hcard e (orderFortyNineH9ProfileMasks rep)
      (orderFortyNineH9T3_profileMasks_size rep hrep) E hE

theorem orderFortyNine_exists_booleanTerminal_t4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ rep ∈ orderFortyNineH9T4Systems, ∃ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 9
        (orderFortyNineH9ProfileMasks rep) edges := by
  obtain ⟨rep, hrep, e, E, hE⟩ :=
    orderFortyNine_exists_alignedCanonicalT4Labeling
      G hfree hmin hcard hHigh hcount
  refine ⟨rep, hrep,
    orderFortyNineGraphEdges (orderFortyNineRelabeledGraph G E), ?_⟩
  exact orderFortyNineBooleanConstraints_of_alignedLabeling
    G hfree hmin hcard e (orderFortyNineH9ProfileMasks rep)
      (orderFortyNineH9T4_profileMasks_size rep hrep) E hE

end

end Erdos85
