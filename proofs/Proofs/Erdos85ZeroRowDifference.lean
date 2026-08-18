import Proofs.Erdos85BinaryCycleIntertwiner
import Proofs.Erdos85DifferencePacking

/-!
# Orientation-free zero-row difference sets

The support of row zero is a canonical connection set for either cyclic
orientation.  For a circulant block, transposition negates this support; for
a reverse-circulant block, transposition preserves it.  Ordered differences
therefore agree in both cases.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The `1`-support in row zero of a binary cyclic block. -/
def zeroRowSupport {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ) : Finset (ZMod r) :=
  Finset.univ.filter (fun z ↦ B 0 z = 1)

/-- The `1`-support in column zero, equivalently row zero after transposing
the block. -/
def zeroColumnSupport {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ) : Finset (ZMod r) :=
  Finset.univ.filter (fun z ↦ B z 0 = 1)

theorem mem_zeroRowSupport_iff
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ) (z : ZMod r) :
    z ∈ zeroRowSupport B ↔ B 0 z = 1 := by
  simp [zeroRowSupport]

/-- A translation-invariant binary block is characterized by its zero row. -/
theorem translationInvariant_one_iff_sub_mem_zeroRowSupport
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y + 1) = B x y)
    (x y : ZMod r) :
    B x y = 1 ↔ y - x ∈ zeroRowSupport B := by
  rw [mem_zeroRowSupport_iff]
  have heq : B x y = B 0 (y - x) :=
    translationInvariant_eq_of_sub_eq B hB (by ring)
  rw [heq]

/-- A reverse-translation-invariant binary block is likewise characterized
by its zero row, now through the coordinate sum. -/
theorem reverseInvariant_one_iff_add_mem_zeroRowSupport
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y - 1) = B x y)
    (x y : ZMod r) :
    B x y = 1 ↔ y + x ∈ zeroRowSupport B := by
  rw [mem_zeroRowSupport_iff]
  have heq : B x y = B 0 (y + x) :=
    reverseTranslationInvariant_eq_of_add_eq B hB (by ring)
  rw [heq]

/-- Reflecting the target of a reverse block produces the standard
circulant connection formula, with the reflected zero-row support. -/
theorem reverseInvariant_reflectedTarget_one_iff_sub_mem_negZeroRowSupport
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y - 1) = B x y)
    (x y : ZMod r) :
    B x (-y) = 1 ↔ y - x ∈ negFinset (zeroRowSupport B) := by
  rw [mem_negFinset_iff]
  have h := reverseInvariant_one_iff_add_mem_zeroRowSupport B hB x (-y)
  convert h using 1 <;> ring

theorem zeroColumnSupport_eq_neg_zeroRowSupport_of_translationInvariant
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y + 1) = B x y) :
    zeroColumnSupport B = negFinset (zeroRowSupport B) := by
  ext z
  have heq : B z 0 = B 0 (-z) :=
    translationInvariant_eq_of_sub_eq B hB (by ring)
  simp only [zeroColumnSupport, zeroRowSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_negFinset_iff]
  rw [heq]

theorem zeroColumnSupport_eq_zeroRowSupport_of_reverseInvariant
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hB : ∀ x y, B (x + 1) (y - 1) = B x y) :
    zeroColumnSupport B = zeroRowSupport B := by
  ext z
  have heq : B z 0 = B 0 z :=
    reverseTranslationInvariant_eq_of_add_eq B hB (by ring)
  simp only [zeroColumnSupport, zeroRowSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [heq]

/-- Transposition preserves the ordered-difference set of the canonical
zero-row support, without choosing which cyclic orientation the block has. -/
theorem orderedDifferenceSet_zeroColumn_eq_zeroRow_of_orientation
    {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) ℤ)
    (hOrient :
      (∀ x y, B (x + 1) (y + 1) = B x y) ∨
      (∀ x y, B (x + 1) (y - 1) = B x y)) :
    orderedDifferenceSet (zeroColumnSupport B) =
      orderedDifferenceSet (zeroRowSupport B) := by
  rcases hOrient with htrans | hreverse
  · rw [zeroColumnSupport_eq_neg_zeroRowSupport_of_translationInvariant B htrans,
      orderedDifferenceSet_negFinset]
  · rw [zeroColumnSupport_eq_zeroRowSupport_of_reverseInvariant B hreverse]

/-- The canonical zero-row support is Sidon in either cyclic orientation. -/
theorem isOrderedSidon_zeroRowSupport_of_c4Free_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u v : ZMod r → V) (hu : Function.Injective u)
    (hv : Function.Injective v)
    (hOrient :
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y + 1)) =
        G.adjMatrix ℤ (u x) (v y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y - 1)) =
        G.adjMatrix ℤ (u x) (v y))) :
    IsOrderedSidon (zeroRowSupport
      (fun x y ↦ G.adjMatrix ℤ (u x) (v y))) := by
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (v y)
  rcases hOrient with htrans | hreverse
  · apply isOrderedSidon_of_c4Free_circulantBlock
      G hfree u v hu hv (zeroRowSupport B)
    intro x z
    have h := translationInvariant_one_iff_sub_mem_zeroRowSupport
      B (by simpa only [B] using htrans) x z
    rw [← h]
    simp [B, SimpleGraph.adjMatrix_apply]
  · have hs : IsOrderedSidon (negFinset (zeroRowSupport B)) := by
      apply isOrderedSidon_of_c4Free_circulantBlock
        G hfree u (fun z ↦ v (-z)) hu (hv.comp neg_injective)
        (negFinset (zeroRowSupport B))
      intro x z
      have h := reverseInvariant_reflectedTarget_one_iff_sub_mem_negZeroRowSupport
        B (by simpa only [B] using hreverse) x z
      rw [← h]
      simp [B, SimpleGraph.adjMatrix_apply]
    exact (isOrderedSidon_negFinset_iff (zeroRowSupport B)).mp hs

/-- The forbidden step `1` is absent from the canonical zero-row difference
set in either orientation. -/
theorem one_not_mem_orderedDifferenceSet_zeroRowSupport_of_secondOrder_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) (hr3 : 3 ≤ r)
    (u v : ZMod r → V) (hu : Function.Injective u)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hOrient :
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y + 1)) =
        G.adjMatrix ℤ (u x) (v y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y - 1)) =
        G.adjMatrix ℤ (u x) (v y))) :
    (1 : ZMod r) ∉ orderedDifferenceSet
      (zeroRowSupport (fun x y ↦ G.adjMatrix ℤ (u x) (v y))) := by
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (v y)
  rcases hOrient with htrans | hreverse
  · apply one_not_mem_orderedDifferenceSet_of_secondOrder_cycleBlock
      G hfree hd heven hmin hcard hr3 u v hu huD (zeroRowSupport B)
    intro x z
    have h := translationInvariant_one_iff_sub_mem_zeroRowSupport
      B (by simpa only [B] using htrans) x z
    rw [← h]
    simp [B, SimpleGraph.adjMatrix_apply]
  · have hnot : (1 : ZMod r) ∉
        orderedDifferenceSet (negFinset (zeroRowSupport B)) := by
      apply one_not_mem_orderedDifferenceSet_of_secondOrder_cycleBlock
        G hfree hd heven hmin hcard hr3 u (fun z ↦ v (-z)) hu huD
          (negFinset (zeroRowSupport B))
      intro x z
      have h := reverseInvariant_reflectedTarget_one_iff_sub_mem_negZeroRowSupport
        B (by simpa only [B] using hreverse) x z
      rw [← h]
      simp [B, SimpleGraph.adjMatrix_apply]
    simpa only [orderedDifferenceSet_negFinset] using hnot

/-- Distinct target components have disjoint canonical zero-row difference
sets, even when their block orientations differ. -/
theorem orderedDifferenceSet_zeroRowSupport_disjoint_of_c4Free_orientations
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u v w : ZMod r → V) (hu : Function.Injective u)
    (hsep : ∀ x y, v x ≠ w y)
    (hvOrient :
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y + 1)) =
        G.adjMatrix ℤ (u x) (v y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (v (y - 1)) =
        G.adjMatrix ℤ (u x) (v y)))
    (hwOrient :
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (w (y + 1)) =
        G.adjMatrix ℤ (u x) (w y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (w (y - 1)) =
        G.adjMatrix ℤ (u x) (w y))) :
    Disjoint
      (orderedDifferenceSet (zeroRowSupport
        (fun x y ↦ G.adjMatrix ℤ (u x) (v y))))
      (orderedDifferenceSet (zeroRowSupport
        (fun x y ↦ G.adjMatrix ℤ (u x) (w y)))) := by
  let Bv : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (v y)
  let Bw : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (w y)
  have hvTrans (h : ∀ x y, Bv (x + 1) (y + 1) = Bv x y) :
      ∀ x z, G.Adj (u x) (v z) ↔ z - x ∈ zeroRowSupport Bv := by
    intro x z
    rw [← translationInvariant_one_iff_sub_mem_zeroRowSupport Bv h]
    simp [Bv, SimpleGraph.adjMatrix_apply]
  have hwTrans (h : ∀ x y, Bw (x + 1) (y + 1) = Bw x y) :
      ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ zeroRowSupport Bw := by
    intro x z
    rw [← translationInvariant_one_iff_sub_mem_zeroRowSupport Bw h]
    simp [Bw, SimpleGraph.adjMatrix_apply]
  have hvRev (h : ∀ x y, Bv (x + 1) (y - 1) = Bv x y) :
      ∀ x z, G.Adj (u x) (v (-z)) ↔
        z - x ∈ negFinset (zeroRowSupport Bv) := by
    intro x z
    rw [← reverseInvariant_reflectedTarget_one_iff_sub_mem_negZeroRowSupport Bv h]
    simp [Bv, SimpleGraph.adjMatrix_apply]
  have hwRev (h : ∀ x y, Bw (x + 1) (y - 1) = Bw x y) :
      ∀ x z, G.Adj (u x) (w (-z)) ↔
        z - x ∈ negFinset (zeroRowSupport Bw) := by
    intro x z
    rw [← reverseInvariant_reflectedTarget_one_iff_sub_mem_negZeroRowSupport Bw h]
    simp [Bw, SimpleGraph.adjMatrix_apply]
  rcases hvOrient with hvT | hvR
  · rcases hwOrient with hwT | hwR
    · exact orderedDifferenceSet_disjoint_of_c4Free_two_circulantBlocks
        G hfree u v w hu hsep (zeroRowSupport Bv) (zeroRowSupport Bw)
          (hvTrans (by simpa only [Bv] using hvT))
          (hwTrans (by simpa only [Bw] using hwT))
    · have h := orderedDifferenceSet_disjoint_of_c4Free_two_circulantBlocks
        G hfree u v (fun z ↦ w (-z)) hu (fun x y ↦ hsep x (-y))
          (zeroRowSupport Bv) (negFinset (zeroRowSupport Bw))
          (hvTrans (by simpa only [Bv] using hvT))
          (hwRev (by simpa only [Bw] using hwR))
      simpa only [orderedDifferenceSet_negFinset] using h
  · rcases hwOrient with hwT | hwR
    · have h := orderedDifferenceSet_disjoint_of_c4Free_two_circulantBlocks
        G hfree u (fun z ↦ v (-z)) w hu (fun x y ↦ hsep (-x) y)
          (negFinset (zeroRowSupport Bv)) (zeroRowSupport Bw)
          (hvRev (by simpa only [Bv] using hvR))
          (hwTrans (by simpa only [Bw] using hwT))
      simpa only [orderedDifferenceSet_negFinset] using h
    · have h := orderedDifferenceSet_disjoint_of_c4Free_two_circulantBlocks
        G hfree u (fun z ↦ v (-z)) (fun z ↦ w (-z)) hu
          (fun x y ↦ hsep (-x) (-y))
          (negFinset (zeroRowSupport Bv)) (negFinset (zeroRowSupport Bw))
          (hvRev (by simpa only [Bv] using hvR))
          (hwRev (by simpa only [Bw] using hwR))
      simpa only [orderedDifferenceSet_negFinset] using h

/-- Canonical zero-row support of a graph adjacency block. -/
def graphCycleBlockZeroSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : ZMod r → V) : Finset (ZMod r) :=
  zeroRowSupport (fun x y ↦ G.adjMatrix ℤ (u x) (v y))

/-- For two parametrized equal odd defect cycles, the ordered-difference set
of the canonical graph block is symmetric under transposing the source and
target components.  No global choice between circulant and reverse-circulant
orientations is required. -/
theorem orderedDifferenceSet_graphCycleBlockZeroSupport_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) (hr : Odd r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u v : ZMod r → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hu : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hv : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)}) :
    orderedDifferenceSet (graphCycleBlockZeroSupport G u v) =
      orderedDifferenceSet (graphCycleBlockZeroSupport G v u) := by
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (v y)
  have hOrient := graph_equalOddCycleBlock_orientation
    hr3 hr G D u v huinj hvinj hcomm hu hv
  have hzeroCol : zeroColumnSupport B = graphCycleBlockZeroSupport G v u := by
    ext z
    simp only [zeroColumnSupport, graphCycleBlockZeroSupport, zeroRowSupport,
      Finset.mem_filter, Finset.mem_univ, true_and, B]
    simp only [SimpleGraph.adjMatrix_apply]
    simp [G.adj_comm]
  calc
    orderedDifferenceSet (graphCycleBlockZeroSupport G u v) =
        orderedDifferenceSet (zeroRowSupport B) := rfl
    _ = orderedDifferenceSet (zeroColumnSupport B) :=
      (orderedDifferenceSet_zeroColumn_eq_zeroRow_of_orientation B hOrient).symm
    _ = orderedDifferenceSet (graphCycleBlockZeroSupport G v u) :=
      congrArg orderedDifferenceSet hzeroCol

/-- Graph-facing canonical leave for intrinsic zero-row supports.  Each
target block may have either orientation independently. -/
theorem unusedOrderedDifferences_graphCycleBlockZeroSupport_eq_one_negOne
    {V K : Type*} [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : ZMod r → V) (w : K → ZMod r → V)
    (hu : Function.Injective u)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hw : ∀ k, Function.Injective (w k))
    (hwD : ∀ k x, (secondOrderDefectGraph G).neighborFinset (w k x) =
      {w k (x - 1), w k (x + 1)})
    (hwsep : ∀ {k l : K}, k ≠ l → ∀ x y, w k x ≠ w l y)
    (hcomm : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ)
    (hexcess : ∑ k,
      (graphCycleBlockZeroSupport G u (w k)).card *
        ((graphCycleBlockZeroSupport G u (w k)).card - 1) = r - 3) :
    unusedOrderedDifferences
      (fun k ↦ graphCycleBlockZeroSupport G u (w k)) = {1, -1} := by
  let A : K → Finset (ZMod r) :=
    fun k ↦ graphCycleBlockZeroSupport G u (w k)
  have hOrient : ∀ k,
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (w k (y + 1)) =
        G.adjMatrix ℤ (u x) (w k y)) ∨
      (∀ x y, G.adjMatrix ℤ (u (x + 1)) (w k (y - 1)) =
        G.adjMatrix ℤ (u x) (w k y)) := by
    intro k
    exact graph_equalOddCycleBlock_orientation hr3 hrOdd G
      (secondOrderDefectGraph G) u (w k) hu (hw k) hcomm huD (hwD k)
  have hpair : ∀ {k l : K}, k ≠ l →
      Disjoint (orderedDifferenceSet (A k))
        (orderedDifferenceSet (A l)) := by
    intro k l hkl
    simpa only [A, graphCycleBlockZeroSupport] using
      (orderedDifferenceSet_zeroRowSupport_disjoint_of_c4Free_orientations
        G hfree u (w k) (w l) hu (hwsep hkl) (hOrient k) (hOrient l))
  have hsidon : ∀ k, IsOrderedSidon (A k) := by
    intro k
    simpa only [A, graphCycleBlockZeroSupport] using
      (isOrderedSidon_zeroRowSupport_of_c4Free_orientation
        G hfree u (w k) hu (hw k) (hOrient k))
  have hone : ∀ k, (1 : ZMod r) ∉ orderedDifferenceSet (A k) := by
    intro k
    simpa only [A, graphCycleBlockZeroSupport] using
      (one_not_mem_orderedDifferenceSet_zeroRowSupport_of_secondOrder_orientation
        G hfree hd heven hmin hcard hr3 u (w k) hu huD (hOrient k))
  exact unusedOrderedDifferences_eq_one_negOne_of_packing
    hr3 A hpair hsidon (by simpa only [A] using hexcess) hone

end

end Erdos85
