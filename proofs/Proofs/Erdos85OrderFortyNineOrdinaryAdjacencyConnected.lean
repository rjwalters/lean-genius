import Proofs.Erdos85OrderFortyNineOrdinaryAdjacencyForcedSector
import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos85DisconnectedShorePartition

/-!
# Connectivity of the order-49 ordinary adjacency block

The three high-neighborhood columns are open perfect codes in the ordinary
graph.  Their support-count balance forces every connected component to
contain either all three pairpoints or none.  A component of the latter kind
would have equally many support-one and support-zero vertices, respectively
of degrees six and seven.  Cherry counting then requires at least nineteen
support-one vertices, although only eighteen exist globally.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph induced by the 46 degree-seven vertices in the canonical
three-high labeling. -/
def orderFortyNineOrdinaryGraph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    SimpleGraph (Fin 46) :=
  G.comap orderFortyNineOrdinaryVertex

local instance orderFortyNineOrdinaryGraph_decidableAdj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    DecidableRel (orderFortyNineOrdinaryGraph G).Adj :=
  Classical.decRel _

def orderFortyNineOrdinarySupportFiber
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : Finset (Fin 46)) (k : ℤ) : Finset (Fin 46) :=
  S.filter fun i => orderFortyNineOrdinaryHighSupportCountInt G i = k

def orderFortyNineOrdinaryShoreGraph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : Finset (Fin 46)) : SimpleGraph S :=
  (orderFortyNineOrdinaryGraph G).comap Subtype.val

local instance orderFortyNineOrdinaryShoreGraph_decidableAdj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : Finset (Fin 46)) :
    DecidableRel (orderFortyNineOrdinaryShoreGraph G S).Adj :=
  Classical.decRel _

theorem sum_support_weight_eq_ten_mul_two_add_six_mul_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : Finset (Fin 46))
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2) :
    (∑ i ∈ S,
      (7 - orderFortyNineOrdinaryHighSupportCountInt G i) *
        orderFortyNineOrdinaryHighSupportCountInt G i) =
      10 * (orderFortyNineOrdinarySupportFiber G S 2).card +
        6 * (orderFortyNineOrdinarySupportFiber G S 1).card := by
  have hpoint (i : Fin 46) :
      (7 - orderFortyNineOrdinaryHighSupportCountInt G i) *
          orderFortyNineOrdinaryHighSupportCountInt G i =
        if orderFortyNineOrdinaryHighSupportCountInt G i = 2 then 10
        else if orderFortyNineOrdinaryHighSupportCountInt G i = 1 then 6
        else 0 := by
    rcases hrange i with hi | hi | hi <;> simp [hi]
  simp_rw [hpoint]
  calc
    (∑ i ∈ S, if orderFortyNineOrdinaryHighSupportCountInt G i = 2 then (10 : ℤ)
        else if orderFortyNineOrdinaryHighSupportCountInt G i = 1 then 6
        else 0) =
        (∑ i ∈ S,
          if orderFortyNineOrdinaryHighSupportCountInt G i = 2 then (10 : ℤ) else 0) +
        ∑ i ∈ S,
          if orderFortyNineOrdinaryHighSupportCountInt G i = 1 then (6 : ℤ) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi2 : orderFortyNineOrdinaryHighSupportCountInt G i = 2
      · simp [hi2]
      · simp [hi2]
    _ = _ := by
      have hten :
          (∑ i ∈ S,
            if orderFortyNineOrdinaryHighSupportCountInt G i = 2
            then (10 : ℤ) else 0) =
          10 * (orderFortyNineOrdinarySupportFiber G S 2).card := by
        simp_rw [show ∀ i : Fin 46,
            (if orderFortyNineOrdinaryHighSupportCountInt G i = 2
              then (10 : ℤ) else 0) =
            10 * (if orderFortyNineOrdinaryHighSupportCountInt G i = 2
              then 1 else 0) by
          intro i
          split_ifs <;> norm_num]
        rw [← Finset.mul_sum, Finset.sum_boole]
        simp [orderFortyNineOrdinarySupportFiber]
      have hsix :
          (∑ i ∈ S,
            if orderFortyNineOrdinaryHighSupportCountInt G i = 1
            then (6 : ℤ) else 0) =
          6 * (orderFortyNineOrdinarySupportFiber G S 1).card := by
        simp_rw [show ∀ i : Fin 46,
            (if orderFortyNineOrdinaryHighSupportCountInt G i = 1
              then (6 : ℤ) else 0) =
            6 * (if orderFortyNineOrdinaryHighSupportCountInt G i = 1
              then 1 else 0) by
          intro i
          split_ifs <;> norm_num]
        rw [← Finset.mul_sum, Finset.sum_boole]
        simp [orderFortyNineOrdinarySupportFiber]
      rw [hten, hsix]

theorem orderFortyNineOrdinaryGraph_not_containsC4
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) :
    ¬ containsC4 (Fin 46) (orderFortyNineOrdinaryGraph G) := by
  intro hcycle
  rcases hcycle with ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨orderFortyNineOrdinaryVertex ∘ f, ?_, ?_⟩
  · intro i j hij
    apply hf
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simp [Function.comp_apply, orderFortyNineOrdinaryVertex] at hval
    omega
  · intro i j hij
    exact hadj i j hij

theorem orderFortyNineOrdinaryShoreGraph_not_containsC4
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (S : Finset (Fin 46)) :
    ¬ containsC4 S (orderFortyNineOrdinaryShoreGraph G S) := by
  intro hcycle
  rcases hcycle with ⟨f, hf, hadj⟩
  apply orderFortyNineOrdinaryGraph_not_containsC4 G hfree
  refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

theorem orderFortyNineOrdinaryShoreGraph_degree_eq
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S T : Finset (Fin 46)) (hcover : S ∪ T = Finset.univ)
    (hanti : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (orderFortyNineOrdinaryGraph G).Adj s t)
    (x : S) :
    (orderFortyNineOrdinaryShoreGraph G S).degree x =
      (orderFortyNineOrdinaryGraph G).degree x := by
  rw [← (orderFortyNineOrdinaryShoreGraph G S).card_neighborFinset_eq_degree,
    ← (orderFortyNineOrdinaryGraph G).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    simpa [SimpleGraph.mem_neighborFinset,
      orderFortyNineOrdinaryShoreGraph] using hy
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro y hy
    have hyAdj : (orderFortyNineOrdinaryGraph G).Adj x y := by
      simpa [SimpleGraph.mem_neighborFinset] using hy
    have hyS : y ∈ S := by
      have hyU : y ∈ S ∪ T := by rw [hcover]; simp
      rcases Finset.mem_union.mp hyU with hyS | hyT
      · exact hyS
      · exact (hanti x x.2 y hyT hyAdj).elim
    refine ⟨⟨y, hyS⟩, ?_, rfl⟩
    simpa [SimpleGraph.mem_neighborFinset,
      orderFortyNineOrdinaryShoreGraph] using hyAdj

theorem orderFortyNineOrdinaryGraph_adjMatrix_int
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    (orderFortyNineOrdinaryGraph G).adjMatrix ℤ =
      orderFortyNineOrdinaryAdjInt G := by
  ext i j
  simp [orderFortyNineOrdinaryGraph, orderFortyNineOrdinaryAdjInt,
    SimpleGraph.adjMatrix_apply]

/-- Ordinary degree is seven minus the number of incident high roots. -/
theorem orderFortyNineOrdinaryGraph_degree_int
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (i : Fin 46) :
    ((orderFortyNineOrdinaryGraph G).degree i : ℤ) =
      7 - orderFortyNineOrdinaryHighSupportCountInt G i := by
  have hrow := congrFun
    (orderFortyNineOrdinaryAdjInt_mulVec_one G hfree hmin hhigh) i
  rw [← orderFortyNineOrdinaryGraph_adjMatrix_int] at hrow
  simp only [SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const,
    nsmul_eq_mul, mul_one] at hrow
  rw [(orderFortyNineOrdinaryGraph G).card_neighborFinset_eq_degree] at hrow
  exact hrow

/-- Summing an adjacency action over one shore of an anticomplete partition
is the degree-weighted sum on that shore. -/
theorem sum_adjMatrix_mulVec_on_anticomplete_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S T : Finset V) (hcover : S ∪ T = Finset.univ)
    (_hdisj : Disjoint S T)
    (hanti : ∀ s ∈ S, ∀ t ∈ T, ¬ H.Adj s t)
    (w : V → ℤ) :
    (∑ x ∈ S, (H.adjMatrix ℤ).mulVec w x) =
      ∑ x ∈ S, (H.degree x : ℤ) * w x := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  calc
    (∑ x : V, ∑ y ∈ S, H.adjMatrix ℤ y x * w x) =
        ∑ x : V, (∑ y ∈ S, H.adjMatrix ℤ y x) * w x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ x ∈ S, (H.degree x : ℤ) * w x := by
      rw [← Finset.sum_subset (s₁ := S) (s₂ := Finset.univ)
        (Finset.subset_univ S)]
      · apply Finset.sum_congr rfl
        intro x hx
        congr 1
        rw [← H.card_neighborFinset_eq_degree]
        simp only [SimpleGraph.adjMatrix_apply]
        rw [Finset.sum_boole]
        norm_cast
        apply congrArg Finset.card
        ext y
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        constructor
        · intro hy
          exact hy.2.symm
        · intro hy
          have hyS : y ∈ S := by
            have hyU : y ∈ S ∪ T := by rw [hcover]; simp
            rcases Finset.mem_union.mp hyU with hyS | hyT
            · exact hyS
            · exact (hanti x hx y hyT hy).elim
          exact ⟨hyS, hy.symm⟩
      · intro x _ hxnot
        have hxT : x ∈ T := by
          have hxU : x ∈ S ∪ T := by rw [hcover]; simp
          rcases Finset.mem_union.mp hxU with hxS | hxT
          · exact (hxnot hxS).elim
          · exact hxT
        apply mul_eq_zero_of_left
        apply Finset.sum_eq_zero
        intro y hy
        simp [SimpleGraph.adjMatrix_apply, hanti y hy x hxT]

/-- The support-count equation summed over a closed ordinary shore. -/
theorem orderFortyNineOrdinary_shore_support_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (S T : Finset (Fin 46)) (hcover : S ∪ T = Finset.univ)
    (hdisj : Disjoint S T)
    (hanti : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (orderFortyNineOrdinaryGraph G).Adj s t) :
    (∑ i ∈ S,
      (7 - orderFortyNineOrdinaryHighSupportCountInt G i) *
        orderFortyNineOrdinaryHighSupportCountInt G i) =
      3 * S.card := by
  let C := orderFortyNineOrdinaryGraph G
  let s := orderFortyNineOrdinaryHighSupportCountInt G
  have haction :=
    orderFortyNineOrdinaryAdjInt_mulVec_highSupportCount
      G hfree hmin hhigh
  rw [← orderFortyNineOrdinaryGraph_adjMatrix_int] at haction
  have hsum := congrArg (fun v : Fin 46 → ℤ => ∑ i ∈ S, v i) haction
  have hshore := sum_adjMatrix_mulVec_on_anticomplete_shore
    C S T hcover hdisj hanti s
  rw [hshore] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hsum' :
      (∑ i ∈ S, ((orderFortyNineOrdinaryGraph G).degree i : ℤ) *
        orderFortyNineOrdinaryHighSupportCountInt G i) =
        3 * S.card := by
    simpa [mul_comm] using hsum
  dsimp [C, s] at hsum ⊢
  rw [← hsum']
  apply Finset.sum_congr rfl
  intro i _
  rw [orderFortyNineOrdinaryGraph_degree_int G hfree hmin hhigh i]

theorem orderFortyNineOrdinary_shore_support_count_balance
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (S T : Finset (Fin 46)) (hcover : S ∪ T = Finset.univ)
    (hdisj : Disjoint S T)
    (hanti : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (orderFortyNineOrdinaryGraph G).Adj s t) :
    10 * ((orderFortyNineOrdinarySupportFiber G S 2).card : ℤ) +
        6 * ((orderFortyNineOrdinarySupportFiber G S 1).card : ℤ) =
      3 * (S.card : ℤ) := by
  rw [← sum_support_weight_eq_ten_mul_two_add_six_mul_one G S hrange]
  exact orderFortyNineOrdinary_shore_support_balance
    G hfree hmin hhigh S T hcover hdisj hanti

/-- If the ordinary graph disconnects in the no-triple profile, one shore
contains no support-two vertex. -/
theorem exists_supportTwo_free_ordinary_shore_of_not_preconnected
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (htwo : (orderFortyNineOrdinarySupportFiber G Finset.univ 2).card = 3)
    (hnot : ¬ (orderFortyNineOrdinaryGraph G).Preconnected) :
    ∃ S T : Finset (Fin 46),
      S.Nonempty ∧ T.Nonempty ∧ S ∪ T = Finset.univ ∧ Disjoint S T ∧
      (∀ s ∈ S, ∀ t ∈ T,
        ¬ (orderFortyNineOrdinaryGraph G).Adj s t) ∧
      (orderFortyNineOrdinarySupportFiber G S 2).card = 0 := by
  obtain ⟨S, T, hSne, hTne, hcover, hdisj, hanti⟩ :=
    exists_nonempty_anticomplete_partition_of_not_preconnected
      (orderFortyNineOrdinaryGraph G) hnot
  have hS := orderFortyNineOrdinary_shore_support_count_balance
    G hfree hmin hhigh hrange S T hcover hdisj hanti
  have hanti' : ∀ t ∈ T, ∀ s ∈ S,
      ¬ (orderFortyNineOrdinaryGraph G).Adj t s := by
    intro t ht s hs hts
    exact hanti s hs t ht hts.symm
  have hcover' : T ∪ S = Finset.univ := by simpa [Finset.union_comm] using hcover
  have hdisj' : Disjoint T S := hdisj.symm
  have hT := orderFortyNineOrdinary_shore_support_count_balance
    G hfree hmin hhigh hrange T S hcover' hdisj' hanti'
  have hfibDisjoint : Disjoint
      (orderFortyNineOrdinarySupportFiber G S 2)
      (orderFortyNineOrdinarySupportFiber G T 2) :=
    hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hfibUnion :
      orderFortyNineOrdinarySupportFiber G S 2 ∪
          orderFortyNineOrdinarySupportFiber G T 2 =
        orderFortyNineOrdinarySupportFiber G Finset.univ 2 := by
    ext i
    have hiU : i ∈ S ∪ T := by rw [hcover]; simp
    simp only [orderFortyNineOrdinarySupportFiber, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨_, hi⟩ | ⟨_, hi⟩) <;> exact hi
    · intro hi
      rcases Finset.mem_union.mp hiU with hiS | hiT
      · exact Or.inl ⟨hiS, hi⟩
      · exact Or.inr ⟨hiT, hi⟩
  have hsplit :
      (orderFortyNineOrdinarySupportFiber G S 2).card +
        (orderFortyNineOrdinarySupportFiber G T 2).card = 3 := by
    rw [← htwo, ← hfibUnion, Finset.card_union_of_disjoint hfibDisjoint]
  have hzero :
      (orderFortyNineOrdinarySupportFiber G S 2).card = 0 ∨
      (orderFortyNineOrdinarySupportFiber G T 2).card = 0 := by
    omega
  rcases hzero with hzero | hzero
  · exact ⟨S, T, hSne, hTne, hcover, hdisj, hanti, hzero⟩
  · exact ⟨T, S, hTne, hSne, hcover', hdisj', hanti', hzero⟩

theorem ordinary_shore_card_eq_twice_supportOne_of_supportTwo_free
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : Finset (Fin 46))
    (hbalance :
      10 * ((orderFortyNineOrdinarySupportFiber G S 2).card : ℤ) +
          6 * ((orderFortyNineOrdinarySupportFiber G S 1).card : ℤ) =
        3 * (S.card : ℤ))
    (hzero : (orderFortyNineOrdinarySupportFiber G S 2).card = 0) :
    S.card = 2 * (orderFortyNineOrdinarySupportFiber G S 1).card := by
  omega

theorem orderFortyNineOrdinaryShoreGraph_degree_eq_six_or_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (S T : Finset (Fin 46)) (hcover : S ∪ T = Finset.univ)
    (hanti : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (orderFortyNineOrdinaryGraph G).Adj s t)
    (hzero : (orderFortyNineOrdinarySupportFiber G S 2).card = 0)
    (x : S) :
    (orderFortyNineOrdinaryShoreGraph G S).degree x =
      if orderFortyNineOrdinaryHighSupportCountInt G x = 1 then 6 else 7 := by
  have hxnot2 : orderFortyNineOrdinaryHighSupportCountInt G x ≠ 2 := by
    intro hx2
    have hxmem : x.1 ∈ orderFortyNineOrdinarySupportFiber G S 2 := by
      simp [orderFortyNineOrdinarySupportFiber, x.2, hx2]
    have hne : (orderFortyNineOrdinarySupportFiber G S 2).Nonempty :=
      ⟨x.1, hxmem⟩
    rw [Finset.card_eq_zero] at hzero
    exact hne.ne_empty hzero
  have hxrange := hrange x
  rcases hxrange with hx0 | hx1 | hx2
  · rw [if_neg (by omega :
        orderFortyNineOrdinaryHighSupportCountInt G x ≠ 1)]
    rw [orderFortyNineOrdinaryShoreGraph_degree_eq G S T hcover hanti]
    have hdeg := orderFortyNineOrdinaryGraph_degree_int
      G hfree hmin hhigh x
    rw [hx0] at hdeg
    norm_num at hdeg
    exact_mod_cast hdeg
  · rw [if_pos hx1]
    rw [orderFortyNineOrdinaryShoreGraph_degree_eq G S T hcover hanti]
    have hdeg := orderFortyNineOrdinaryGraph_degree_int
      G hfree hmin hhigh x
    rw [hx1] at hdeg
    norm_num at hdeg
    exact_mod_cast hdeg
  · exact (hxnot2 hx2).elim

theorem ordinaryShore_subtype_supportFiber_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : Finset (Fin 46)) (k : ℤ) :
    ((Finset.univ : Finset S).filter (fun x : S =>
        orderFortyNineOrdinaryHighSupportCountInt G x.1 = k)).card =
      (orderFortyNineOrdinarySupportFiber G S k).card := by
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [orderFortyNineOrdinarySupportFiber, x.2, hx]
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro y hy
    simp only [orderFortyNineOrdinarySupportFiber, Finset.mem_filter] at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    simp [hy.2]

theorem orderFortyNineOrdinaryShoreGraph_sum_degree_choose_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (S T : Finset (Fin 46)) (hcover : S ∪ T = Finset.univ)
    (hanti : ∀ s ∈ S, ∀ t ∈ T,
      ¬ (orderFortyNineOrdinaryGraph G).Adj s t)
    (hzero : (orderFortyNineOrdinarySupportFiber G S 2).card = 0)
    (hcard : S.card =
      2 * (orderFortyNineOrdinarySupportFiber G S 1).card) :
    (∑ x : S,
      ((orderFortyNineOrdinaryShoreGraph G S).degree x).choose 2) =
      36 * (orderFortyNineOrdinarySupportFiber G S 1).card := by
  have hchoose (x : S) :
      ((orderFortyNineOrdinaryShoreGraph G S).degree x).choose 2 =
        if orderFortyNineOrdinaryHighSupportCountInt G x = 1
        then 15 else 21 := by
    rw [orderFortyNineOrdinaryShoreGraph_degree_eq_six_or_seven
      G hfree hmin hhigh hrange S T hcover hanti hzero x]
    split_ifs <;> decide
  simp_rw [hchoose]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hone := ordinaryShore_subtype_supportFiber_card G S 1
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset S))
    (p := fun x : S =>
      orderFortyNineOrdinaryHighSupportCountInt G x.1 = 1)
  rw [hone] at hpartition
  simp only [Finset.card_univ, Fintype.card_coe] at hpartition
  have hneg :
      ((Finset.univ : Finset S).filter (fun x : S =>
        ¬ orderFortyNineOrdinaryHighSupportCountInt G x.1 = 1)).card =
      (orderFortyNineOrdinarySupportFiber G S 1).card := by
    omega
  change
    ((Finset.univ : Finset S).filter (fun x : S =>
        orderFortyNineOrdinaryHighSupportCountInt G x.1 = 1)).card * 15 +
      ((Finset.univ : Finset S).filter (fun x : S =>
        ¬ orderFortyNineOrdinaryHighSupportCountInt G x.1 = 1)).card * 21 =
      36 * (orderFortyNineOrdinarySupportFiber G S 1).card
  rw [hone]
  rw [hneg]
  omega

/-- In the no-triple three-high profile, the ordinary adjacency graph is
preconnected. -/
theorem orderFortyNineOrdinaryGraph_preconnected_of_noTriple_profile
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (hrange : ∀ i,
      orderFortyNineOrdinaryHighSupportCountInt G i = 0 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 1 ∨
      orderFortyNineOrdinaryHighSupportCountInt G i = 2)
    (htwo : (orderFortyNineOrdinarySupportFiber G Finset.univ 2).card = 3)
    (hone : (orderFortyNineOrdinarySupportFiber G Finset.univ 1).card = 18) :
    (orderFortyNineOrdinaryGraph G).Preconnected := by
  by_contra hnot
  obtain ⟨S, T, hSne, hTne, hcover, hdisj, hanti, hzero⟩ :=
    exists_supportTwo_free_ordinary_shore_of_not_preconnected
      G hfree hmin hhigh hrange htwo hnot
  have hbalance := orderFortyNineOrdinary_shore_support_count_balance
    G hfree hmin hhigh hrange S T hcover hdisj hanti
  have hcard := ordinary_shore_card_eq_twice_supportOne_of_supportTwo_free
    G S hbalance hzero
  let b := (orderFortyNineOrdinarySupportFiber G S 1).card
  have hbpos : 0 < b := by
    have hSpos : 0 < S.card := Finset.card_pos.mpr hSne
    dsimp [b]
    omega
  have hble : b ≤ 18 := by
    dsimp [b]
    rw [← hone]
    apply Finset.card_le_card
    intro i hi
    simp only [orderFortyNineOrdinarySupportFiber,
      Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ i, hi.2⟩
  have hsum := orderFortyNineOrdinaryShoreGraph_sum_degree_choose_two
    G hfree hmin hhigh hrange S T hcover hanti hzero hcard
  have hcherry :=
    sum_degree_choose_two_le_card_choose_two_of_not_containsC4
      (orderFortyNineOrdinaryShoreGraph G S)
      (orderFortyNineOrdinaryShoreGraph_not_containsC4 G hfree S)
  rw [hsum] at hcherry
  simp only [Fintype.card_coe] at hcherry
  have hcardb : S.card = 2 * b := by exact hcard
  rw [hcardb] at hcherry
  have htwice := two_mul_choose_two (2 * b)
  have hdouble : 2 * (36 * b) ≤ 2 * ((2 * b).choose 2) :=
    Nat.mul_le_mul_left 2 hcherry
  rw [htwice] at hdouble
  have hpred : 2 * b - 1 ≤ 35 := by omega
  have hupper : 2 * b * (2 * b - 1) ≤ 2 * b * 35 :=
    Nat.mul_le_mul_left (2 * b) hpred
  omega

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryGraph_not_containsC4
#print axioms Erdos85.orderFortyNineOrdinaryGraph_adjMatrix_int
#print axioms Erdos85.orderFortyNineOrdinaryGraph_degree_int
#print axioms Erdos85.sum_adjMatrix_mulVec_on_anticomplete_shore
#print axioms Erdos85.orderFortyNineOrdinary_shore_support_balance
#print axioms Erdos85.orderFortyNineOrdinary_shore_support_count_balance
#print axioms Erdos85.exists_supportTwo_free_ordinary_shore_of_not_preconnected
#print axioms Erdos85.orderFortyNineOrdinaryGraph_preconnected_of_noTriple_profile
