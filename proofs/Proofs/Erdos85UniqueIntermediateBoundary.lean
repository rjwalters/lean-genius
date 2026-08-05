import Proofs.Erdos85UniqueSidonFactor
import Proofs.Erdos85SecondOrderQuotient

/-!
# Isolating a unique boundary intermediate component

Across two distinct components of the second-order defect two-factor, the
global square identity gives exactly one common `G`-neighbor.  If only one
defect component has positive quotient entries on both sides, that common
neighbor must lie in it.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem secondOrder_unique_common_neighbor_in_only_intermediate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {c k e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (honly : ∀ l : (secondOrderDefectGraph G).ConnectedComponent, l ≠ k →
      componentQuotientMatrix G (secondOrderDefectGraph G) c l = 0 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) l e = 0)
    {x y : V} (hx : x ∈ c.supp) (hy : y ∈ e.supp) :
    ∃! z : V, z ∈ k.supp ∧ G.Adj x z ∧ G.Adj z y := by
  let D := secondOrderDefectGraph G
  have hmkx : D.connectedComponentMk x = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
  have hmky : D.connectedComponentMk y = e :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e y).mp hy
  have hxy : x ≠ y := by
    intro h
    apply hce
    rw [← hmkx, ← hmky, h]
  have hDxy : ¬ D.Adj x y := by
    intro hadj
    apply hce
    rw [← hmkx, ← hmky]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  have hnotmem : y ∉ D.neighborFinset x := by
    simpa only [SimpleGraph.mem_neighborFinset] using hDxy
  have hcommon := card_common_eq_if_secondOrderDefect_of_even
    G hfree hd heven hmin hcard x y hxy
  rw [if_neg hnotmem] at hcommon
  obtain ⟨z, hzset⟩ := Finset.card_eq_one.mp hcommon
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    rw [hzset]
    simp
  have hzx : G.Adj z x := by
    exact ((G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hzmem).1).symm
  have hzy : G.Adj z y := by
    exact ((G.mem_neighborFinset y z).mp (Finset.mem_inter.mp hzmem).2).symm
  let l : D.ConnectedComponent := D.connectedComponentMk z
  have hz_l : z ∈ l.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff l z).mpr rfl
  have hlk : l = k := by
    by_contra hlne
    rcases honly l hlne with hzero | hzero
    · have hQ := componentQuotientMatrix_apply_eq G D 2
        (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
        (adjMatrix_comm_secondOrderDefect_of_even_real
          G hfree hd heven hmin hcard) c l hx
      have hzN : z ∈ componentNeighborFinset G D l x := by
        simp [componentNeighborFinset, hzx.symm,
          SimpleGraph.ConnectedComponent.mem_supp_iff, l]
      have hpos : 0 < componentQuotientMatrix G D c l := by
        rw [hQ]
        exact Finset.card_pos.mpr ⟨z, hzN⟩
      exact (Nat.ne_of_gt hpos) hzero
    · have hQ := componentQuotientMatrix_apply_eq G D 2
        (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
        (adjMatrix_comm_secondOrderDefect_of_even_real
          G hfree hd heven hmin hcard) l e hz_l
      have hyN : y ∈ componentNeighborFinset G D e z := by
        simp [componentNeighborFinset, hzy,
          SimpleGraph.ConnectedComponent.mem_supp_iff, hmky]
      have hpos : 0 < componentQuotientMatrix G D l e := by
        rw [hQ]
        exact Finset.card_pos.mpr ⟨y, hyN⟩
      exact (Nat.ne_of_gt hpos) hzero
  have hzk : z ∈ k.supp := by simpa [hlk] using hz_l
  refine ⟨z, ⟨hzk, hzx.symm, hzy⟩, ?_⟩
  intro z' hz'
  have hz'mem : z' ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x z').mpr hz'.2.1,
      (G.mem_neighborFinset y z').mpr hz'.2.2.symm⟩
  rw [hzset] at hz'mem
  exact Finset.mem_singleton.mp hz'mem

/-- Coordinate form of the preceding theorem.  Exact cycle parametrizations
transport the unique middle vertex to a unique middle cyclic coordinate. -/
theorem secondOrder_unique_middle_coordinate_in_only_intermediate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {Z : Type*} [Fintype Z]
    {c k e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (honly : ∀ l : (secondOrderDefectGraph G).ConnectedComponent, l ≠ k →
      componentQuotientMatrix G (secondOrderDefectGraph G) c l = 0 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) l e = 0)
    (u w v : Z → V)
    (huRange : Set.range u = c.supp)
    (hwInj : Function.Injective w) (hwRange : Set.range w = k.supp)
    (hvRange : Set.range v = e.supp) :
    ∀ x y : Z, ∃! z : Z,
      G.Adj (u x) (w z) ∧ G.Adj (w z) (v y) := by
  intro x y
  have hux : u x ∈ c.supp := by rw [← huRange]; exact ⟨x, rfl⟩
  have hvy : v y ∈ e.supp := by rw [← hvRange]; exact ⟨y, rfl⟩
  obtain ⟨q, hq, hquniq⟩ :=
    secondOrder_unique_common_neighbor_in_only_intermediate
      G hfree hd heven hmin hcard hce honly hux hvy
  have hqrange : q ∈ Set.range w := by simpa [hwRange] using hq.1
  obtain ⟨z, hz⟩ := hqrange
  refine ⟨z, ?_, ?_⟩
  · simpa [hz] using hq.2
  · intro z' hz'
    apply hwInj
    have hwz'k : w z' ∈ k.supp := by rw [← hwRange]; exact ⟨z', rfl⟩
    have heq := hquniq (w z') ⟨hwz'k, hz'.1, hz'.2⟩
    simpa [hz] using heq

/-- Fully assembled boundary contradiction once the two equal-cycle blocks
have been put in circulant coordinates. -/
theorem secondOrder_no_only_intermediate_of_circulant_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    {c k e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (honly : ∀ l : (secondOrderDefectGraph G).ConnectedComponent, l ≠ k →
      componentQuotientMatrix G (secondOrderDefectGraph G) c l = 0 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) l e = 0)
    (u w v : ZMod r → V)
    (huInj : Function.Injective u) (hwInj : Function.Injective w)
    (hvInj : Function.Injective v)
    (huRange : Set.range u = c.supp)
    (hwRange : Set.range w = k.supp)
    (hvRange : Set.range v = e.supp)
    (A B : Finset (ZMod r))
    (hAblock : ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A)
    (hBblock : ∀ x z, G.Adj (w x) (v z) ↔ z - x ∈ B) : False := by
  apply no_unique_middle_circulant_blocks G hfree u w v
    huInj hwInj hvInj A B hAblock hBblock
  · simpa using hr3
  · exact secondOrder_unique_middle_coordinate_in_only_intermediate
      G hfree hd heven hmin hcard hce honly u w v
      huRange hwInj hwRange hvRange

/-- Orientation-free assembly for three already-parametrized equal odd
defect cycles.  Reflections of the middle and target coordinates reduce all
four orientation combinations to the preceding circulant theorem. -/
theorem secondOrder_no_only_intermediate_of_equalOddCycleParams
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) (hrOdd : Odd r)
    {c k e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e)
    (honly : ∀ l : (secondOrderDefectGraph G).ConnectedComponent, l ≠ k →
      componentQuotientMatrix G (secondOrderDefectGraph G) c l = 0 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) l e = 0)
    (u w v : ZMod r → V)
    (huInj : Function.Injective u) (hwInj : Function.Injective w)
    (hvInj : Function.Injective v)
    (huRange : Set.range u = c.supp)
    (hwRange : Set.range w = k.supp)
    (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hwD : ∀ x, (secondOrderDefectGraph G).neighborFinset (w x) =
      {w (x - 1), w (x + 1)})
    (hvD : ∀ x, (secondOrderDefectGraph G).neighborFinset (v x) =
      {v (x - 1), v (x + 1)}) : False := by
  let D := secondOrderDefectGraph G
  let P : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x z ↦ G.adjMatrix ℤ (u x) (w z)
  let Q : Matrix (ZMod r) (ZMod r) ℤ :=
    fun z y ↦ G.adjMatrix ℤ (w z) (v y)
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hPO := graph_equalOddCycleBlock_orientation hr3 hrOdd G D u w
    huInj hwInj hcomm huD hwD
  have hQO := graph_equalOddCycleBlock_orientation hr3 hrOdd G D w v
    hwInj hvInj hcomm hwD hvD
  have range_reflect (f : ZMod r → V) :
      Set.range (fun z ↦ f (-z)) = Set.range f := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨-z, by simp⟩
    · rintro ⟨z, rfl⟩
      exact ⟨-z, by simp⟩
  have inj_reflect {f : ZMod r → V} (hf : Function.Injective f) :
      Function.Injective (fun z ↦ f (-z)) := by
    intro a b hab
    have hn : -a = -b := hf hab
    exact neg_injective hn
  rcases hPO with hPT | hPR <;> rcases hQO with hQT | hQR
  · obtain ⟨A, hA⟩ := exists_connectionSet_of_translationInvariantBlock G u w hPT
    obtain ⟨B, hB⟩ := exists_connectionSet_of_translationInvariantBlock G w v hQT
    exact secondOrder_no_only_intermediate_of_circulant_blocks
      G hfree hd heven hmin hcard hr3 hce honly u w v
      huInj hwInj hvInj huRange hwRange hvRange A B hA hB
  · let v' : ZMod r → V := fun y ↦ v (-y)
    have hQR' : ∀ x y,
        G.adjMatrix ℤ (w (x + 1)) (v' (y + 1)) =
          G.adjMatrix ℤ (w x) (v' y) := by
      exact reverseInvariant_targetReflection_translationInvariant Q
        (by simpa only [Q] using hQR)
    obtain ⟨A, hA⟩ := exists_connectionSet_of_translationInvariantBlock G u w hPT
    obtain ⟨B, hB⟩ := exists_connectionSet_of_translationInvariantBlock G w v' hQR'
    exact secondOrder_no_only_intermediate_of_circulant_blocks
      G hfree hd heven hmin hcard hr3 hce honly u w v'
      huInj hwInj (inj_reflect hvInj) huRange hwRange
      ((range_reflect v).trans hvRange) A B hA hB
  · let w' : ZMod r → V := fun z ↦ w (-z)
    let v' : ZMod r → V := fun y ↦ v (-y)
    have hPR' : ∀ x z,
        G.adjMatrix ℤ (u (x + 1)) (w' (z + 1)) =
          G.adjMatrix ℤ (u x) (w' z) := by
      exact reverseInvariant_targetReflection_translationInvariant P
        (by simpa only [P] using hPR)
    have hQT' : ∀ z y,
        G.adjMatrix ℤ (w' (z + 1)) (v' (y + 1)) =
          G.adjMatrix ℤ (w' z) (v' y) := by
      have hs := translationInvariant_sourceReflection_reverseInvariant Q
        (by simpa only [Q] using hQT)
      exact reverseInvariant_targetReflection_translationInvariant
        (fun z y ↦ Q (-z) y) hs
    obtain ⟨A, hA⟩ := exists_connectionSet_of_translationInvariantBlock G u w' hPR'
    obtain ⟨B, hB⟩ := exists_connectionSet_of_translationInvariantBlock G w' v' hQT'
    exact secondOrder_no_only_intermediate_of_circulant_blocks
      G hfree hd heven hmin hcard hr3 hce honly u w' v'
      huInj (inj_reflect hwInj) (inj_reflect hvInj) huRange
      ((range_reflect w).trans hwRange) ((range_reflect v).trans hvRange)
      A B hA hB
  · let w' : ZMod r → V := fun z ↦ w (-z)
    have hPR' : ∀ x z,
        G.adjMatrix ℤ (u (x + 1)) (w' (z + 1)) =
          G.adjMatrix ℤ (u x) (w' z) := by
      exact reverseInvariant_targetReflection_translationInvariant P
        (by simpa only [P] using hPR)
    have hQR' : ∀ z y,
        G.adjMatrix ℤ (w' (z + 1)) (v (y + 1)) =
          G.adjMatrix ℤ (w' z) (v y) := by
      exact reverseInvariant_sourceReflection_translationInvariant Q
        (by simpa only [Q] using hQR)
    obtain ⟨A, hA⟩ := exists_connectionSet_of_translationInvariantBlock G u w' hPR'
    obtain ⟨B, hB⟩ := exists_connectionSet_of_translationInvariantBlock G w' v hQR'
    exact secondOrder_no_only_intermediate_of_circulant_blocks
      G hfree hd heven hmin hcard hr3 hce honly u w' v
      huInj (inj_reflect hwInj) hvInj huRange
      ((range_reflect w).trans hwRange) hvRange A B hA hB

end

end Erdos85
