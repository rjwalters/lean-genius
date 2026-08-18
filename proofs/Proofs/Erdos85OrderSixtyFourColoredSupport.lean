import Proofs.Erdos85OrderSixtyFourSevenComponentLocal
import Proofs.Erdos85FifthMomentBridge
import Proofs.Erdos85LocalTriangleParity

/-! # Colored support in the seven-component order-64 branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every triangle-free color degree is zero or two in the seven-component
order-64 branch.  The defect-component local-degree theorem gives the upper
bound two, while local triangle parity gives evenness. -/
theorem orderSixtyFour_seven_defect_components_triangleFree_degree_zero_or_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) (x : Fin 64) :
    (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 := by
  let instG := ‹DecidableRel G.Adj›
  let instAnti := ‹DecidableRel (antipodalGraph G).Adj›
  let instT := ‹DecidableRel (triangleFreeEdgeGraph G).Adj›
  let instComp := ‹DecidableEq (secondOrderDefectGraph G).ConnectedComponent›
  classical
  letI := instG
  letI := instAnti
  letI := instT
  letI := instComp
  let D := secondOrderDefectGraph G
  let T := triangleFreeEdgeGraph G
  obtain ⟨c, _hc16, hcLocal, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_local_degrees
      G hfree hmin hcover hcount
  let e := D.connectedComponentMk x
  have hsubset : T.neighborFinset x ⊆
      (G.neighborFinset x).filter (fun y => D.connectedComponentMk y = e) := by
    intro y hy
    have hTxy : T.Adj x y := (T.mem_neighborFinset x y).mp hy
    have hGxy : G.Adj x y :=
      ((mem_triangleFreeNeighbors G x y).mp
        ((triangleFreeEdgeGraph_adj G x y).mp hTxy)).1
    have hDxy : D.Adj x y := by
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y
      exact Or.inr hTxy
    refine Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hGxy, ?_⟩
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm
  have hlocalBound :
      ((G.neighborFinset x).filter
        (fun y => D.connectedComponentMk y = e)).card ≤ 2 := by
    by_cases hec : e = c
    · have hxmem : x ∈ c.supp := by
        rw [ConnectedComponent.mem_supp_iff]
        exact hec
      have h := hcLocal x hxmem
      simpa [D, e, hec] using h.le
    · obtain ⟨_he8, heLocal⟩ := hsmall e hec
      have h := heLocal x (by
        exact ConnectedComponent.connectedComponentMk_mem)
      have :
          ((G.neighborFinset x).filter
            (fun y => D.connectedComponentMk y = e)).card = 1 := by
        simpa [D, e] using h
      omega
  have hdegreeLe : T.degree x ≤ 2 := by
    rw [← T.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hsubset).trans hlocalBound
  have hdegreeLe' : (triangleFreeEdgeGraph G).degree x ≤ 2 := by
    simpa [T] using hdegreeLe
  have hparity : T.degree x % 2 = 0 := by
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
    simpa [hreg x] using
      triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree x
  have hnotOne : (triangleFreeEdgeGraph G).degree x ≠ 1 := by
    intro hone
    have : T.degree x = 1 := by simpa [T] using hone
    rw [this] at hparity
    norm_num at hparity
  rcases Nat.eq_zero_or_pos ((triangleFreeEdgeGraph G).degree x) with hzero | hpos
  · exact Or.inl hzero
  · exact Or.inr (by omega)

/-- In the seven-component order-64 branch, every vertex of triangle-free
degree two lies in the unique order-16 defect component.  Consequently the
triangle-free-colored sector has order at most sixteen. -/
theorem orderSixtyFour_seven_defect_components_colorOrder_le_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card ≤ 16 := by
  classical
  let D := secondOrderDefectGraph G
  let T := triangleFreeEdgeGraph G
  obtain ⟨c, hc16, _hcLocal, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_local_degrees
      G hfree hmin hcover hcount
  have hsupport : ∀ x : Fin 64, T.degree x = 2 → x ∈ c.supp := by
    intro x hx
    let e := D.connectedComponentMk x
    by_contra hxc
    have hec : e ≠ c := by
      intro heq
      apply hxc
      rw [ConnectedComponent.mem_supp_iff]
      exact heq
    obtain ⟨_he8, heLocal⟩ := hsmall e hec
    have hsubset : T.neighborFinset x ⊆
        (G.neighborFinset x).filter (fun y => D.connectedComponentMk y = e) := by
      intro y hy
      have hTxy : T.Adj x y := (T.mem_neighborFinset x y).mp hy
      have hGxy : G.Adj x y :=
        ((mem_triangleFreeNeighbors G x y).mp
          ((triangleFreeEdgeGraph_adj G x y).mp hTxy)).1
      have hDxy : D.Adj x y := by
        change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y
        exact Or.inr hTxy
      refine Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hGxy, ?_⟩
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm
    have hcard := Finset.card_le_card hsubset
    have hTcard : (T.neighborFinset x).card = 2 := by
      rw [T.card_neighborFinset_eq_degree, hx]
    have hecard :
        ((G.neighborFinset x).filter
          (fun y => D.connectedComponentMk y = e)).card = 1 := by
      simpa [D, e] using heLocal x (by
        exact ConnectedComponent.connectedComponentMk_mem)
    omega
  have hfilterSubset :
      (Finset.univ.filter fun x : Fin 64 => T.degree x = 2) ⊆ c.supp.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Set.mem_toFinset.mpr (hsupport x hx.2)
  calc
    (Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2).card =
        (Finset.univ.filter fun x : Fin 64 => T.degree x = 2).card := by rfl
    _ ≤ c.supp.toFinset.card := Finset.card_le_card hfilterSubset
    _ = c.supp.ncard := (Set.ncard_eq_toFinset_card' c.supp).symm
    _ = 16 := hc16

/-- Cubic trace in the seven-component branch, expressed exactly through
the colored order.  The component-local theorem reduces every
triangle-free degree to zero or two. -/
theorem orderSixtyFour_seven_defect_components_trace_cube_eq
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    Matrix.trace
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) =
      512 - 2 * ((Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
  classical
  let T := triangleFreeEdgeGraph G
  let C := (Finset.univ.filter fun x : Fin 64 => T.degree x = 2).card
  have hdegree : ∀ x : Fin 64, T.degree x = 0 ∨ T.degree x = 2 :=
    orderSixtyFour_seven_defect_components_triangleFree_degree_zero_or_two
      G hfree hmin hcover hcount
  have hsum : (∑ x : Fin 64, (T.degree x : ℤ)) = 2 * (C : ℤ) := by
    calc
      (∑ x : Fin 64, (T.degree x : ℤ)) =
          ∑ x : Fin 64, if T.degree x = 2 then (2 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hdegree x with hx | hx <;> simp [hx]
      _ = 2 * (C : ℤ) := by
        simp only [C]
        rw [← Finset.sum_filter]
        simp
        ring
  have hcolor :=
    trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees G
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hcubic :=
    trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree_of_regular
      G hfree hreg
  change Matrix.trace
      (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) =
    512 - 2 * (C : ℤ)
  have hcolor' : Matrix.trace (G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) = 2 * (C : ℤ) :=
    hcolor.trans (by simpa [T] using hsum)
  rw [hcolor'] at hcubic
  norm_num at hcubic ⊢
  linarith

/-- The colored-support cap turns the cubic identity into the numerical
lower bound `tr(A³) ≥ 480`. -/
theorem orderSixtyFour_seven_defect_components_trace_cube_ge_480
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    (480 : ℤ) ≤ Matrix.trace
      (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) := by
  rw [orderSixtyFour_seven_defect_components_trace_cube_eq
    G hfree hmin hcover hcount]
  have hC :=
    orderSixtyFour_seven_defect_components_colorOrder_le_sixteen
      G hfree hmin hcover hcount
  have hCZ : ((Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) ≤ 16 := by
    exact_mod_cast hC
  omega

end

end Erdos85
