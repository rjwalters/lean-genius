import Proofs.Erdos85ComponentCycleCharpoly
import Proofs.Erdos85CycleResolvent

namespace Erdos85

open SimpleGraph
open Polynomial Polynomial.Chebyshev

theorem secondOrderDefect_resolvent_eq_prod_chebyshev
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3)
    (a : ℤ) :
    ∃ r : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ c, 3 ≤ r c) ∧
      (∀ c, r c = c.supp.ncard) ∧
      Matrix.det (Matrix.scalar V a - (secondOrderDefectGraph G).adjMatrix ℤ) =
        ∏ c, (Polynomial.Chebyshev.C ℤ (r c : ℤ) - 2).eval a := by
  classical
  choose r hr hrsize hdet using fun c =>
    secondOrderDefect_component_resolvent_chebyshev
      G hfree hd heven hmin hcard c a
  refine ⟨r, hr, hrsize, ?_⟩
  rw [det_resolvent_eq_prod_connectedComponents]
  apply Finset.prod_congr rfl
  intro c hc
  have hscalar : Matrix.scalar c.supp a =
      Matrix.diagonal (fun _ : c.supp ↦ a) := rfl
  rw [hscalar, hdet c]

/-- The actual defect-component lengths are all at least three and partition
the vertex set.  Their total order is odd, while the number of even-order
components is even.  This discharges the former conditional factorization
hypothesis in the cycle-resolvent obstruction. -/
theorem secondOrderDefect_cycle_lengths_parity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3) :
    ∃ rs : List ℕ, (∀ r ∈ rs, 3 ≤ r) ∧
      rs.sum = Fintype.card V ∧ Odd rs.sum ∧ Even (evenCycleCount rs) := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨r, hr, hrsize, hfactorZ⟩ :=
    secondOrderDefect_resolvent_eq_prod_chebyshev
      G hfree hd heven hmin hcard ((d : ℤ) - 1)
  let rs := (Finset.univ : Finset D.ConnectedComponent).toList.map r
  have hparts : (∑ c : D.ConnectedComponent, c.supp.ncard) = Fintype.card V := by
    calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c hc
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  have hsum_toList (s : Finset D.ConnectedComponent) :
      (s.toList.map r).sum = ∑ c ∈ s, r c := by
    calc
      (s.toList.map r).sum = s.toList.toFinset.sum r :=
        (List.sum_toFinset r s.nodup_toList).symm
      _ = s.sum r := by rw [s.toList_toFinset]
  have hrsum : rs.sum = Fintype.card V := by
    have htmp : rs.sum = ∑ x, r x := by
      simpa [rs] using hsum_toList
        (Finset.univ : Finset D.ConnectedComponent)
    rw [htmp]
    rw [show (∑ x, r x) = ∑ x : D.ConnectedComponent, x.supp.ncard by
      apply Finset.sum_congr rfl
      intro c hc
      exact hrsize c]
    exact hparts
  have hoddcard : Odd (Fintype.card V) := by
    rw [hcard]
    exact (heven.mul_right (d - 1)).add_odd (by norm_num)
  have hodd : Odd rs.sum := hrsum ▸ hoddcard
  have hrthree : ∀ n ∈ rs, 3 ≤ n := by
    intro n hn
    simp only [rs, List.mem_map] at hn
    obtain ⟨c, hc, rfl⟩ := hn
    exact hr c
  refine ⟨rs, hrthree, hrsum, hodd, ?_⟩
  let fZ : D.ConnectedComponent → ℤ := fun c => cycleResolventAt d (r c)
  have hprod_toList (s : Finset D.ConnectedComponent) :
      (s.toList.map fZ).prod = ∏ c ∈ s, fZ c := by
    calc
      (s.toList.map fZ).prod = s.toList.toFinset.prod fZ :=
        (List.prod_toFinset fZ s.nodup_toList).symm
      _ = s.prod fZ := by rw [s.toList_toFinset]
  have hprodZ : (rs.map (cycleResolventAt d)).prod =
      Matrix.det (Matrix.scalar V ((d : ℤ) - 1) - D.adjMatrix ℤ) := by
    calc
      (rs.map (cycleResolventAt d)).prod =
          ((Finset.univ : Finset D.ConnectedComponent).toList.map fZ).prod := by
            dsimp only [rs, fZ]
            rw [List.map_map]
            apply congrArg List.prod
            apply List.map_congr_left
            intro c hc
            rfl
      _ = ∏ c : D.ConnectedComponent, fZ c := by
        exact hprod_toList (Finset.univ : Finset D.ConnectedComponent)
      _ = ∏ c : D.ConnectedComponent,
          (C ℤ (r c : ℤ) - 2).eval ((d : ℤ) - 1) := by
            apply Finset.prod_congr rfl
            intro c hc
            rfl
      _ = Matrix.det (Matrix.scalar V ((d : ℤ) - 1) - D.adjMatrix ℤ) :=
        hfactorZ.symm
  let MZ := Matrix.scalar V ((d : ℤ) - 1) - D.adjMatrix ℤ
  let MQ := (d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ
  have hscalarMap : (Int.castRingHom ℚ).mapMatrix
      (Matrix.scalar V ((d : ℤ) - 1)) = Matrix.scalar V ((d : ℚ) - 1) := by
    change (Matrix.diagonal (fun _ : V => (d : ℤ) - 1)).map
      (Int.castRingHom ℚ) = Matrix.diagonal (fun _ : V => (d : ℚ) - 1)
    rw [Matrix.diagonal_map (by norm_num)]
    congr 1
    funext x
    norm_num
  have hadjMap : (Int.castRingHom ℚ).mapMatrix (D.adjMatrix ℤ) =
      D.adjMatrix ℚ := by
    ext x y
    by_cases hadj : D.Adj x y <;>
      simp [RingHom.mapMatrix_apply, SimpleGraph.adjMatrix_apply, hadj]
  have hsmulScalar : (d - 1 : ℚ) • (1 : Matrix V V ℚ) =
      Matrix.scalar V ((d : ℚ) - 1) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, hxy]
  have hmap : (Int.castRingHom ℚ).mapMatrix MZ = MQ := by
    dsimp only [MZ, MQ]
    rw [hsmulScalar]
    ext x y
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    change (Int.castRingHom ℚ)
        (((Matrix.scalar V ((d : ℤ) - 1) - D.adjMatrix ℤ) x y)) =
      (Matrix.scalar V ((d : ℚ) - 1) - D.adjMatrix ℚ) x y
    rw [Matrix.sub_apply, (Int.castRingHom ℚ).map_sub, Matrix.sub_apply]
    rw [show (Int.castRingHom ℚ)
          ((Matrix.scalar V ((d : ℤ) - 1)) x y) =
          (Matrix.scalar V ((d : ℚ) - 1)) x y from
        congrFun (congrFun hscalarMap x) y,
      show (Int.castRingHom ℚ) ((D.adjMatrix ℤ) x y) =
          (D.adjMatrix ℚ) x y from congrFun (congrFun hadjMap x) y]
  have hdetcast : ((Matrix.det MZ : ℤ) : ℚ) = Matrix.det MQ := by
    exact (RingHom.map_det (Int.castRingHom ℚ) MZ).trans
      (congrArg Matrix.det hmap)
  obtain ⟨q, hq⟩ := secondOrder_defect_resolvent_is_square_mul
    G hfree hd heven hmin hcard
  have hq' : Matrix.det MQ = (d - 3 : ℚ) * q ^ 2 := by
    exact hq
  have hfactorQ : (((rs.map (cycleResolventAt d)).prod : ℤ) : ℚ) =
      (d - 3 : ℚ) * q ^ 2 := by
    calc
      (((rs.map (cycleResolventAt d)).prod : ℤ) : ℚ) =
          ((Matrix.det MZ : ℤ) : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) hprodZ
      _ = Matrix.det MQ := hdetcast
      _ = (d - 3 : ℚ) * q ^ 2 := hq'
  have hdet0 := secondOrder_scalar_sub_defect_det_ne_zero
    G hfree hd heven hmin hcard
  have hdet0' : Matrix.det MQ ≠ 0 := hdet0
  have hprod0 : (rs.map (cycleResolventAt d)).prod ≠ 0 := by
    intro hz
    apply hdet0'
    rw [← hdetcast, ← hprodZ, hz]
    norm_num
  exact evenCycleCount_even_of_odd_sum_and_square_factorization
    d hd rs hodd q hfactorQ hprod0


end Erdos85
