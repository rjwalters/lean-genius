import Proofs.Erdos85MinimumLayerDesignMatrix
import Proofs.Erdos85MinimumLayerGramMatrix

/-!
# The minimum defect layer is an integral design

The quotient matrix restricted to the components of minimum order has constant
row sum.  Consequently its number of components, minimum order, and common
row sum satisfy the same quadratic boundary equation as the original graph.
-/

namespace Erdos85

noncomputable section

open SimpleGraph Matrix

/-- The minimum-layer quotient has a common integral row sum satisfying the
quadratic design equation `s² + 3 = |M|w + s`. -/
theorem secondOrder_minimumLayer_design_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℤ,
      (∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        c.supp.ncard = c₀.supp.ncard →
          (∑ e ∈ Finset.univ.filter
              (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
                x.supp.ncard = c₀.supp.ncard),
            (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ)) = s) ∧
      s * s + 3 =
        ((Finset.univ.filter
          (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
            x.supp.ncard = c₀.supp.ncard)).card : ℤ) *
          (c₀.supp.ncard : ℤ) + s := by
  classical
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let M : Finset C := Finset.univ.filter
    (fun x : C ↦ x.supp.ncard = c₀.supp.ncard)
  let I := {c : C // c ∈ M}
  let R : Matrix I I ℤ := fun i j ↦
    (componentQuotientMatrix G (secondOrderDefectGraph G) i.1 j.1 : ℤ)
  let w : ℤ := c₀.supp.ncard
  have hc₀M : c₀ ∈ M := by simp [M]
  let i₀ : I := ⟨c₀, hc₀M⟩
  letI : Nonempty I := ⟨i₀⟩
  have hmem (i : I) : i.1.supp.ncard = c₀.supp.ncard := by
    exact (Finset.mem_filter.mp i.2).2
  have hsymm : R.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    dsimp [R, Matrix.transpose]
    exact_mod_cast componentQuotientMatrix_symm_of_ncard_eq
      G hfree hd heven hmin hcard j.1 i.1
        ((hmem j).trans (hmem i).symm)
  have hsq : R * R = minimumLayerDesignMatrix R w := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hdiag := secondOrder_minimumLayer_gramSquare_diag
        G hfree hd heven hmin hcard c₀ hc₀min i.1 (hmem i)
      have hprod :
          (R * R) i i = ∑ k : I,
            (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 i.1 : ℤ) *
              (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 i.1 : ℤ) := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [R]
        rw [componentQuotientMatrix_symm_of_ncard_eq
          G hfree hd heven hmin hcard i.1 k.1
            ((hmem i).trans (hmem k).symm)]
      have hdiagI :
          (∑ k : I,
            (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 i.1 : ℤ) *
              (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 i.1 : ℤ)) =
            w - 3 + ∑ e ∈ M,
              (componentQuotientMatrix G (secondOrderDefectGraph G) i.1 e : ℤ) := by
        calc
          _ = ∑ e ∈ M,
              (componentQuotientMatrix G (secondOrderDefectGraph G) e i.1 : ℤ) *
                (componentQuotientMatrix G (secondOrderDefectGraph G) e i.1 : ℤ) := by
              exact (Finset.sum_subtype M (fun _ ↦ Iff.rfl)
                (fun e : C ↦
                  (componentQuotientMatrix G (secondOrderDefectGraph G) e i.1 : ℤ) *
                    (componentQuotientMatrix G (secondOrderDefectGraph G) e i.1 : ℤ))).symm
          _ = _ := by simpa [M, w] using hdiag
      have hrowI : minimumLayerRowSum R i = ∑ e ∈ M,
          (componentQuotientMatrix G (secondOrderDefectGraph G) i.1 e : ℤ) := by
        change (∑ j : I,
          (componentQuotientMatrix G (secondOrderDefectGraph G) i.1 j.1 : ℤ)) = _
        exact (Finset.sum_subtype M (fun _ ↦ Iff.rfl)
          (fun e : C ↦
            (componentQuotientMatrix G (secondOrderDefectGraph G) i.1 e : ℤ))).symm
      rw [hprod, hdiagI]
      simp only [minimumLayerDesignMatrix, if_pos]
      rw [hrowI]
      ring
    · have hne : i.1 ≠ j.1 := by
        intro h
        exact hij (Subtype.ext h)
      have hoff := secondOrder_minimumLayer_gramSquare_offDiag
        G hfree hd heven hmin hcard c₀ hc₀min i.1 j.1
          (hmem i) (hmem j) hne
      have hprod :
          (R * R) i j = ∑ k : I,
            (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 i.1 : ℤ) *
              (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 j.1 : ℤ) := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [R]
        rw [componentQuotientMatrix_symm_of_ncard_eq
          G hfree hd heven hmin hcard i.1 k.1
            ((hmem i).trans (hmem k).symm)]
      have hoffI :
          (∑ k : I,
            (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 i.1 : ℤ) *
              (componentQuotientMatrix G (secondOrderDefectGraph G) k.1 j.1 : ℤ)) = w := by
        calc
          _ = ∑ e ∈ M,
              (componentQuotientMatrix G (secondOrderDefectGraph G) e i.1 : ℤ) *
                (componentQuotientMatrix G (secondOrderDefectGraph G) e j.1 : ℤ) := by
              exact (Finset.sum_subtype M (fun _ ↦ Iff.rfl)
                (fun e : C ↦
                  (componentQuotientMatrix G (secondOrderDefectGraph G) e i.1 : ℤ) *
                    (componentQuotientMatrix G (secondOrderDefectGraph G) e j.1 : ℤ))).symm
          _ = w := by
            have := congrArg (fun n : ℕ ↦ (n : ℤ)) hoff
            simpa [M, w] using this
      rw [hprod, hoffI]
      simp [minimumLayerDesignMatrix, hij]
  have hwthree : 3 ≤ c₀.supp.ncard := by
    obtain ⟨u, hu, huRange, huD, hthree⟩ :=
      exists_mixed_cycle_labeling G hfree hd heven hmin hcard
    exact hthree c₀
  have hlt : ∀ i j, R i j < w := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hle := secondOrder_minimumLayer_diag_le_two
        G hfree hd heven hmin hcard c₀ hc₀min i.1 (hmem i)
      dsimp [R, w]
      exact_mod_cast lt_of_le_of_lt hle (by omega : 2 < c₀.supp.ncard)
    · have hne : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
      have hi2 : 2 ≤ i.1.supp.ncard := by rw [hmem i]; omega
      have hj2 : 2 ≤ j.1.supp.ncard := by rw [hmem j]; omega
      have hbound := componentQuotientMatrix_lt_ncard_of_ne
        G hfree hd heven hmin hcard i.1 j.1 hne
          hi2 hj2
      dsimp [R, w]
      exact_mod_cast (hmem j ▸ hbound)
  have hrows := minimumLayer_rowSum_eq_of_sq_eq_design R w hsymm hsq hlt
  let s := minimumLayerRowSum R i₀
  have hrow : ∀ i, minimumLayerRowSum R i = s := fun i ↦ hrows i i₀
  refine ⟨s, ?_, ?_⟩
  · intro c hc
    have hcM : c ∈ M := by simp [M, hc]
    let i : I := ⟨c, hcM⟩
    have hi := hrow i
    dsimp [minimumLayerRowSum, R] at hi
    calc
      (∑ e ∈ Finset.univ.filter
          (fun x : C ↦ x.supp.ncard = c₀.supp.ncard),
        (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ)) =
          ∑ j : I,
            (componentQuotientMatrix G (secondOrderDefectGraph G) c j.1 : ℤ) := by
              exact Finset.sum_subtype M (fun _ ↦ Iff.rfl)
                (fun e : C ↦
                  (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ))
      _ = s := hi
  · have hscalar := minimumLayer_design_scalar_of_constant_rowSum R w s hsq hrow
    have hcardI : Fintype.card I = M.card := by simp [I]
    rw [hcardI] at hscalar
    simpa [M, w] using hscalar

/-- Natural-number form of the minimum-layer design equation. -/
theorem secondOrder_minimumLayer_design_equation_nat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        c.supp.ncard = c₀.supp.ncard →
          (∑ e ∈ Finset.univ.filter
              (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
                x.supp.ncard = c₀.supp.ncard),
            componentQuotientMatrix G (secondOrderDefectGraph G) c e) = s) ∧
      s * s + 3 =
        (Finset.univ.filter
          (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
            x.supp.ncard = c₀.supp.ncard)).card * c₀.supp.ncard + s := by
  classical
  obtain ⟨s, hrows, hscalar⟩ := secondOrder_minimumLayer_design_equation
    G hfree hd heven hmin hcard c₀ hc₀min
  let M := Finset.univ.filter
    (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
      x.supp.ncard = c₀.supp.ncard)
  let sN := ∑ e ∈ M,
    componentQuotientMatrix G (secondOrderDefectGraph G) c₀ e
  have hc₀size : c₀.supp.ncard = c₀.supp.ncard := rfl
  have hsCast : (sN : ℤ) = s := by
    simpa [M, sN] using hrows c₀ hc₀size
  refine ⟨sN, ?_, ?_⟩
  · intro c hc
    have hr := hrows c hc
    rw [← hsCast] at hr
    exact_mod_cast hr
  · rw [← hsCast] at hscalar
    exact_mod_cast hscalar

/-- In particular, the number of minimum-order defect components is odd. -/
theorem secondOrder_minimumLayer_card_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    Odd (Finset.univ.filter
      (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
        x.supp.ncard = c₀.supp.ncard)).card := by
  obtain ⟨s, _hrows, hdesign⟩ := secondOrder_minimumLayer_design_equation_nat
    G hfree hd heven hmin hcard c₀ hc₀min
  exact minimumLayer_card_odd_of_design _ _ s hdesign

end

end Erdos85
