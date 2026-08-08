import Proofs.Erdos85MinimumLayerGramMatrix
import Proofs.Erdos85MinimumLayerDesignMatrix

/-!
# The minimum-layer design equation, instantiated

The restricted quotient matrix of the minimum layer satisfies the abstract
design-matrix hypotheses: it is symmetric, its square is the design matrix,
and every entry is strictly below the minimum order.  The rigidity theorem
then yields a common row sum `s` with the scalar quadratic

`s² + 3 = u·w + s`,

where `u` is the number of minimum-layer components and `w` the minimum
order — the same quadratic-boundary form as `n = d(d-1) + 3` one level
down.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **The design scalar of the minimum layer.**  All restricted row sums
agree, and the common value satisfies `s² + 3 = u·w + s`. -/
theorem secondOrder_minimumLayer_design_scalar
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
      (∀ c ∈ Finset.univ.filter
          (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
            x.supp.ncard = c₀.supp.ncard),
        (∑ e ∈ Finset.univ.filter
            (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
              x.supp.ncard = c₀.supp.ncard),
          (componentQuotientMatrix G (secondOrderDefectGraph G) c e : ℤ)) =
            s) ∧
      s * s + 3 =
        ((Finset.univ.filter
          (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
            x.supp.ncard = c₀.supp.ncard)).card : ℤ) *
          (c₀.supp.ncard : ℤ) + s := by
  classical
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun x ↦ x.supp.ncard = c₀.supp.ncard) with hM
  set QM := componentQuotientMatrix G (secondOrderDefectGraph G) with hQM
  have hmemSize : ∀ e ∈ M, e.supp.ncard = c₀.supp.ncard := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hc₀M : c₀ ∈ M := by
    rw [hM]
    simp
  -- The minimum order is at least three.
  obtain ⟨uLab, -, -, -, hthree⟩ :=
    exists_mixed_cycle_labeling G hfree hd heven hmin hcard
  have hw3 : 3 ≤ c₀.supp.ncard := hthree c₀
  -- The restricted matrix on the subtype of the minimum layer.
  letI : Nonempty ↥M := ⟨⟨c₀, hc₀M⟩⟩
  set R : Matrix ↥M ↥M ℤ :=
    fun i j ↦ (QM i.1 j.1 : ℤ) with hR
  set w : ℤ := (c₀.supp.ncard : ℤ) with hw
  -- Symmetry.
  have hsymm : R.IsSymm := by
    apply Matrix.ext
    intro i j
    rw [Matrix.transpose_apply]
    show (QM j.1 i.1 : ℤ) = (QM i.1 j.1 : ℤ)
    have := componentQuotientMatrix_symm_of_ncard_eq
      G hfree hd heven hmin hcard j.1 i.1
        ((hmemSize j.1 j.2).trans (hmemSize i.1 i.2).symm)
    rw [← hQM] at this
    exact_mod_cast this
  -- Row sums of the restricted matrix are the restricted quotient rows.
  have hrowSum : ∀ i : ↥M,
      minimumLayerRowSum R i = ∑ e ∈ M, (QM i.1 e : ℤ) := by
    intro i
    rw [minimumLayerRowSum]
    exact Finset.sum_coe_sort M (fun e ↦ (QM i.1 e : ℤ))
  -- The square is the design matrix.
  have hsq : R * R = minimumLayerDesignMatrix R w := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply]
    have hsum : (∑ k : ↥M, R i k * R k j) =
        ∑ e ∈ M, (QM e i.1 : ℤ) * (QM e j.1 : ℤ) := by
      calc
        (∑ k : ↥M, R i k * R k j) =
            ∑ e ∈ M, (QM i.1 e : ℤ) * (QM e j.1 : ℤ) :=
          Finset.sum_coe_sort M
            (fun e ↦ (QM i.1 e : ℤ) * (QM e j.1 : ℤ))
        _ = ∑ e ∈ M, (QM e i.1 : ℤ) * (QM e j.1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro e he
          have := componentQuotientMatrix_symm_of_ncard_eq
            G hfree hd heven hmin hcard i.1 e
              ((hmemSize i.1 i.2).trans (hmemSize e he).symm)
          rw [← hQM] at this
          congr 1
          exact_mod_cast this
    by_cases hij : i = j
    · subst hij
      have hdiag := secondOrder_minimumLayer_gramSquare_diag
        G hfree hd heven hmin hcard c₀ hc₀min i.1 (hmemSize i.1 i.2)
      rw [← hQM, ← hM] at hdiag
      rw [hsum]
      simp only [minimumLayerDesignMatrix, if_pos rfl]
      rw [hrowSum i]
      rw [hdiag]
      rw [hw]
      simp only [if_true]
      ring
    · have hne : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
      have hoff := secondOrder_minimumLayer_gramSquare_offDiag
        G hfree hd heven hmin hcard c₀ hc₀min i.1 j.1
          (hmemSize i.1 i.2) (hmemSize j.1 j.2) hne
      rw [← hQM, ← hM] at hoff
      rw [hsum]
      simp only [minimumLayerDesignMatrix, if_neg hij, add_zero]
      rw [hw]
      calc
        (∑ e ∈ M, (QM e i.1 : ℤ) * (QM e j.1 : ℤ)) =
            ((∑ e ∈ M, QM e i.1 * QM e j.1 : ℕ) : ℤ) := by
          push_cast
          rfl
        _ = (c₀.supp.ncard : ℤ) := by
          exact_mod_cast hoff
  -- Every entry is strictly below the minimum order.
  have hlt : ∀ i j : ↥M, R i j < w := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hdle := secondOrder_minimumLayer_diag_le_two
        G hfree hd heven hmin hcard c₀ hc₀min i.1 (hmemSize i.1 i.2)
      rw [← hQM] at hdle
      show (QM i.1 i.1 : ℤ) < w
      rw [hw]
      have h2 : (QM i.1 i.1 : ℤ) ≤ 2 := by exact_mod_cast hdle
      have h3 : (3 : ℤ) ≤ (c₀.supp.ncard : ℤ) := by exact_mod_cast hw3
      linarith
    · have hne : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
      have hltQ := componentQuotientMatrix_lt_ncard_of_ne
        G hfree hd heven hmin hcard i.1 j.1 hne
        (by rw [hmemSize i.1 i.2]; omega)
        (by rw [hmemSize j.1 j.2]; omega)
      rw [← hQM] at hltQ
      show (QM i.1 j.1 : ℤ) < w
      rw [hw]
      rw [hmemSize j.1 j.2] at hltQ
      exact_mod_cast hltQ
  -- Rigidity: the row sums agree; the scalar quadratic follows.
  have hconst := minimumLayer_rowSum_eq_of_sq_eq_design R w hsymm hsq hlt
  set s : ℤ := minimumLayerRowSum R ⟨c₀, hc₀M⟩ with hs
  have hrow : ∀ i : ↥M, minimumLayerRowSum R i = s :=
    fun i ↦ hconst i ⟨c₀, hc₀M⟩
  have hscalar := minimumLayer_design_scalar_of_constant_rowSum
    R w s hsq hrow
  refine ⟨s, ?_, ?_⟩
  · intro c hc
    have := hrow ⟨c, hc⟩
    rw [hrowSum ⟨c, hc⟩] at this
    exact this
  · rw [Fintype.card_coe] at hscalar
    rw [hw] at hscalar
    exact hscalar

end

end Erdos85
