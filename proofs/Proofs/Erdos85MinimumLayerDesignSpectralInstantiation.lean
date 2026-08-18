import Proofs.Erdos85MinimumLayerGramMatrix
import Proofs.Erdos85MinimumLayerDesignSpectral

/-!
# The nonsquare spectral refinement, instantiated

When the design scalar `s` has nonsquare transverse part `s - 3`, the
spectral trace argument bounds it by twice the number of minimum-layer
components, and the design equation then squeezes the minimum order:

`s ≤ 2u` and `w ≤ 2s`.

The minimum sector in the nonsquare branch is tall and narrow: many small
components.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Nonsquare branch: the minimum sector is tall and narrow.**  If the
common restricted row sum `s ≥ 3` has nonsquare `s - 3`, and the minimum
layer has more than one component, then `s ≤ 2u` and `w ≤ 2s`. -/
theorem secondOrder_minimumLayer_nonsquare_narrow
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
      c₀.supp.ncard ≤ e.supp.ncard)
    (hu2 : 1 < (Finset.univ.filter
      (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
        x.supp.ncard = c₀.supp.ncard)).card)
    {s : ℕ} (hs3 : 3 ≤ s)
    (hrowsum : ∀ c ∈ Finset.univ.filter
        (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
          x.supp.ncard = c₀.supp.ncard),
      (∑ e ∈ Finset.univ.filter
          (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
            x.supp.ncard = c₀.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) c e) = s)
    (hdesign : s * s + 3 =
      (Finset.univ.filter
        (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
          x.supp.ncard = c₀.supp.ncard)).card * c₀.supp.ncard + s)
    (hnonsq : ¬ IsSquare (s - 3)) :
    s ≤ 2 * (Finset.univ.filter
        (fun x : (secondOrderDefectGraph G).ConnectedComponent ↦
          x.supp.ncard = c₀.supp.ncard)).card ∧
      c₀.supp.ncard ≤ 2 * s := by
  classical
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun x ↦ x.supp.ncard = c₀.supp.ncard) with hM
  set QM := componentQuotientMatrix G (secondOrderDefectGraph G) with hQM
  have hmemSize : ∀ e ∈ M, e.supp.ncard = c₀.supp.ncard := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty ↥M := ⟨⟨hMne.choose, hMne.choose_spec⟩⟩
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
  -- Row sums.
  have hrowSum : ∀ i : ↥M,
      minimumLayerRowSum R i = ∑ e ∈ M, (QM i.1 e : ℤ) := by
    intro i
    rw [minimumLayerRowSum]
    exact Finset.sum_coe_sort M (fun e ↦ (QM i.1 e : ℤ))
  have hrow : ∀ i : ↥M, minimumLayerRowSum R i = (s : ℤ) := by
    intro i
    rw [hrowSum i]
    have := hrowsum i.1 i.2
    calc
      (∑ e ∈ M, (QM i.1 e : ℤ)) = ((∑ e ∈ M, QM i.1 e : ℕ) : ℤ) := by
        push_cast
        rfl
      _ = (s : ℤ) := by exact_mod_cast this
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
  -- Diagonal bound.
  have hdiag2 : ∀ i : ↥M, R i i ≤ 2 := by
    intro i
    have := secondOrder_minimumLayer_diag_le_two
      G hfree hd heven hmin hcard c₀ hc₀min i.1 (hmemSize i.1 i.2)
    rw [← hQM] at this
    show (QM i.1 i.1 : ℤ) ≤ 2
    exact_mod_cast this
  -- The spectral trace bound.
  have hcardM : 1 < Fintype.card ↥M := by
    rw [Fintype.card_coe]
    exact hu2
  have htraceZ := minimumLayer_rowSum_le_two_mul_card_of_nonsquare
    R w s hs3 hcardM hsymm hsq hrow hnonsq hdiag2
  rw [Fintype.card_coe] at htraceZ
  have htrace : s ≤ 2 * M.card := by exact_mod_cast htraceZ
  refine ⟨htrace, ?_⟩
  have hdesign' : s * s + 3 = M.card * c₀.supp.ncard + s := hdesign
  exact minimumLayer_order_le_two_mul_rowSum M.card c₀.supp.ncard s hs3
    hdesign' htrace

end

end Erdos85
