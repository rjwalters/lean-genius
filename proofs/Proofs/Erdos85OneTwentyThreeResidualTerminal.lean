import Proofs.Erdos85AbstractTraceEscape
import Proofs.Erdos85OneTwentyThreeTraceEscape
import Proofs.Erdos85SymmetricRestrictionSemisimple
import Proofs.Erdos85OneTwentyThreeArithmetic
import Proofs.Erdos85ExteriorCharpolyDivisibility
import Proofs.Erdos85OneTwentyThreeSemisimplePackage
import Proofs.Erdos85OwnerFiberProjectedSquare

/-!
# Scalar-123 residual terminal

The operator theorem below is the final contradiction engine.  The graph
wrapper transports the saturated owner-fiber hard sector into this engine.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- **Operator-level scalar-123 terminal.**  Semisimplicity peels the
designated eigenvalue `2`; trace `-135` forces the residual trace nonzero,
while the arithmetic hypothesis and abstract trace escape force it zero. -/
theorem false_of_oneTwentyThree_semisimple_residual
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (hsq : S * S = (123 : ℚ) • (1 : E →ₗ[ℚ] E) - T)
    (htrace : LinearMap.trace ℚ E S = -(135 : ℚ))
    (hsemi : Module.End.IsSemisimple T)
    (harith : ∀ f : ℚ[X], f.Monic → Irreducible f → f ∣ T.charpoly →
      f ≠ X - C (2 : ℚ) → ¬ IsSquare (f.eval 123)) : False := by
  obtain ⟨r, hr2, hcop, hann, hrdvd⟩ :=
    exists_coprime_residual_annihilator_of_isSemisimple T hsemi 2
  have hne := residual_trace_ne_zero_of_sq_oneTwentyThree_of_trace_neg135
    S T hcomm r hcop hann hsq htrace
  have hzero := abstract_residual_trace_eq_zero
    S T hcomm hsq (LinearMap.aeval_self_charpoly T) hr2 hrdvd harith
  exact hne hzero

/-- **Graph-facing d=124 saturated terminal.**  A saturated `(124,12)`
minimum layer cannot exist: its canonical 112-fiber hard sector produces
the contradictory scalar-123 residual traces. -/
theorem no_minimumLayer_saturated_124_hardSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 124 ≤ G.minDegree)
    (hcard : Fintype.card V = 124 * (124 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 12)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        12 * (12 - 1) + 3) : False := by
  classical
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
  let P := (D.comap (fun z : X => z.1)).adjMatrix ℚ
  have hhard := exists_minimumLayer_saturated_124_hardSector_square
    G hfree hmin hcard c₀ hregChild hcardChild
  obtain ⟨owner, huniform, hcommAE, hcommPE, htrace, hsq⟩ := hhard
  let E := normalizedOwnerProjection (K := ℚ) owner 112
  let Q : Matrix X X ℚ := 1 - E
  have hQ : Q * Q = Q := by
    simpa [Q, E, IsIdempotentElem] using
      (complement_normalizedOwnerProjection_isIdempotent
        (K := ℚ) owner 112 (by norm_num) huniform)
  have hcommAQ : A * Q = Q * A := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcommAE]
  have hcommPQ : P * Q = Q * P := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcommPE]
  have hPsymm : P.IsSymm := SimpleGraph.isSymm_adjMatrix _
  have hpkg := range_restrict_oneTwentyThree_semisimple_package
    A P Q hPsymm hQ hcommAQ hcommPQ htrace hsq
  dsimp only at hpkg
  obtain ⟨htraceR, hsqR, hcommR, hsemiR⟩ := hpkg
  apply false_of_oneTwentyThree_semisimple_residual _ _
    hcommR hsqR htraceR hsemiR
  intro f hfmonic hfirr hfdvd hfne
  obtain ⟨c, hc3, hcmax, hfcycle⟩ :=
    exteriorHardSector_irreducible_dvd_cycleChebyshev
      G hfree (d := 124) (by norm_num) (by exact ⟨62, by norm_num⟩)
        hmin hcard c₀ Q hQ hcommPQ f hfirr hfdvd
  have hcmax' : c.supp.ncard ≤ 15255 := by
    norm_num at hcard
    rwa [hcard] at hcmax
  exact oneTwentyThree_cycleFactor_eval_nonsquare_except_two
    c.supp.ncard hc3 hcmax' f hfmonic hfirr hfcycle hfne

/-- **Unconditional sharp minimum-layer descent.**  The scalar-123
terminal removes the final `(d,s)=(124,12)` saturated residual from
`secondOrder_minimumLayer_gap_or_degree_oneTwentyFour`. -/
theorem secondOrder_minimumLayer_strict_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hd4 : d ≠ 4) (hd12 : d ≠ 12)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧ s < d ∧ s * (s - 1) + 4 ≤ d := by
  obtain ⟨s, hreg, hcardChild, hsEven, hsd, hbranch⟩ :=
    secondOrder_minimumLayer_gap_or_degree_oneTwentyFour
      G hfree hd heven hmin hcard hd4 hd12 c₀ hc₀min
  refine ⟨s, hreg, hcardChild, hsEven, hsd, ?_⟩
  rcases hbranch with hresidual | hgap
  · obtain ⟨rfl, rfl, hc₀three, hcount⟩ := hresidual
    exact False.elim (no_minimumLayer_saturated_124_hardSector
      G hfree hmin hcard c₀ hreg hcardChild)
  · exact hgap

/-- At ambient degree sixteen, unconditional sharp descent leaves only the
three even child degrees `0`, `2`, and `4`. -/
theorem secondOrder_degree_sixteen_minimumLayer_degree_zero_two_or_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (s = 0 ∨ s = 2 ∨ s = 4) ∧
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 := by
  obtain ⟨s, hreg, hcardChild, hsEven, hsd, hgap⟩ :=
    secondOrder_minimumLayer_strict_gap G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard (by norm_num) (by norm_num)
        c₀ hc₀min
  obtain ⟨k, hk⟩ := hsEven
  have hcases : s = 0 ∨ s = 2 ∨ s = 4 := by
    interval_cases s <;> norm_num at hgap <;> omega
  exact ⟨s, hcases, hreg, hcardChild⟩

end

end Erdos85
