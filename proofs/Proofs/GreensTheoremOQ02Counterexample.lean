/-
  Counterexample: `greens_theorem_l1curl` is FALSE as currently stated
  ====================================================================

  Open question: greens-theorem-oq-02-oq-02
  Main file:     proofs/Proofs/GreensTheoremOQ02.lean  (axiom at line ~361)

  STATUS: build-pending, UNREGISTERED (Docker verification blackout 2026-06-15).
  This file is NOT added to the gallery / lakefile registration; it is an
  artifact documenting an integrity defect in the stated axiom, to be
  compile-checked when Docker is restored.

  ----------------------------------------------------------------------
  The finding
  ----------------------------------------------------------------------
  Five prior research sessions reduced the discharge of `greens_theorem_l1curl`
  to a SINGLE upstream keystone — the function-level FTC for absolutely
  continuous functions (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`,
  Mathlib v4.28.0) — and a Fubini reduction of the RHS double integral. The
  recommended discharge blueprint's step 4 assumed the LHS line integral could
  be assembled from "OQ01's boundary algebra" for free.

  That assumption is WRONG, and as a result the axiom is FALSE as stated. The
  only hypothesis linking the abstract curve `C : LipschitzClosedCurve` to the
  rectangle is

      hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Icc a b ×ˢ Icc c d)

  i.e. *image containment* in the boundary. This does NOT encode

    * orientation (counterclockwise vs clockwise — a global sign),
    * winding number / single traversal (the curve may wind k times),
    * non-degeneracy (the curve may collapse to a single boundary point).

  OQ01 (`GreensTheoremOQ01.lean`) never relates an abstract curve to the
  boundary: it *defines* its line integral as an explicitly oriented four-edge
  sum (`rectLineIntegral`, line 76). So there is no reusable
  "curve ⟹ four edges" lemma; that reduction is a genuine SECOND gap, and the
  reduction is simply false under the weak `hTraversal`.

  ----------------------------------------------------------------------
  The counterexample (degenerate curve)
  ----------------------------------------------------------------------
  Take the constant curve  γ ≡ (0,0)  on the unit square [0,1]×[0,1], with the
  field  P = 0,  Q(x,y) = x,  whose curl is  ∂Q/∂x − ∂P/∂y = 1  everywhere.

    * It is a legitimate `LipschitzClosedCurve` (0-Lipschitz, closed).
    * `hCurlAE`, `hL1`, `hTraversal` all hold ((0,0) is a corner of the
      square, hence on its frontier).
    * Yet the line integral is 0 (the curve has zero velocity), while the
      double integral of the curl is the area = 1.

  So the axiom forces  0 = 1.  The correct formalization must strengthen
  `hTraversal` to "C is a positively-oriented simple parametrization of the
  rectangle boundary" — e.g. assume `lipschitzLineIntegral P Q C =
  rectLineIntegral P Q a b c d` and discharge THAT via OQ01 — which is itself a
  nontrivial reparametrization-invariance fact, NOT covered by the Mathlib bump.
-/
import Mathlib
import Proofs.GreensTheoremOQ02

namespace GreensTheoremOQ02Counterexample

open MeasureTheory intervalIntegral Real
open GreensTheoremOQ02

/-- The degenerate constant curve `γ ≡ (0,0)`, a valid `LipschitzClosedCurve`
    (0-Lipschitz, closed) whose image is the single corner `(0,0)` of the unit
    square. -/
noncomputable def constCurve : LipschitzClosedCurve where
  T := 1
  γ := fun _ => (0, 0)
  hT := by norm_num
  K := 0
  hLip := LipschitzWith.const _
  isClosed := rfl

/-- The counterexample vector field: `P = 0`, `Q(x,y) = x`, with curl `≡ 1`. -/
noncomputable def cexP : ℝ × ℝ → ℝ := fun _ => 0
noncomputable def cexQ : ℝ × ℝ → ℝ := fun p => p.1
noncomputable def cexCurl : ℝ × ℝ → ℝ := fun _ => 1

/-- The line integral over the degenerate (zero-velocity) curve vanishes: the
    derivatives of both constant coordinate functions are 0, so the integrand
    is identically 0. This is the crux — a curve satisfying `hTraversal` need
    not contribute the boundary integral at all. -/
theorem constCurve_lineIntegral_zero :
    lipschitzLineIntegral cexP cexQ constCurve = 0 := by
  simp [lipschitzLineIntegral, constCurve]

/-- `hTraversal` is satisfied: the constant image `(0,0)` is a corner of the
    unit square and hence lies on its frontier, for every parameter `t`. -/
theorem constCurve_hTraversal :
    ∀ t ∈ Set.Icc (0 : ℝ) constCurve.T,
      constCurve.γ t ∈ frontier (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro t _
  show ((0 : ℝ), (0 : ℝ)) ∈ frontier (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
  rw [frontier_prod_eq]
  refine Or.inl ⟨subset_closure ?_, ?_⟩
  · exact ⟨le_refl 0, by norm_num⟩
  · rw [frontier_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.mem_insert _ _

/-- `hCurlAE` is satisfied (in fact the curl identity holds everywhere, not
    just a.e.): `∂Q/∂x = 1` and `∂P/∂y = 0`. -/
theorem cex_hCurlAE :
    ∀ᵐ p ∂(volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)),
      cexCurl p = deriv (fun x => cexQ (x, p.2)) p.1 -
                  deriv (fun y => cexP (p.1, y)) p.2 := by
  refine ae_of_all _ (fun p => ?_)
  simp only [cexCurl, cexQ, cexP, deriv_id'']
  rw [deriv_const]
  norm_num

/-- `hL1` is satisfied: the curl is the constant `1` on the compact rectangle,
    which has finite measure. -/
theorem cex_hL1 :
    IntegrableOn cexCurl (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) volume := by
  apply integrableOn_const.mpr
  exact Or.inr (isCompact_Icc.prod isCompact_Icc).measure_lt_top

/-- The double integral of the (unit) curl over the open square is its area,
    `1` — nonzero, unlike the line integral. -/
theorem cexCurl_double_integral :
    (∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1, cexCurl p ∂volume) = 1 := by
  have hvol : volume (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) = 1 := by
    rw [volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    norm_num
  simp [cexCurl, setIntegral_const, hvol]

/-- **Refutation.** The axiom `greens_theorem_l1curl`, applied to the degenerate
    constant curve and the curl-1 field above (all of whose hypotheses are
    discharged), forces `0 = 1`. Hence the axiom as currently stated in
    `GreensTheoremOQ02.lean` is FALSE: `hTraversal` is too weak. -/
theorem greens_theorem_l1curl_refuted : (0 : ℝ) = 1 := by
  have hkey := greens_theorem_l1curl constCurve cexP cexQ cexCurl 0 1 0 1
      (by norm_num) (by norm_num) cex_hCurlAE cex_hL1 constCurve_hTraversal
  rw [constCurve_lineIntegral_zero, cexCurl_double_integral] at hkey
  exact hkey

end GreensTheoremOQ02Counterexample
