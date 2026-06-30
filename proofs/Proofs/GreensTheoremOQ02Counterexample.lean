/-
  Counterexample data for the (now corrected) `greens_theorem_l1curl`
  ====================================================================

  Open question: greens-theorem-oq-02-oq-02
  Main file:     proofs/Proofs/GreensTheoremOQ02.lean  (axiom at line ~361)

  STATUS (2026-06-15, S10): the axiom has been CORRECTED. The registered
  `greens_theorem_l1curl` now carries the orientation hypothesis
  `hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d`, so the
  degenerate-curve counterexample below no longer refutes it — instead it FAILS
  `hLineEq` (see `GreensTheoremOQ02Corrected.counterexample_violates_hLineEq`).
  This file is still UNREGISTERED (not in Proofs.lean); it supplies the
  counterexample data the soundness witness consumes.

  ----------------------------------------------------------------------
  The original finding (motivation for the fix)
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

/-- The counterexample vector field: `P = 0`, `Q(x,y) = x` (curl `≡ 1`). -/
noncomputable def cexP : ℝ × ℝ → ℝ := fun _ => 0
noncomputable def cexQ : ℝ × ℝ → ℝ := fun p => p.1

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

/-
  Historical note. Earlier revisions of this file also carried
  `greens_theorem_l1curl_refuted : (0 : ℝ) = 1`, which fed this degenerate curve
  and the curl-1 field into the THEN-unsound axiom to force `0 = 1` (the finding
  that motivated the fix; see PR #24381). That theorem can no longer be stated:
  the registered axiom now requires the orientation hypothesis
  `hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d`, and this
  curve cannot satisfy it. The replacement is the soundness witness
  `GreensTheoremOQ02Corrected.counterexample_violates_hLineEq`, which proves
  exactly that `hLineEq` fails here — so the corrected axiom is vacuously
  inapplicable to the counterexample. The supporting facts above
  (`constCurve_lineIntegral_zero`, `constCurve_hTraversal`) remain the data that
  witness consumes.
-/

end GreensTheoremOQ02Counterexample
