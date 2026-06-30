/-
# Green's theorem OQ-02-OQ-02 — soundness witness for the orientation fix

`greens-theorem-oq-02-murakami` sibling: `greens-theorem-oq-02-oq-02`.

## Status

The orientation correction this file originally prototyped is now **landed in the
registered files**: `GreensTheoremOQ02.greens_theorem_l1curl` and its consumers
(both in `GreensTheoremOQ02.lean` and `GreensTheoremOQ02OQ04.lean`) now carry the
extra orientation hypothesis

    hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d

tying the curve's circulation to the concrete, counterclockwise four-edge
rectangle integral `GreensTheoremOQ01.rectLineIntegral`.  The previously separate
`…_oriented` re-proofs in this file have therefore been deleted — they are now
identical to the registered declarations.

## Why this file remains

It keeps the **soundness witness** `counterexample_violates_hLineEq`: the
Session-5 unsound witness (constant curve `γ ≡ (0,0)` with field `(0, x)`, curl
`≡ 1`) does NOT satisfy the new orientation hypothesis.  Its circulation is `0`
(`constCurve_lineIntegral_zero`) while its four-edge rectangle integral is `1`
(the *proven* `unit_square_area_as_line_integral`).  Hence the corrected axiom is
vacuously inapplicable to it — the original `0 = 1` unsoundness is genuinely
removed by the new hypothesis, not merely hidden.

This is the converse-facing check that the registered fix actually excludes the
known counterexample.
-/
import Mathlib
import Proofs.GreensTheoremOQ02OQ04
import Proofs.GreensTheoremOQ02Counterexample

open MeasureTheory
open GreensTheoremOQ01 (rectLineIntegral)
open GreensTheoremOQ02
open GreensTheoremOQ02Counterexample (constCurve cexP cexQ constCurve_lineIntegral_zero)

namespace GreensTheoremOQ02Corrected

/-- **Soundness check for the registered orientation fix.**  The Session-5 unsound
witness (constant curve + `(0, x)` field) does NOT satisfy the orientation
hypothesis `hLineEq` now carried by the registered `greens_theorem_l1curl`: its
circulation is `0` (`constCurve_lineIntegral_zero`) while its four-edge rectangle
integral is `1` (the *proven* `unit_square_area_as_line_integral`).  Hence the
corrected axiom is vacuously inapplicable to it — the `0 = 1` unsoundness is
removed, not hidden. -/
theorem counterexample_violates_hLineEq :
    lipschitzLineIntegral cexP cexQ constCurve ≠ rectLineIntegral cexP cexQ 0 1 0 1 := by
  have hrect : rectLineIntegral cexP cexQ 0 1 0 1 = 1 :=
    GreensTheoremOQ01.unit_square_area_as_line_integral
  rw [constCurve_lineIntegral_zero, hrect]
  norm_num

end GreensTheoremOQ02Corrected
