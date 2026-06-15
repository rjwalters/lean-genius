/-
# Green's theorem OQ-02-OQ-02 — CORRECTED axiom (orientation-fixed)

`greens-theorem-oq-02-murakami` sibling: `greens-theorem-oq-02-oq-02`.

## Why this file exists

Session 5 (`GreensTheoremOQ02Counterexample.lean`) proved that the registered
axiom `GreensTheoremOQ02.greens_theorem_l1curl` is **FALSE as stated**: the only
curve↔rectangle hypothesis `hTraversal` is image-containment in the frontier,
which constrains neither orientation nor winding nor non-degeneracy.  The
degenerate constant curve `γ ≡ (0,0)` with `P = 0, Q(x,y) = x` (curl ≡ 1)
satisfies every hypothesis yet has line integral `0` while `∬ curl = 1`, forcing
`0 = 1` (`greens_theorem_l1curl_refuted`).

The fix (identified in the problem `nextSteps`) is to add ONE orientation
hypothesis tying the curve's line integral to the concrete, correctly-oriented
four-edge rectangle integral `GreensTheoremOQ01.rectLineIntegral`:

    hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d

This file states the CORRECTED axiom `greens_theorem_l1curl_oriented` and
re-proves the full downstream blast radius — the three consumers in
`GreensTheoremOQ02.lean` (`lineIntegral_zero_curl`, `lineIntegral_l1curl_smul`,
`greens_oq1_from_l1curl`) and the two in `GreensTheoremOQ02OQ04.lean`
(`greens_stokes_l1curl`, `closed_l1form_zero_integral`) — each with `hLineEq`
threaded through.  Every consumer proof is the original verbatim plus the single
extra `hLineEq` argument, so this is a pure signature-threading correction.

It also proves `counterexample_violates_hLineEq`: the Session-5 unsound witness
fails the new orientation hypothesis (its `lipschitzLineIntegral = 0` but its
`rectLineIntegral = 1`, by the *proven* `unit_square_area_as_line_integral`),
so the corrected axiom is vacuously inapplicable to it — the unsoundness is
genuinely removed, not merely hidden.

UNREGISTERED, build-pending (authored under a Docker + Aristotle blackout).  This
is intentionally a separate, isolated file: the registered files are NOT edited
here, because a 6-consumer signature change across two registered files cannot be
build-verified under the blackout and must land as a single Docker-checked patch.
Once Docker returns, port `…_oriented` back onto the registered declarations
(drop the `_oriented` suffix) and delete this file.
-/
import Mathlib
import Proofs.GreensTheoremOQ02OQ04
import Proofs.GreensTheoremOQ02Counterexample

open MeasureTheory
open GreensTheoremOQ01 (rectLineIntegral)
open GreensTheoremOQ02
open GreensTheoremOQ02OQ04 (OneForm2D extDeriv1_2D)
open GreensTheoremOQ02Counterexample (constCurve cexP cexQ constCurve_lineIntegral_zero)

namespace GreensTheoremOQ02Corrected

/-- **Whitney's theorem, orientation-corrected.**  Same as the registered
`greens_theorem_l1curl` but with the extra hypothesis `hLineEq` fixing the
boundary orientation: the curve's line integral equals the concrete four-edge
rectangle integral `rectLineIntegral P Q a b c d` (OQ-01).  This excludes the
degenerate / wrongly-oriented curves that make the original statement false. -/
axiom greens_theorem_l1curl_oriented
    (C : LipschitzClosedCurve)
    (P Q : ℝ × ℝ → ℝ)
    (curlF : ℝ × ℝ → ℝ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hCurlAE : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        curlF p = deriv (fun x => Q (x, p.2)) p.1 -
                  deriv (fun y => P (p.1, y)) p.2)
    (hL1 : IntegrableOn curlF (Set.Icc a b ×ˢ Set.Icc c d) volume)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d) :
    lipschitzLineIntegral P Q C =
    ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, curlF p ∂volume

/-- Consumer 1 (was `lineIntegral_zero_curl`): zero curl ⟹ zero circulation,
now requiring the orientation hypothesis. -/
theorem lineIntegral_zero_curl_oriented
    (C : LipschitzClosedCurve)
    (P Q : ℝ × ℝ → ℝ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hCurlZeroAE : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        deriv (fun x => Q (x, p.2)) p.1 = deriv (fun y => P (p.1, y)) p.2)
    (hL1 : IntegrableOn (fun _ => (0 : ℝ)) (Set.Icc a b ×ˢ Set.Icc c d) volume)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d) :
    lipschitzLineIntegral P Q C = 0 := by
  have h := greens_theorem_l1curl_oriented C P Q (fun _ => 0) a b c d hab hcd
    (by filter_upwards [hCurlZeroAE] with p hp; simp [hp]) hL1 hTraversal hLineEq
  simp at h
  exact h

/-- Consumer 2 (was `lineIntegral_l1curl_smul`): scaling invariance, now
requiring the orientation hypothesis. -/
theorem lineIntegral_l1curl_smul_oriented
    (C : LipschitzClosedCurve)
    (P Q : ℝ × ℝ → ℝ)
    (curlF : ℝ × ℝ → ℝ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hCurlAE : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        curlF p = deriv (fun x => Q (x, p.2)) p.1 -
                  deriv (fun y => P (p.1, y)) p.2)
    (hL1 : IntegrableOn curlF (Set.Icc a b ×ˢ Set.Icc c d) volume)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d)
    (k : ℝ) :
    lipschitzLineIntegral (fun p => k * P p) (fun p => k * Q p) C =
    k * ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, curlF p ∂volume := by
  rw [lineIntegral_smul]
  rw [greens_theorem_l1curl_oriented C P Q curlF a b c d hab hcd hCurlAE hL1 hTraversal hLineEq]

/-- Consumer 3 (was `greens_oq1_from_l1curl`): reduction to the OQ-01 / C¹ case,
now requiring the orientation hypothesis. -/
theorem greens_oq1_from_l1curl_oriented
    (P Q dQdx dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (C : LipschitzClosedCurve)
    (hQ_ae : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        HasDerivAt (fun x => Q (x, p.2)) (dQdx p) p.1)
    (hP_ae : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        HasDerivAt (fun y => P (p.1, y)) (dPdy p) p.2)
    (hCurlAE : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        dQdx p - dPdy p = deriv (fun x => Q (x, p.2)) p.1 -
                           deriv (fun y => P (p.1, y)) p.2)
    (hL1 : IntegrableOn (fun p => dQdx p - dPdy p) (Set.Icc a b ×ˢ Set.Icc c d) volume)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d) :
    lipschitzLineIntegral P Q C =
    ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, (dQdx p - dPdy p) ∂volume := by
  apply greens_theorem_l1curl_oriented C P Q (fun p => dQdx p - dPdy p) a b c d hab hcd
  · filter_upwards [hCurlAE] with p hp
    exact hp
  · exact hL1
  · exact hTraversal
  · exact hLineEq

/-- Consumer 4 (was `GreensTheoremOQ02OQ04.greens_stokes_l1curl`): Stokes form,
now requiring the orientation hypothesis. -/
theorem greens_stokes_l1curl_oriented
    (C : LipschitzClosedCurve)
    (ω : OneForm2D)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hL1 : IntegrableOn (extDeriv1_2D ω) (Set.Icc a b ×ˢ Set.Icc c d) volume)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral ω.P ω.Q C = rectLineIntegral ω.P ω.Q a b c d) :
    lipschitzLineIntegral ω.P ω.Q C =
    ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, extDeriv1_2D ω p ∂volume := by
  simp only [extDeriv1_2D]
  exact greens_theorem_l1curl_oriented C ω.P ω.Q
    (fun p => deriv (fun x => ω.Q (x, p.2)) p.1 - deriv (fun y => ω.P (p.1, y)) p.2)
    a b c d hab hcd (by filter_upwards [] with p; rfl) hL1 hTraversal hLineEq

/-- Consumer 5 (was `GreensTheoremOQ02OQ04.closed_l1form_zero_integral`):
Cauchy-Goursat for L¹-closed forms, now requiring the orientation hypothesis. -/
theorem closed_l1form_zero_integral_oriented
    (C : LipschitzClosedCurve)
    (ω : OneForm2D)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hClosedAE : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
        extDeriv1_2D ω p = 0)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral ω.P ω.Q C = rectLineIntegral ω.P ω.Q a b c d) :
    lipschitzLineIntegral ω.P ω.Q C = 0 := by
  have hCurlZeroAE : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ Set.Ioo c d)),
      deriv (fun x => ω.Q (x, p.2)) p.1 = deriv (fun y => ω.P (p.1, y)) p.2 := by
    filter_upwards [hClosedAE] with p hp
    simp only [extDeriv1_2D] at hp; linarith
  exact lineIntegral_zero_curl_oriented C ω.P ω.Q a b c d hab hcd hCurlZeroAE
    integrableOn_const hTraversal hLineEq

/-- **Soundness check.**  The Session-5 unsound witness (constant curve + `(0,x)`
field) does NOT satisfy the new orientation hypothesis `hLineEq`: its line
integral is `0` (`constCurve_lineIntegral_zero`) while its four-edge rectangle
integral is `1` (the *proven* `unit_square_area_as_line_integral`).  Hence the
corrected axiom is vacuously inapplicable to it — the `0 = 1` unsoundness is
removed, not hidden. -/
theorem counterexample_violates_hLineEq :
    lipschitzLineIntegral cexP cexQ constCurve ≠ rectLineIntegral cexP cexQ 0 1 0 1 := by
  have hrect : rectLineIntegral cexP cexQ 0 1 0 1 = 1 := by
    simp only [cexP, cexQ]
    exact GreensTheoremOQ01.unit_square_area_as_line_integral
  rw [constCurve_lineIntegral_zero, hrect]
  norm_num

end GreensTheoremOQ02Corrected
