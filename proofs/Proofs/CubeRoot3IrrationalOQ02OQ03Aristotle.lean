/-
  Aristotle companion for the Vahlen–Capelli entry
  (`cube-root-3-irrational-oq-02-oq-03`).

  Target: `vahlen_capelli_four` — the smallest genuine `4 ∣ n` case of the
  even-sufficiency direction, i.e. the *first* exponent at which the Sophie–Germain
  / `-4·K⁴` obstruction is the essential extra content beyond "a is not a square".
  Discharging it is the concrete next step toward the sole remaining `sorry` in the
  registered `CubeRoot3IrrationalOQ02OQ03.lean` (`vahlen_capelli`, the even `n ≥ 4`
  branch), which coincides with an explicit open `TODO` in
  `Mathlib/FieldTheory/KummerExtension.lean` (Lang, *Algebra*, VI §9).

  Why a companion. Both local verification paths are currently unavailable — the
  Docker build gate is failing on a corrupt containerd content store
  (`input/output error` on blobs) and the interactive Aristotle endpoint returns
  `Resource not found`. This companion isolates the obligation as a clean,
  self-contained `theorem … := by sorry` so the batch proof-search pipeline can
  attempt it remotely once infrastructure recovers, exactly as the repository's
  Aristotle workflow intends (`research/SORRY-CLASSIFICATION.md`).

  It imports the registered file so the already-proven helpers
  (`sophie_germain`, `factor_capelli`, `no_root_of_not_square_even`, …) are in
  scope; none are needed to *state* the target, but they give the prover ready
  building blocks.

  ---------------------------------------------------------------------------
  Complete elementary proof plan (checked by hand; all characteristics).
  ---------------------------------------------------------------------------
  Let `f = X⁴ − C a` (monic, `natDegree 4`, `f ≠ 0`).

  Step 1 — no linear factor.  If `a` is not a square then `f` has no root: a root
  `r` gives `r⁴ = a`, so `a = (r²)²` is a square.  (This is precisely
  `no_root_of_not_square_even` at `n = 4`.)  Hence in any factorisation `f = p·q`
  with both factors non-units, neither factor can have degree `1` or `3`
  (a degree-1 or degree-3 factor forces a linear factor, hence a root).

  Step 2 — reduce to two monic quadratics.  A non-unit factorisation must
  therefore be `(natDegree 2, natDegree 2)`.  Since `f` is monic,
  `leadingCoeff p · leadingCoeff q = 1`; rescale `p ↦ (C (leadingCoeff p)⁻¹)·p`
  and `q ↦ (C (leadingCoeff p))·q` to get two *monic* quadratics whose product is
  still `f`.  Write them as `X² + C u·X + C v` and `X² + C s·X + C t`.

  Step 3 — match coefficients of `X⁴ + 0·X³ + 0·X² + 0·X + C(−a)`:
      X³:  u + s = 0            ⟹  s = −u
      X²:  v + t + u·s = 0      ⟹  v + t = u²
      X¹:  u·t + v·s = 0        ⟹  u·(t − v) = 0
      X⁰:  v·t = −a
  Two cases from `u·(t − v) = 0`:

    • `u = 0`:  then `s = 0`, `t = −v`, and `v·t = −v² = −a`, so `a = v²`,
      contradicting `h1` at `b = v`.

    • `u ≠ 0`:  then `t = v`, so `2v = u²` and `v² = −a`, giving `a = −v²`.
      Put `b = u/2`.  Then
          4·b⁴ = 4·(u/2)⁴ = u⁴/4 = (u²)²/4 = (2v)²/4 = v²,
      hence `a = −v² = −(4·b⁴)`, contradicting `h2`.
      (In characteristic 2 the equation `2v = u²` becomes `u² = 0`, i.e. `u = 0`,
      so this case is vacuous; equivalently `−v² = v²` already forces `a = v²`,
      contradicting `h1`.)

  Either case contradicts the hypotheses, so `f` is irreducible.  ∎

  Once proved, the registered `vahlen_capelli` closes its `by_cases h4 : n = 4`
  branch with `vahlen_capelli_four (hcond.1 2 Nat.prime_two ⟨2, rfl⟩)
  (hcond.2 ⟨1, rfl⟩)`, shrinking its sole remaining `sorry` to even `n ≥ 6`.
-/

import Mathlib
import Proofs.CubeRoot3IrrationalOQ02OQ03

open Polynomial
open CubeRoot3IrrationalOQ02OQ03

namespace CubeRoot3IrrationalOQ02OQ03Aristotle

/-- **Vahlen–Capelli, the `n = 4` sufficiency case.** Over any field `K`, if `a` is
not a square (`∀ b, b² ≠ a`, condition (1) at the prime `p = 2 ∣ 4`) and `a` is not of
the form `−4b⁴` (`∀ b, a ≠ −(4·b⁴)`, condition (2), which fires because `4 ∣ 4`), then
`X⁴ − C a` is irreducible.

This is the smallest exponent at which the Sophie–Germain obstruction is essential:
`n = 2` needs only "not a square" (the `−4·K⁴` clause is vacuous since `4 ∤ 2`), whereas
`n = 4` needs *both* clauses.  It is the first genuine step of the even-sufficiency
direction that Mathlib leaves as an open `TODO` (Lang, *Algebra*, VI §9), and it holds
in every characteristic (see the proof plan in the file header). -/
theorem vahlen_capelli_four {K : Type*} [Field K] {a : K}
    (h1 : ∀ b : K, b ^ 2 ≠ a)
    (h2 : ∀ b : K, a ≠ -(4 * b ^ 4)) :
    Irreducible (X ^ 4 - C a) := by
  sorry

end CubeRoot3IrrationalOQ02OQ03Aristotle
