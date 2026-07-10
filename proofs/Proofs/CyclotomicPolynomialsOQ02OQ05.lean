/-
Erdős Problem #1215 — cyclotomic restriction (OQ-02): cyclotomic polynomials are
explicit unit-circle witnesses to the negative answer.

Parent: `Proofs.Erdos1215Problem` asks whether, for every polynomial `P` with
`P(0) = 1` and all roots on the unit circle (`IsUnitCirclePolynomial P`), there is a
bounded-level path from `0` to `∞` inside `{z : |P(z)| < C}`
(`HasBoundedLevelPath P C`).  The parent file records the negative answer as the
black-box axiom `Erdos1215.maclane_1953`.

The companion `CyclotomicPolynomialsOQ02OQ01` proved that for the cyclotomic
polynomials `Φ_n` the level set `{z : |Φ_n(z)| < C}` is **bounded** for *every*
threshold `C`, so `Φ_n` admits no escape-to-`∞` path
(`not_hasBoundedLevelPath_cyclotomic`).  What was missing is the observation that
these `Φ_n` are themselves members of the parent hypothesis class: for `n ≥ 2` the
constant term of `Φ_n` is `1` (so `Φ_n(0) = 1`) and every root is a primitive
`n`-th root of unity, hence lies on the unit circle.

Combining the two facts, each `Φ_n` (`n ≥ 2`) is a *concrete arithmetic witness* to
the negative answer of Erdős #1215: a genuine unit-circle polynomial with no
bounded-level path, for every `C`.  In particular this lets us **re-derive the parent
conclusion `¬∃ C > 1, ∀ unit-circle P, HasBoundedLevelPath P C` without invoking the
`maclane_1953` axiom** — the single witness `Φ₂ = X + 1` already suffices, since its
level sets are compact for all `C`.

(This does not reproduce Mac Lane's deep labyrinth phenomenon, which lives in the
`C > 1` regime and forces paths near `0`; it only shows the literal
escape-to-`∞` formulation is already refuted by the compactness of cyclotomic
lemniscates, and identifies `Φ_n` as explicit members of the hypothesis class.)

Main results:
* `cyclotomic_eval_zero_eq_one`       : `Φ_n(0) = 1` for `n ≥ 2`.
* `norm_eq_one_of_isRoot_cyclotomic`  : every root of `Φ_n` has modulus `1`.
* `cyclotomic_isUnitCirclePolynomial` : `Φ_n` is an `IsUnitCirclePolynomial` (`n ≥ 2`).
* `cyclotomic_witness_no_path`        : explicit unit-circle witness with no path.
* `erdos_1215_via_cyclotomic`         : axiom-free re-derivation of the parent
                                        negative answer via the cyclotomic family.

All results are `0`-axiom / `0`-sorry (they do not depend on `maclane_1953`).
-/

import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ01

open Complex Polynomial

namespace CyclotomicPolynomialsOQ02OQ05

/-- **`Φ_n(0) = 1` for `n ≥ 2`.**
The value of a cyclotomic polynomial at the origin is its constant term, which equals
`1` whenever `2 ≤ n` (`Polynomial.cyclotomic_coeff_zero`). -/
theorem cyclotomic_eval_zero_eq_one (n : ℕ) (hn : 2 ≤ n) :
    (cyclotomic n ℂ).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero]
  exact cyclotomic_coeff_zero ℂ (by omega)

/-- **Every root of `Φ_n` lies on the unit circle.**
For `n ≥ 2`, if `z` is a root of `cyclotomic n ℂ` then `z` is a primitive `n`-th root
of unity (`isRoot_cyclotomic_iff`), hence `‖z‖ = 1`. -/
theorem norm_eq_one_of_isRoot_cyclotomic (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : (cyclotomic n ℂ).IsRoot z) : ‖z‖ = 1 := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero (n : ℂ) := ⟨by exact_mod_cast hn0⟩
  have hprim : IsPrimitiveRoot z n := (isRoot_cyclotomic_iff).1 hz
  exact hprim.norm'_eq_one hn0

/-- **Cyclotomic polynomials are unit-circle polynomials.**
For `n ≥ 2`, `Φ_n` satisfies `Φ_n(0) = 1` and has all roots on the unit circle, so it
belongs to the parent hypothesis class `Erdos1215.IsUnitCirclePolynomial`. -/
theorem cyclotomic_isUnitCirclePolynomial (n : ℕ) (hn : 2 ≤ n) :
    Erdos1215.IsUnitCirclePolynomial (cyclotomic n ℂ) :=
  ⟨cyclotomic_eval_zero_eq_one n hn, norm_eq_one_of_isRoot_cyclotomic n hn⟩

/-- **Explicit cyclotomic witness to the negative answer.**
For `n ≥ 2` and *any* threshold `C`, the cyclotomic polynomial `Φ_n` is a genuine
unit-circle polynomial that nonetheless admits no bounded-level path from `0` to `∞`
inside `{z : |Φ_n(z)| < C}`.  This packages the parent hypothesis membership with the
OQ-01 compactness obstruction into one concrete witness. -/
theorem cyclotomic_witness_no_path (n : ℕ) (hn : 2 ≤ n) (C : ℝ) :
    Erdos1215.IsUnitCirclePolynomial (cyclotomic n ℂ) ∧
      ¬ Erdos1215.HasBoundedLevelPath (cyclotomic n ℂ) C :=
  ⟨cyclotomic_isUnitCirclePolynomial n hn,
    CyclotomicPolynomialsOQ02OQ01.not_hasBoundedLevelPath_cyclotomic n (by omega) C⟩

/-- **Axiom-free re-derivation of the Erdős #1215 negative answer via cyclotomics.**
The parent theorem `Erdos1215.erdos_1215` obtains its witnesses from the black-box
axiom `maclane_1953`.  Here we reprove the same statement using only the concrete
cyclotomic family: the single polynomial `Φ₂ = X + 1` is a unit-circle polynomial
whose level sets are compact for *every* `C`, so it defeats any candidate constant.
This derivation does not depend on `maclane_1953`. -/
theorem erdos_1215_via_cyclotomic :
    ¬∃ C : ℝ, C > 1 ∧ ∀ P : ℂ[X], Erdos1215.IsUnitCirclePolynomial P →
      Erdos1215.HasBoundedLevelPath P C := by
  rintro ⟨C, _hC, hall⟩
  obtain ⟨hunit, hnopath⟩ := cyclotomic_witness_no_path 2 le_rfl C
  exact hnopath (hall _ hunit)

end CyclotomicPolynomialsOQ02OQ05
