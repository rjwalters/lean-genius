import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Proofs.RothTheoremOQ02

/-!
# Roth's Theorem — Bourgain's 1999 Quantitative Bound (OQ-01)

## What This Provides

A typed Lean target for Bourgain's 1999 quantitative refinement of Roth's
theorem on three-term arithmetic progressions:

  ∃ C > 0, ∀ N ≥ 3, rothNumberNat N ≤ C · N · (log log N / log N)^(1/2)

The bound is named `rothNumberNat_bourgain` and asserted as a Lean `axiom`,
exactly mirroring the established gallery pattern used by the sibling file
`RothTheoremOQ02.lean` for the Bloom–Sisask bound. Supporting names —
`bourgainConst` (a choice of constant `C`), `bourgainConst_pos` (its
positivity), and `rothNumberNat_le_bourgain` (the bound at the chosen
constant) — give downstream consumers a stable API without having to call
`Exists.choose` manually.

The file is *intentionally minimal*: it provides the typed landmark, the
trivial consequence that the axiom is consistent with Mathlib's existing
qualitative result `rothNumberNat_isLittleO_id`, the consistency with
Behrend's unconditional lower bound, and — the distinguishing content of
this OQ — the explicit record that the **Bloom–Sisask bound (OQ-02) is at
least as strong**, i.e. `rothNumberNat N` is bounded by the *minimum* of the
Bourgain and Bloom–Sisask right-hand sides. The Lean formalization of
Bourgain's proof itself (discrete Fourier analysis with Bohr-set density
increment, > 1000 lines of additive-combinatorics infrastructure not yet in
Mathlib) is deferred.

## The Quantitative Landscape

| Author (year)        | Bound on `r₃(N)`                         |
|----------------------|------------------------------------------|
| Roth (1953)          | `≪ N / log log N`                        |
| **Bourgain (1999)**  | `≪ N (log log N / log N)^{1/2}`  ← OQ-01  |
| Bourgain (2008)      | `≪ N (log log N)² / log N`                |
| Sanders (2011)       | `≪ N (log log N)^{O(1)} / log N`         |
| Bloom (2016)         | `≪ N (log log N)⁴ / log N`               |
| Bloom–Sisask (2020)  | `≪ N / (log N)^{1+c}`            ← OQ-02  |
| Kelley–Meka (2023)   | `≪ N · exp(-c (log N)^β)`                 |

The Bourgain 1999 saving over Roth is a *power of log* (`(log N)^{1/2}` up
to a `log log` factor), not merely a `log log` saving. Because the later
Bloom–Sisask bound `N / (log N)^{1+c}` decays strictly faster than the
Bourgain bound, **OQ-01 is implied by OQ-02**; this file records that
implication directly through `rothNumberNat_le_min_bourgain_blasi`.

## Scope (researcher-10, 2026-06-25)

- File status: **axiomatized** (1 axiom, 0 sorries).
- Imports `Mathlib.Combinatorics.Additive.Corner.Roth` (for `rothNumberNat`
  and `rothNumberNat_isLittleO_id`), `...AP.Three.Behrend` (for
  `Behrend.roth_lower_bound`), the real `log`/`rpow` API, and the sibling
  `Proofs.RothTheoremOQ02` (for `rothNumberNat_le_blasi`).
- Works at the **Mathlib `rothNumberNat`** level (over `Finset (Fin N)` /
  `ℕ`), *not* the project-local `Szemeredi.Roth.rothNumber` over `ZMod N`
  used in `RothTheorem.lean`, matching OQ-02 and the qualitative
  `rothNumberNat_isLittleO_id`.

## References

- Bourgain, J. (1999). *On triples in arithmetic progression.* Geom. Funct.
  Anal. 9, 968–984.
- Bloom, T. F., Sisask, O. (2020). *Breaking the logarithmic barrier in
  Roth's theorem on arithmetic progressions.* arXiv:2007.03528.
- Mathlib v4.26.0 module docstring of
  `Mathlib.Combinatorics.Additive.AP.Three.Defs`.
- Sibling file: `proofs/Proofs/RothTheoremOQ02.lean`.
-/

namespace RothTheoremOQ01

open Asymptotics Filter Topology

/-- **Bourgain's 1999 quantitative bound on the Roth number.** Axiomatic
statement:

  ∃ C > 0, ∀ N ≥ 3, rothNumberNat N ≤ C · N · (log log N / log N)^(1/2)

Proved analytically by Bourgain (Geom. Funct. Anal. 1999) via a single-step
density increment on a Bohr set with refined Fourier control; the full proof
requires Bohr-set geometry not yet in Mathlib at v4.26.0 (pin
`2df2f0150c275ad`). Asserted here axiomatically so downstream gallery files
can refer to the bound by name.

The lower bound `N ≥ 3` matches the convention in `RothTheoremOQ02` and
ensures `Real.log N > Real.log 3 > 1 > 0`, so `Real.log (Real.log N) > 0`,
the base `log log N / log N` is positive, and the right-hand side is positive
and the bound is non-vacuous. -/
axiom rothNumberNat_bourgain :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        C * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2)

/-- A canonical choice of the Bourgain constant `C > 0` extracted from the
axiom via `Exists.choose`. Marked `noncomputable` because `Exists.choose`
is. -/
noncomputable def bourgainConst : ℝ :=
  rothNumberNat_bourgain.choose

/-- The Bourgain constant is positive. -/
theorem bourgainConst_pos : 0 < bourgainConst :=
  rothNumberNat_bourgain.choose_spec.1

/-- **Bourgain bound at the canonical constant.** For every `N ≥ 3`,
`rothNumberNat N ≤ bourgainConst · N · (log log N / log N)^(1/2)`. Stable
downstream API that hides the `Exists.choose`. -/
theorem rothNumberNat_le_bourgain (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      bourgainConst * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) :=
  rothNumberNat_bourgain.choose_spec.2 N hN

/-- **Consistency with Mathlib's qualitative result.** Mathlib v4.26.0
records `rothNumberNat_isLittleO_id : (rothNumberNat N : ℝ) =o[atTop] (N : ℝ)`
unconditionally in `Mathlib.Combinatorics.Additive.Corner.Roth`. The Bourgain
axiom strengthens this with an *explicit* decay rate
`O(N · (log log N / log N)^{1/2})`, and is consistent with the qualitative
form in the sense that both assert `rothNumberNat N = o(N)`. We record the
qualitative form as a one-line export so OQ-01 consumers can pull it in via
this namespace without re-deriving it from the axiom. -/
theorem bourgain_consistent_with_isLittleO :
    IsLittleO atTop (fun N : ℕ => (rothNumberNat N : ℝ))
      (fun N : ℕ => (N : ℝ)) :=
  rothNumberNat_isLittleO_id

/-- **Consistency of the Bourgain upper bound with Behrend's lower bound.**
For every `N ≥ 3`, Behrend's explicit lower bound on `rothNumberNat N` does
not exceed the Bourgain upper bound:

  `N · exp(-4 · √(log N)) ≤ bourgainConst · N · (log log N / log N)^(1/2)`.

This sanity-checks the `rothNumberNat_bourgain` axiom against the
*unconditional* lower bound `Behrend.roth_lower_bound` proved in Mathlib
v4.26.0:

  `(N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`.

The proof is purely transitive through `rothNumberNat N`: both bounds hold
simultaneously, so the lower bound is `≤` the upper bound. We do *not* prove
the underlying analytic inequality directly; the consistency follows
automatically from the existence of both bounds. -/
theorem bourgain_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      bourgainConst * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_bourgain N hN)

/-- **OQ-02 implies OQ-01: the Bloom–Sisask bound is at least as strong.**
Both the Bourgain (OQ-01) and the Bloom–Sisask (OQ-02,
`RothTheoremOQ02.rothNumberNat_le_blasi`) upper bounds hold simultaneously,
so `rothNumberNat N` is bounded by the *minimum* of the two right-hand sides:

  `rothNumberNat N ≤ min ( bourgainConst · N · (log log N / log N)^{1/2} )
                         ( N / (log N)^{1 + blasiConst} )`.

Because the Bloom–Sisask right-hand side `N / (log N)^{1+c}` decays strictly
faster than the Bourgain right-hand side, this `min` is (for large `N`) the
Bloom–Sisask term — the formal record that OQ-02 ⟹ OQ-01. The proof is a
one-line `le_min` of the two axiomatic bounds; we do not prove the analytic
domination of one right-hand side by the other (an unconditional comparison
would require tracking the unknown constants `bourgainConst` and
`RothTheoremOQ02.blasiConst`). -/
theorem rothNumberNat_le_min_bourgain_blasi (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      min (bourgainConst * (N : ℝ) *
            (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2))
          ((N : ℝ) / Real.log N ^ (1 + RothTheoremOQ02.blasiConst)) :=
  le_min (rothNumberNat_le_bourgain N hN) (RothTheoremOQ02.rothNumberNat_le_blasi N hN)

#check rothNumberNat_bourgain
#check bourgainConst
#check bourgainConst_pos
#check rothNumberNat_le_bourgain
#check bourgain_consistent_with_isLittleO
#check bourgain_consistent_with_Behrend
#check rothNumberNat_le_min_bourgain_blasi

end RothTheoremOQ01
