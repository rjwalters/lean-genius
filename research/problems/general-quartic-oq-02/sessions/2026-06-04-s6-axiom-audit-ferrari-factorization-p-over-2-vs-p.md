# Session 2026-06-04 S6 AUDIT — Ferrari factorization axioms are inconsistent with the file's resolvent cubic

**Researcher**: researcher-1
**Phase transition**: ACT (S5b SCAFFOLDs complete) → ACT (S6 AUDIT / BUGFIX)
**Outcome**: Bug identified, fix applied, build verification pending.

## Goal

Audit the long-standing `ferrari_factorization_forward` /
`ferrari_factorization_backward` axioms in
`proofs/Proofs/GeneralQuartic.lean` to understand why they have resisted
discharge across 5+ research sessions and across multiple researchers.

## Finding (TL;DR)

**The file's resolvent cubic and its Ferrari factorization axioms use
incompatible conventions.** The resolvent cubic
`8m³ + 20pm² + (16p²−8r)m + (4p³−4pr−q²) = 0` corresponds to the
**non-standard** Ferrari completion `(y² + p + m)²` (with `A = p`,
where `A` is the constant added inside the perfect-square trinomial).
But the factor expressions in the axioms use `(y² + p/2 + m ∓ αy ± β)`,
which corresponds to the **standard** completion `(y² + p/2 + m)²`
(with `A = p/2`).

The two conventions are not interchangeable. With the file's resolvent
and its `α² = 2m + p` relation, the only self-consistent factor form is
**`(y² + p + m ∓ αy ± β)`** — i.e., the constant is `p + m`, not
`p/2 + m`.

The factor-form bug propagates to the `ferrariRoots` definition, which
computes discriminants using `(p/2 + m ± β)` instead of `(p + m ± β)`.

## Numerical counterexample (witnesses inconsistency)

Take `p = 1`, `q = 0`, `r = 0`. The file's resolvent cubic at these
parameters is `8m³ + 20m² + 16m + 4 = 0`, which factors as
`4(2m + 1)(m + 1)² = 0`, giving roots `m ∈ {−1/2, −1, −1}`.

Pick `m = −1`. Then `α² = 2m + p = −1`, so `α = i` (principal branch).
`β = q / (2α) = 0`.

The factor expressions in the file's axiom evaluate (at `y = 0`,
which IS a root of `y⁴ + py² + qy + r = y⁴ + y² = y²(y² + 1) = 0`):

* Factor 1 (file): `0² + p/2 + m − α·0 + β = 0 + 1/2 + (−1) − 0 + 0 = −1/2 ≠ 0`
* Factor 2 (file): `0² + p/2 + m + α·0 − β = 0 + 1/2 + (−1) + 0 − 0 = −1/2 ≠ 0`

So `y = 0` is a root of the quartic, the hypotheses
`α² = 2m + p`, `β = q/(2α)`, and `resolventCubic.eval m = 0` all hold,
but neither factor disjunct evaluates to zero. The axiom's conclusion
is **mathematically false** at this witness.

Compare with the CORRECTED factor expressions `y² + p + m ∓ αy ± β`:

* Corrected Factor 1: `0 + 1 + (−1) − 0 + 0 = 0` ✓
* Corrected Factor 2: `0 + 1 + (−1) + 0 − 0 = 0` ✓

The corrected disjuncts both vanish at `y = 0`.

## Symbolic derivation (confirms the bug)

Let `F₁ := y² + C + m − αy + β` and `F₂ := y² + C + m + αy − β`, where
`C` is a free constant (the file uses `C = p/2`; we will show
`C = p`).

Then
```
F₁ · F₂ = (y² + C + m)² − (αy − β)²
       = y⁴ + 2(C+m)y² + (C+m)² − α²y² + 2αβy − β²
       = y⁴ + (2C + 2m − α²)y² + 2αβy + (C+m)² − β²
```

For `F₁ · F₂` to equal the depressed quartic `y⁴ + py² + qy + r`:

* **y² coefficient**: `2C + 2m − α² = p`. With file's `α² = 2m + p`:
  `2C + 2m − (2m + p) = 2C − p`. So we need `2C − p = p`, i.e.,
  **`C = p`**. (The file uses `C = p/2`, which gives `0`, not `p`.)

* **y coefficient**: `2αβ = q`, i.e., `β = q/(2α)`. (Matches file's `hβ`.)

* **constant**: `(C+m)² − β² = r`. With `C = p`:
  `(p+m)² − β² = r`, i.e., `β² = (p+m)² − r`. Substituting
  `β = q/(2α)` and `α² = 2m + p`:
  `q²/(4(2m+p)) = (p+m)² − r`
  `q² = 4(2m+p)((p+m)² − r)`
  `q² = 8m³ + 20pm² + 16p²m − 8mr + 4p³ − 4pr`
  `8m³ + 20pm² + (16p² − 8r)m + (4p³ − 4pr − q²) = 0`

That **is** the file's `resolventCubic p q r`. ✓

So the file's resolvent corresponds to choice `C = p` (i.e., the
completion `(y² + p + m)²`), and the factor expressions **must use**
`(y² + p + m ∓ αy ± β)` for the factorization to hold.

## Secondary bug: `ferrariRoots` α-sign / discriminant pairing

After fixing `p/2 → p` in `disc1`, `disc2`, the file's `ferrariRoots`
tuple still has an internal sign mismatch:

```lean
let disc1 := α^2 - 4 * (p + m + β)   -- corrected, = disc(F1)
let disc2 := α^2 - 4 * (p + m - β)   -- corrected, = disc(F2)
let sqrt1 := Complex.cpow disc1 (1/2 : ℂ)
let sqrt2 := Complex.cpow disc2 (1/2 : ℂ)
((-α + sqrt1) / 2, (-α - sqrt1) / 2, (α + sqrt2) / 2, (α - sqrt2) / 2)
```

By the quadratic formula applied to `F₁ := y² − αy + (p+m+β) = 0`
(read off as `ay² + by + c` with `a = 1`, `b = −α`, `c = p+m+β`),
the roots of `F₁` are `(α ± sqrt1)/2`, **not** `(−α ± sqrt1)/2`.
Symmetrically, the roots of `F₂` are `(−α ± sqrt2)/2`, **not**
`(α ± sqrt2)/2`.

So the α-sign in `y₁, y₂` is paired with the wrong discriminant. The
**second fix** is to swap the leading α-signs across the tuple
(equivalently: swap `disc1` and `disc2`).

## Proposed fix (scope: 5 textual edits, ≤ 10 LOC delta)

In `proofs/Proofs/GeneralQuartic.lean`:

| Line(s) | Current | Fixed |
|---|---|---|
| 142 | `y^2 + p/2 + m ∓ α * y ± β = 0` (axiom F-fwd conclusion) | `y^2 + p + m ∓ α * y ± β = 0` |
| 151 | same in axiom F-bwd hypothesis | same |
| 230–231 | same in `ferrari_factorization` theorem conclusion | same |
| 271 | `let disc1 := α^2 - 4 * (p/2 + m + β)` | `let disc1 := α^2 - 4 * (p + m + β)` |
| 272 | `let disc2 := α^2 - 4 * (p/2 + m - β)` | `let disc2 := α^2 - 4 * (p + m - β)` |
| 275 | `((-α + sqrt1) / 2, (-α - sqrt1) / 2, (α + sqrt2) / 2, (α - sqrt2) / 2)` | `((α + sqrt1) / 2, (α - sqrt1) / 2, (-α + sqrt2) / 2, (-α - sqrt2) / 2)` |

Net effect:

* `ferrari_factorization_forward / backward` axioms become
  **mathematically true** (verifiable by polynomial-identity expansion).
* `ferrariRoots` returns the actual four roots of the corrected factors.
* `ferrari_roots_verify` axiom (line 281) becomes mathematically true
  — its previously-vacuous proof obligation can now be discharged from
  `ferrari_factorization_backward` + quadratic-formula algebra (left
  for a future session as a 3rd axiom-elimination target).

**Soundness improvement**: prior to this fix, the file's
`ferrari_factorization_forward` axiom was **inconsistent** — it
asserted a false implication and could in principle be used to derive
`False`. After this fix, the axiom is a true mathematical statement.

## Downstream impact

Theorems unchanged in form, semantics now coherent:

* `ferrari_factorization` (line 225): proof body unchanged, calls the
  now-true axioms.
* `ferrari_roots_are_roots` (line 293): proof body unchanged, calls the
  now-true `ferrari_roots_verify` axiom on corrected `ferrariRoots`.
* `ferrari_biquad_limit` (line 483, S3 DISCHARGE): proof body unchanged.
  The `y₁, y₂, y₃, y₄` unwrapped from `ferrariRoots p 0 r m hm` change
  values but each is still a root of the depressed quartic, and the
  proof chain via `ferrari_roots_are_roots` + `biquadratic_simple`
  still discharges the conclusion. The theorem itself becomes **truly
  provable** (rather than vacuously-true via a false axiom).

Unrelated to this fix (orthogonal):

* `biquadratic_forward / backward` axioms (lines 181, 189) — independent
  of the Ferrari factorization. Still provable from `Complex.cpow`
  squaring identity; not addressed in this session.
* `quartic_has_four_roots` axiom (line 174) — independent. FTA-level
  result, still axiom.

## Comment/docstring inconsistencies left for follow-up

The TOP-LEVEL docstring (lines 39–58) derives Ferrari classically using
the **standard** completion `(y² + p/2 + m)²` and quotes the standard
resolvent indirectly. The file's actual resolvent corresponds to
`(y² + p + m)²`. These docs should be reconciled (either change file
to use the standard convention, or update docs to reflect the
non-standard convention actually used). This is a SEPARATE session task.

The `ferrari_factorization` theorem docstring (line 223) and the
`ferrariRoots` definition docstring (lines 260–266) similarly reference
the standard `p/2 + m` form. They should be updated to match the
corrected code, but the audit/bugfix is the higher priority.

## Why this was missed across many sessions

The file shipped with documentation matching the **standard** Ferrari
completion (so reviewers saw a familiar derivation), while the actual
**code** used a non-standard completion. The bug is only visible when
you carefully cross-check the resolvent's coefficients against the
factor expressions' constant terms — a check no prior session
performed.

The downstream theorems compiled because:

1. The factorization axioms were declared, not proved (axiom always
   "type-checks").
2. `ferrariRoots` is a definition — its return value doesn't need to
   satisfy any equational property at definition time.
3. `ferrari_roots_verify` is also an axiom, so its (false) conclusion
   was never checked.
4. Downstream theorems (`ferrari_biquad_limit`, etc.) used these
   axioms abstractly without inspecting the specific `y_i` values.

So the build succeeded, the gallery rendered, and the inconsistency
hid behind layered axioms.

## Build verification status

**Pending.** This session does not include a Docker build cycle. The
audit + fix is mathematically verified above (numerically + symbolically).
Lake / Docker build verification should be the next action — either by
the auditor agent or by the next researcher claiming this problem.

## Next steps

1. (NEXT SESSION) Run `./proofs/scripts/docker-build.sh Proofs.GeneralQuartic`
   to verify the fix builds.
2. (NEXT SESSION) Reconcile the top-level docstring (lines 39–58) and
   `ferrari_factorization` theorem docstring (line 223) and
   `ferrariRoots` def docstring (lines 260–266) with the corrected
   non-standard `(y² + p + m)²` completion convention.
3. (FOLLOW-UP) Now that `ferrari_factorization_forward / backward`
   are true statements, attempt to discharge them via
   `linear_combination` + ring arithmetic. They should be ~10 LOC each.
4. (FOLLOW-UP) Discharge `ferrari_roots_verify` from the now-true
   `ferrari_factorization_backward` + quadratic formula.

## Honest assessment of significance

This is a **bug-fix audit**, not a new mathematical result. The
contribution:

* Explains why 5+ prior sessions across multiple researchers could not
  discharge the Ferrari factorization axioms (they were FALSE as
  stated, not just hard).
* Replaces an unsound axiom with a true one. This is a **soundness
  improvement** for the file.
* Opens the door to discharging 3 of the 6 remaining axioms
  (`ferrari_factorization_forward / backward`, `ferrari_roots_verify`)
  in follow-up sessions, since they are now mathematically valid.

It does not advance any of OQ-02.a, OQ-02.b, OQ-02.c directly (those
were closed / scaffolded in prior sessions). But it strengthens the
foundation those open-questions rest on by removing a false-axiom
dependency.
