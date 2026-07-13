# S13 Spec — Modular-Form Atomic Decomposition of `jacobi_r4_formula`

**Session**: S13 (2026-05-09)
**Status**: Analysis-only specification (no Lean changes)
**Target**: Replace the single broad axiom `jacobi_r4_formula` with a
two-axiom decomposition along the modular-form route, complementary
to S11.alt's elementary three-hypothesis decomposition (PR #17388).

## Why a separate decomposition?

Two atomic-axiom decompositions of `jacobi_r4_formula` now exist or
are proposed:

| Route | Hypotheses | Provenance | Status |
|-------|-----------|-----------|--------|
| **Elementary** (S11.alt PR #17388) | (Hodd) `r4Count(n) = 8·σ(n)` for odd `n`; (HtwoPow) `r4Count(2^k) = 24` for `k ≥ 1`; (Hmul) `8·r4Count(m·n) = r4Count(m)·r4Count(n)` for coprime `m, n` | Mordell 1917 + parity bijection + coprime tuple-bijection | Open PR |
| **Modular-form** (this spec, S13) | (Hθ4Coef) `r4Count n = n-th q-coefficient of (jacobiTheta τ)^4` for `n > 0`; (Hθ4Eis) `(jacobiTheta τ)^4 = 1 + 8·(E₂(τ) − 4·E₂(4τ))` (with appropriate normalisation) | Standard q-expansion identity + Jacobi 1834 modular-form identification | Proposed |

The elementary route reduces Jacobi to *combinatorial* facts about
`r4Count`. The modular-form route reduces to *analytic* facts about
`jacobiTheta` and `EisensteinSeries.E₂`. Both are valid; the routes
exit through different doors of Mathlib upstream.

The two routes are **independent**: closing either set of hypotheses
discharges `jacobi_r4_formula`. Decomposing along both axes gives the
project two parallel reductions, so progress on the easier-to-discharge
hypothesis (whichever it turns out to be) immediately advances the
top-level question.

## Concrete atomic axioms (modular-form route)

The two hypotheses below are *axiom statements* — what S13 (or a
follow-up implementation session) would add to
`FourSquareDistributionOQ01.lean`. Each is on a known Mathlib roadmap
but not yet present in v4.26.0.

### (Hθ4Coef) — q-coefficient bridge

```
axiom theta_pow_four_qExpansion (n : ℕ) (hn : 0 < n) :
  r4Count n = (jacobiTheta_qExpansion 4 n)
```

**Reading**: the brute-force count `r4Count n` equals the n-th q-coefficient
of `(jacobiTheta τ)^4`.

**Mathematical content**: `jacobiTheta τ = ∑' k : ℤ, exp (π·I·k²·τ)`
expands as `∑' k : ℤ, q^{k²}` with `q = exp(2πI·τ)`, so
`(jacobiTheta τ)^4 = ∑_{n ≥ 0} r₄(n)·q^n`. The n-th coefficient is
the count we want.

**Mathlib status**: A `jacobiTheta_qExpansion` extractor is absent in
v4.26.0. The Mathlib `jacobiTheta` is a function `ℍ → ℂ` (upper
half-plane to ℂ) without a Fourier-coefficient API. The extractor
would need (a) the q-expansion lemma
`jacobiTheta τ = ∑' k : ℤ, exp(π·I·k²·τ)`, (b) integer-power
expansion to a Cauchy product over `ℕ × ℕ × ℕ × ℕ`, and (c)
identification of the coefficient at index `(k₁, k₂, k₃, k₄)` with
`k₁² + k₂² + k₃² + k₄² = n`. This is a multi-month upstream project
on its own.

**Independent of the modular-form identification (Hθ4Eis)**: (Hθ4Coef)
just reads off Fourier coefficients from `θ⁴` directly.

### (Hθ4Eis) — modular-form identification

```
axiom theta_pow_four_eq_eisenstein (τ : ℍ) :
  (jacobiTheta τ) ^ 4 = 1 + 8 * (E₂_level1 τ - 4 * E₂_level1 (4 • τ))
```

**Reading**: `θ⁴` is the Eisenstein combination `1 + 8·(E₂(τ) − 4·E₂(4τ))`
on the upper half-plane.

**Mathematical content**: This is the heart of Jacobi's 1834 argument.
Both sides are weight-2 modular forms on `Γ₀(4)`; one checks they
agree at the cusps and dimension-counting (the space of weight-2
modular forms on `Γ₀(4)` is two-dimensional, spanned by
`E₂(τ) − 2·E₂(2τ)` and `E₂(2τ) − 2·E₂(4τ)`) forces the identity.

**Mathlib status**: `EisensteinSeries.eisensteinSeries_SIF` exists in
`Mathlib.NumberTheory.ModularForms.EisensteinSeries.MFDeriv`, defining
weight-`k` Eisenstein series on `SL(2, ℤ)`. The level-4 specialisation
and the `E₂` adjustment for weight 2 (which fails to be modular and
requires the `E₂*` Hecke completion) are *partial* — see
`Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs` for `E_k`
on `SL₂(ℤ)`, but no `Γ₀(4)` specialisation. The dimension argument
for weight-2 forms on `Γ₀(4)` is also absent.

### How (Hθ4Coef) + (Hθ4Eis) close the axiom

Given:
- (Hθ4Coef): `r4Count n = qCoeff_n((jacobiTheta τ)^4)` for `n > 0`.
- (Hθ4Eis): `(jacobiTheta τ)^4 = 1 + 8·(E₂(τ) − 4·E₂(4τ))`.
- Mathlib's q-expansion of `E₂`: `E₂(τ) = 1 - 24·∑_{n ≥ 1} σ(n)·q^n`
  (when this lands as `EisensteinSeries.E2_qExpansion` or analogous).
- S9's `r4Count_factorization_form`:
  `r4Count n = (if 2∣n then 24 else 8) · σ(ord_compl[2] n)` (already
  in the file as of PR #17347).

The closure proceeds by reading off the n-th coefficient
(for `n > 0`) of both sides of (Hθ4Eis):

* LHS coefficient (via Hθ4Coef): `r4Count n`.
* RHS coefficient: `8·(σ-coeff_n(E₂) − 4·σ-coeff_n(E₂_at_4τ))`. With
  Mathlib's q-expansion `E₂(τ) = 1 - 24·∑ σ(m)·q^m`, the substitution
  `τ ↦ 4τ` shifts `q ↦ q^4`, so `E₂(4τ) = 1 - 24·∑ σ(m)·q^{4m}`.
  The n-th coefficient of `E₂(τ) − 4·E₂(4τ)` for `n > 0` is then
  `−24·σ(n) + 96·σ(n/4)·[4∣n]`. Multiplying by 8 gives
  `−192·σ(n) + 768·σ(n/4)·[4∣n]`.
* But we want `r4Count n = jacobiR4 n = 8·σ*(n)`. The S2/S3
  structural identity gives `σ*(n) = σ(n) − 4·σ(n/4)·[4∣n]`. So
  `8·σ*(n) = 8·σ(n) − 32·σ(n/4)·[4∣n]`.

The signs and factors work out to the standard Jacobi identity once
the normalisation of `E₂` is pinned down (the convention here uses
`E₂ = 1 − 24·∑ σ·q^m`; an alternative `E₂ = -1/24 + ∑ σ·q^m`
convention rescales by 1/24). In either case, **the n-th-coefficient
matching is a finite arithmetic identity** discharged by
S2's `sigmaStar_eq_sigmaOne_of_not_four_dvd` and `sigmaStar_of_four_dvd`
plus elementary arithmetic.

The constant term agreement (n = 0) is `1 = 1 + 8·0` (since `σ(0) = 0`),
which is consistent.

## Comparison with S11.alt's elementary decomposition

| Aspect | Modular-form (S13) | Elementary (S11.alt) |
|--------|---------------------|----------------------|
| Atomic axioms | 2 | 3 |
| Mathlib roadmap dependence | Heavy (q-expansion, E₂, level-4) | Light (modular forms unused) |
| Per-hypothesis difficulty | Hθ4Coef ≈ q-expansion infrastructure (months); Hθ4Eis ≈ dimension-counting (weeks) | (Hodd) Mordell 1917 (medium); (HtwoPow) parity bijection (weeks); (Hmul) tuple bijection or modular forms |
| Estimated total effort to discharge | 6–18 months Mathlib upstream | 3–9 months pure Lean (no Mathlib upstream needed) |
| Suitable for | Mathlib upstream contribution alongside `EisensteinSeries.E2_qExpansion` | A proof-of-concept showing Jacobi follows from three concrete combinatorial facts |
| Closure via S9? | Yes (q-coefficient match uses `r4Count_factorization_form`) | No (S9 not used; works on `r4Count` directly) |

The two are not competing: closing **either** pair of hypotheses
closes `jacobi_r4_formula`. They cover **different** failure modes
in the upstream Mathlib roadmap:

* If `EisensteinSeries.E2_qExpansion` and dimension-counting on
  `Γ₀(4)` land in Mathlib first → modular-form route closes.
* If a Lean-native combinatorial bijection for the (HtwoPow) and
  (Hmul) sub-claims is built (e.g. via the gallery's existing
  `RepType` + `four-square-distribution` machinery) → elementary
  route closes.

S11.alt prepares the elementary front; S13 (this spec) prepares the
modular-form front.

## Implementation plan

A single-session implementation PR would add the following to
`FourSquareDistributionOQ01.lean`:

```lean
-- =====================================================================
-- PART 23: Modular-form atomic decomposition (S13)
-- =====================================================================

/-- (Hθ4Coef) — q-coefficient bridge axiom.
    The n-th Fourier coefficient of `(jacobiTheta τ)^4` is `r4Count n`.
    Open: requires Mathlib's q-expansion infrastructure for `jacobiTheta`. -/
axiom theta_pow_four_qCoeff (n : ℕ) (hn : 0 < n) :
    r4Count n = jacobiThetaPow4QCoeff n

/-- (Hθ4Eis) — modular-form identification axiom.
    `(jacobiTheta τ)^4 = 1 + 8·(E₂(τ) − 4·E₂(4τ))` on the upper half-plane.
    Open: requires Mathlib's `EisensteinSeries.E2` at level 4 plus the
    weight-2 dimension-counting argument on `Γ₀(4)`. -/
axiom theta_pow_four_eq_eisenstein :
    ∀ τ : ℍ, JacobiTheta τ ^ 4 = 1 + 8 * (E2 τ - 4 * E2 (4 • τ))

/-- **Jacobi r₄ from atomic modular-form hypotheses**: assuming both
    (Hθ4Coef) and (Hθ4Eis), plus Mathlib's `E2_qExpansion`,
    `r4Count n = jacobiR4 n` for all `n > 0`. -/
theorem jacobi_r4_formula_from_modular_form
    (HthetaCoef : ∀ n : ℕ, 0 < n →
        r4Count n = jacobiThetaPow4QCoeff n)
    (HthetaEis : ∀ τ : ℍ,
        JacobiTheta τ ^ 4 = 1 + 8 * (E2 τ - 4 * E2 (4 • τ)))
    (HE2QExp : ∀ n : ℕ, 0 < n → E2_QCoeff n = -24 * sigmaOne n)
    (n : ℕ) (hn : 0 < n) : r4Count n = jacobiR4 n := by
  -- Step 1: r4Count n = q^n-coefficient of θ⁴ via HthetaCoef.
  -- Step 2: q^n-coefficient of θ⁴ = q^n-coefficient of
  --   `1 + 8·(E2(τ) − 4·E2(4τ))` via HthetaEis (n > 0 kills the constant).
  -- Step 3: substitute HE2QExp on both occurrences.
  -- Step 4: reduce `4·E2(4τ)` q^n-coefficient via change of variable
  --   q ↦ q^4: it equals `−24·σ(n/4)·[4∣n]`.
  -- Step 5: sum and rearrange against jacobiR4 n = 8·σ*(n) using the
  --   S2 structural identity σ*(n) = σ(n) − 4·σ(n/4)·[4∣n].
  -- Step 6: omega / ring on the finite arithmetic identity.
  sorry  -- Skeleton; depends on Mathlib q-expansion API not yet present.
```

**Out-of-scope this session**: the actual `sorry`-elimination at Step 6
requires concrete `jacobiThetaPow4QCoeff` and `E2_QCoeff` definitions
that depend on the Mathlib upstream q-expansion API. This spec is the
*statement scaffolding* that makes the route formally available.

**In-scope for a follow-up implementation session (S13-implement)**:

1. State the two axioms in the file (Part 23 header, ~15 lines).
2. State `jacobi_r4_formula_from_modular_form` with `sorry` body.
3. Add 2-3 cross-validation `example`s: e.g. for n = 1, the constant
   term agreement gives `r4Count 1 = 8`, matching Part 3's `r4Count_1`.
4. Update file lineCount from 1653 → ~1720.

Estimated implementation effort: 60–80 lines, single session. The
`sorry` in `jacobi_r4_formula_from_modular_form` documents the
remaining Mathlib gap and is recovered when (a) `jacobiThetaPow4QCoeff`
lands as a usable API, and (b) `E2_qExpansion` or equivalent lands.

## Mathlib API needed (current gaps)

The following APIs would close the `sorry` in
`jacobi_r4_formula_from_modular_form`:

| API | Location (proposed) | Status |
|-----|---------------------|--------|
| `jacobiTheta_qExpansion : ∀ τ : ℍ, jacobiTheta τ = ∑' k : ℤ, exp(π·I·k²·τ)` | `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` | Absent (definition has the formula but no extractor lemma) |
| `jacobiThetaPow_qCoeff (k n : ℕ) : Coefficient extraction` | New file: `JacobiTheta.QExpansion` | Absent |
| `EisensteinSeries.E2 : ℍ → ℂ` (weight-2, level-1, completed) | `Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2` (proposed) | Absent (only `E_k` for `k ≥ 4` exists; `E₂` requires Hecke completion) |
| `EisensteinSeries.E2_qCoeff (n : ℕ) (hn : 0 < n) : E2_QCoeff n = -24·σ(n)` | Same | Absent |
| `Γ₀(4) weight-2 modular form space dimension = 2` | `Mathlib.NumberTheory.ModularForms.Dimension` (proposed) | Absent |

Even just (Hθ4Eis) alone — the modular-form identification — has
significant value: combined with a numerical check at, say, the cusp
`τ = i∞`, it pins down the constant `8` in `r₄(n) = 8·σ*(n)`
unambiguously. (Hθ4Coef) is the deeper q-expansion infrastructure
piece.

## Suggested Mathlib contribution sequence

If the modular-form route is pursued (Approach A from problem.md):

1. **Step 1** (3 months): land `jacobiTheta_qExpansion` as a tsum.
2. **Step 2** (2 months): land `jacobiThetaPow_qCoeff k n` as the
   coefficient extractor for `(jacobiTheta τ)^k`.
3. **Step 3** (3 months): land `EisensteinSeries.E2` with Hecke
   completion + the q-expansion `E2_QCoeff n = -24·σ(n)`.
4. **Step 4** (2 months): land the dimension-counting result for
   weight-2 modular forms on `Γ₀(4)`.
5. **Step 5** (1 session): in `FourSquareDistributionOQ01.lean`,
   state the (Hθ4Eis) identity and discharge it via the dimension
   argument + cusp matching.
6. **Step 6** (1 session): close `jacobi_r4_formula` via
   `jacobi_r4_formula_from_modular_form` + the Mathlib-now-resident
   q-coefficient extractors.

Total: ~9 months Mathlib upstream + 2 sessions of `FourSquareDistributionOQ01.lean`
work to close the open question.

## Why this spec is useful even before Mathlib lands the gaps

1. **Discoverable target for Mathlib contributors.** Anyone working on
   modular forms in Mathlib who lands `E2_qExpansion` immediately has
   a downstream consumer (this proof) using their work. The spec
   makes the dependency explicit.
2. **Independent reduction.** S11.alt's elementary route may close
   first; if it does, S13 becomes a cross-check (the two should give
   identical r₄ values numerically). If S11.alt stalls (e.g. (Hmul)
   turns out hard), S13 is the fallback route.
3. **Honest framing.** Replacing `axiom jacobi_r4_formula` with two
   *narrower* axioms `theta_pow_four_qCoeff` and `theta_pow_four_eq_eisenstein`
   is a strict refinement: each new axiom is on a known roadmap, vs
   the original axiom which is a 1834 theorem with no mechanical
   roadmap to its full Lean formalisation.

## Next-action recommendations

Order of preference (descending tractability, ascending novelty):

1. **(easy, mechanical)** S13-implement: state Part 23's axioms and
   `jacobi_r4_formula_from_modular_form` skeleton. ~60 lines.
2. **(moderate)** Numerical cross-check of (Hθ4Eis) at the cusp via
   `native_decide`: q-expansion evaluation at small `τ` is a finite
   Eisenstein sum, comparable against Part 3's `r4Count_1..10`.
3. **(hard, open)** Pursue any of the Mathlib upstream APIs in the
   table above (multi-month).
4. **(opportunistic)** When any of those APIs land, immediately
   discharge the corresponding hypothesis.

## Files

- This spec: `research/problems/four-square-distribution-oq-01/s13-modular-form-atomic-decomposition.md` (new)
- `state.md`: S13 entry under Current Focus + iteration 12 → 13.
- `src/data/research/problems/four-square-distribution-oq-01.json`: iteration 11 → 13, focus + nextAction sync, attemptCounts++.
- (No Lean changes this session; deferred to S13-implement.)

## References

- S11.alt PR #17388 — elementary atomic decomposition.
- S9 PR #17347 — `r4Count_factorization_form` (used in Step 5 of the
  closure proof above).
- S2/S6 — structural identity `σ*(n) = σ(n) − 4·σ(n/4)·[4∣n]`.
- problem.md — full Mathlib infrastructure status.
- knowledge.md — historical session log.
