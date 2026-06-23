# S4b OBSERVE — p-adic Mathlib Survey (doc-only)

**Researcher**: researcher-12
**Date**: 2026-05-12
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Lean file**: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (unmodified by this iteration)
**Parent**: PR #18221 (S4a, complex `ℂⁿ` Gaussian, build-verified) — this survey is orthogonal.

## Purpose

S2a–S4a fully formalised the **complex** Gaussian arm of OQ-05-OQ-04
(see `state.md` for the four built theorems and the n-fold extension
in PR #18221). The **p-adic** arm (problem.md candidate **(C2)**:
`𝟙_{ℤ_[p]}` is self-Fourier under `(ψ_p, μ)` with `μ(ℤ_[p]) = 1`)
remains blocked on two named Mathlib milestones (knowledge.md §gaps).

This iteration **re-audits** those milestones against Mathlib v4.26.0
(the pin in `proofs/lakefile.toml`), tracking every adjacent piece of
infrastructure that does exist. No Lean source is modified; no axioms
introduced. This file is the basis for a concrete S5b (or later
upstream Mathlib PR) once a researcher has bandwidth for the multi-week
contribution.

## Gap A — standard additive character `ψ_p : ℚ_[p] → ℂ`

Required: a continuous group homomorphism `ψ_p : (ℚ_[p], +) → ℂˣ`
with the standard normalisation `ψ_p|_{ℤ_[p]} = 1` and
`ψ_p(p^{-n}) = exp(2πi · a_n)` where `a_n ∈ ℚ ∩ [0, 1)` is the
fractional part of any rational representative.

### Status at v4.26.0: NOT in Mathlib.

### Adjacent pieces that DO exist (verified by direct content fetch):

| Mathlib file | Provides | Limitation vs. `ψ_p` |
|---|---|---|
| `Mathlib.NumberTheory.Padics.AddChar` | `AddChar ℤ_[p] R` for any complete ultrametric normed `ℤ_[p]`-algebra `R` | `ℂ` is NOT a `ℤ_[p]`-algebra (no canonical `ℤ_[p] →+* ℂ`); also only covers `ℤ_[p]`, not `ℚ_[p]` |
| `Mathlib.Analysis.Fourier.ZMod` | `ZMod.stdAddChar : AddChar (ZMod N) ℂˣ` mapping `j ↦ exp(2πi j / N)` | discrete domain only |
| `Mathlib.NumberTheory.Padics.RingHoms` | `PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p^n)`, the standard reduction | only on `ℤ_[p]` (`ℚ_[p]` projects through the inverse limit, not directly) |
| `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar` | `AddChar` constructions into the unit circle from `ZMod N` and `AddCircle` | exposes the **target** machinery; needs the right domain bridge |

### Composition that gives `ψ_p` on `ℤ_[p]` only (trivial)

Composing the projection `toZModPow n` with `ZMod.stdAddChar` gives
a character `ℤ_[p] → ℂˣ` that is **trivial on `p^n ℤ_[p]`** and
non-trivial on the cosets — i.e. the level-`n` truncation of `ψ_p`.
Concretely:

```text
ψ_p^{(n)}(x) := ZMod.stdAddChar (toZModPow n x)        -- ℤ_[p] →* ℂˣ
              = exp(2πi · (zmodRepr_n x) / p^n)
```

This is *not* the standard `ψ_p`. The standard `ψ_p` is trivial on
`ℤ_[p]` and non-trivial on `ℚ_[p] / ℤ_[p]` — exactly the opposite
support pattern. The pair `(ψ_p^{(n)}, ψ_p)` together generate the
full Pontryagin dual of `ℚ_[p]`; Tate's thesis uses both.

### Missing: domain extension `ℤ_[p] ↪ ℚ_[p]` for additive characters

The standard ψ_p is the extension by zero on `ℤ_[p]` of a non-trivial
character on `ℚ_[p] / ℤ_[p]`. Mathlib v4.26.0 does NOT expose either:

1. The quotient `ℚ_[p] / ℤ_[p]` as a `ZMod`-like discrete group; or
2. The equivalence `ℚ_[p] / ℤ_[p] ≃ ⊕_{ℕ⁺} ZMod (p^n)` (or
   `≃ ℤ[1/p] / ℤ`) needed to define the character pointwise.

The quotient is well-defined algebraically — `ℚ_[p]` is a discrete
valuation field with `ℤ_[p]` its valuation ring — but the
`AddSubgroup.quotient`-side Mathlib equivalence to `ZMod`-pieces is
not present.

### Recommended single-PR Mathlib contribution

A new file `Mathlib/NumberTheory/Padics/StandardAdditiveCharacter.lean`
that defines:

```lean
-- The fractional-part map ℚ_[p] → ℚ ∩ [0, 1).
def Padic.fracPart : ℚ_[p] → ℚ := ...

-- ψ_p(x) = exp(2πi · fracPart x).
noncomputable def Padic.stdAddChar : AddChar ℚ_[p] ℂˣ := ...

theorem Padic.stdAddChar_trivial_on_intRange (x : ℤ_[p]) :
    Padic.stdAddChar (x : ℚ_[p]) = 1 := ...

theorem Padic.stdAddChar_value_at_inv_p_pow (n : ℕ) (hn : 1 ≤ n) :
    Padic.stdAddChar ((p : ℚ_[p]) ^ (-n : ℤ)) = exp (2 * π * I / p ^ n) := ...
```

Effort estimate: ~300–500 lines, 2–4 weeks. Self-contained — does not
block on any other Mathlib milestone. Highest leverage path to (C2).

## Gap B — `MeasureTheory.Measure ℚ_[p]` with `μ(ℤ_[p]) = 1`

Required: a Borel-measurable, left-invariant, locally-finite Haar
measure `μ` on `(ℚ_[p], +)`, **normalised** so that `μ(ℤ_[p]) = 1`.

### Status at v4.26.0: NOT in Mathlib.

The general Haar-measure construction
`Mathlib.MeasureTheory.Measure.Haar.Basic.haarMeasure` accepts any
locally-compact Hausdorff topological group `G` with a `PositiveCompacts
G` element `K₀`, and produces an outer-regular Haar measure
normalised so `μ(K₀) = 1`. For `(ℚ_[p], +)`:

| Required hypothesis | Mathlib v4.26.0 status |
|---|---|
| `LocallyCompactSpace ℚ_[p]` | **available** via `Padic.instProperSpace` (`Mathlib.NumberTheory.Padics.ProperSpace`, line 63) |
| `T2Space ℚ_[p]` | **available** via `MetricSpace ℚ_[p]` |
| `CommGroup ℚ_[p]` (additive) | **available** via `AddCommGroup ℚ_[p]` |
| `PositiveCompacts ℚ_[p]` with `ℤ_[p]` body | **derivable**: `ℤ_[p]` is compact (`PadicInt.compactSpace`, line 54) and has non-empty interior (`ℤ_[p]` is the open ball of radius 1 in `ℚ_[p]`) |
| `MeasurableSpace ℚ_[p]` | NOT explicitly registered. Auto-derivable: `borel`-class instance. |
| `BorelSpace ℚ_[p]` | NOT explicitly registered. Auto-derivable. |

### What's needed: a short instance-registration file

```lean
-- Mathlib/NumberTheory/Padics/HaarMeasure.lean
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace Padic
variable (p : ℕ) [Fact p.Prime]

instance : MeasurableSpace ℚ_[p] := borel _
instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- `ℤ_[p]` as a `PositiveCompacts` in `ℚ_[p]`. -/
noncomputable def intRangeCompacts : TopologicalSpace.PositiveCompacts ℚ_[p] :=
  ⟨⟨{ x | ‖x‖ ≤ 1 }, ?compactness⟩, ?interior⟩

/-- Standard normalised Haar measure on `ℚ_[p]` with `μ(ℤ_[p]) = 1`. -/
noncomputable def haarMeasure : MeasureTheory.Measure ℚ_[p] :=
  MeasureTheory.Measure.haarMeasure (intRangeCompacts p)

theorem haarMeasure_intRange : haarMeasure p { x | ‖x‖ ≤ 1 } = 1 := ...
```

Effort estimate: ~100–200 lines, 1 week. Independent of Gap A.

## What changed in Mathlib HEAD vs v4.26.0 (not in our pin, FYI)

Direct file-listing diff between `main` and `2df2f015`:

- **NEW** `Mathlib.NumberTheory.Padics.HeightOneSpectrum.lean`
  (Mercuri, 2025): isomorphism `adicCompletion ℚ ↔ ℚ_[p]` and
  `adicCompletionIntegers ↔ ℤ_[p]`. Bridges to Dedekind-domain
  adic-completion machinery — closer to Tate-thesis language than the
  direct `PadicNumbers`-Cauchy-sequence construction. Does NOT supply
  ψ_p or a measure.

- **NEW** `Mathlib.MeasureTheory.Measure.Haar.Extension.lean`
  (Browning, 2025): Haar measure on a short exact sequence
  `1 → A → B → C → 1` from Haar measures on `A` and `C`. Potentially
  applicable to `0 → ℤ_[p] → ℚ_[p] → ℚ_[p]/ℤ_[p] → 0`, but the SES
  itself is not yet wired up in Mathlib (Gap A.2 above).

Pinning Mathlib past v4.26.0 is out-of-scope for this iteration; the
gap analysis above stands for the v4.26.0 codebase we actually build
against.

## (C1) bonus — provable today if we accept axioms

The problem.md "trivial" candidate (C1),
`∫_{ℤ_[p]} ψ_p(x) dx = 1`, is provable in a single line *after*
axiomatising both Gap A and Gap B (since `ψ_p ≡ 1` on `ℤ_[p]` and
`μ(ℤ_[p]) = 1`, the integral collapses to `1`). This is **not** a
useful next step:

1. The mathematical content is zero — it's an identity-restriction.
2. It does not exercise the character-sum identity on `ZMod (p^k)` that
   constitutes the *real* content of (C2).
3. It adds two unconstrained axioms that should be Mathlib lemmas.

The axiom-integrity policy (CLAUDE.md) explicitly discourages this
pattern: structure-encoded hypotheses count toward the assumption
total. So we will NOT submit a `(C1)-with-axioms` Lean iteration as
S5b.

## Recommended S5 (in order of single-session productivity)

1. **S5c (complex orthogonality, in PR #18221's roadmap)** — prove
   `∫_ℂ z̄ⱼ · exp(-(b · ‖z‖²)) = 0` and the diagonal moment
   `∫_ℂ |z|² · (1/π) · exp(-‖z‖²) = 1/π` directly from S2a/S3 (no
   dependence on S4a's n-fold result). Pure Mathlib reduction:
   `Real.integral_exp_neg_sq_mul_id_sq` (the `x · exp(-bx²)` moment)
   plus the `ℂ ≃ᵐ ℝ × ℝ` transport already proved in this file.
   Build-pending acceptable.

2. **S5a (complex Fourier-eigenfunction)** — prove `f(z) = exp(-π‖z‖²)`
   is fixed by the 2-D real Fourier transform via the `ℂ ≃ ℝ²`
   identification. Mathlib has
   `Mathlib.Analysis.Fourier.FourierTransform` (1-D `Real.fourierIntegral`)
   and Plancherel; the 2-D version reduces to the product of two 1-D
   Gaussians being self-Fourier (the canonical archimedean fact). The
   single-variable result `Real.exp_neg_sq_self_fourier` should be in
   Mathlib already; bridge to `ℂ` via product structure.

3. **S5b (Mathlib milestone — single contribution: Gap B)** — multi-week
   upstream Mathlib PR for `Mathlib.NumberTheory.Padics.HaarMeasure` as
   sketched above. Independent of S5a/S5c.

The S5c path is the smallest, safest, and most consonant with the
S2a–S4a "complex Gaussian" theme of the file. The S5a path is the
single-PR archimedean analogue of (C2) and the most pedagogically
satisfying. S5b is the only direct progress toward (C2) itself but is
upstream-blocking.

## Compatibility with open PRs

- **#18221** (S4a, build-verified, open as of 2026-05-12 17:50 UTC):
  no file overlap. PR #18221 modifies `state.md`, `knowledge.md`,
  `src/data/research/problems/...json`, and `AreaOfCircleOQ05OQ04.lean`.
  This iteration introduces a **single new file** in
  `research/area-of-circle-oq-05-oq-04/`. Cleanly mergeable in either
  order.

- No other open or pending PRs were found for this slug
  (`gh api repos/rjwalters/lean-genius/pulls --paginate` and
  `git branch -r | grep area-of-circle-oq-05-oq-04`).

## Files touched in this iteration

- `research/area-of-circle-oq-05-oq-04/s4b-padic-survey.md` (new, ~200 lines)

## Sorries / axioms / build

- Sorries: 0 (doc-only)
- Axioms: 0 (doc-only)
- Build: N/A (no Lean changes)
