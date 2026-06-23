# area-of-circle-oq-05-oq-04 — Problem Statement

**Parent**: `area-of-circle` (Wiedijk 100 #9), specifically the Gaussian integral branch
`AreaOfCircleOQ05` (∫ exp(−x²) = √π) and its multivariate extension `AreaOfCircleOQ05OQ02`.

**Source notes** (from `.lean/state/candidate-pool.json`):

> The Gaussian integral over ℂ (and more generally, over p-adic fields ℚ_[p]) takes
> analogous forms: ∫_{ℚ_[p]} e^{2πi ‖x‖_p} dx = 1. Are adelic Gaussian integrals …

## S1 Observation: the source formula is malformed

The literal formula `∫_{ℚ_[p]} e^{2πi ‖x‖_p} dx = 1` is mathematically ill-posed
in two distinct ways, both worth recording before any formalization step:

1. **The norm ‖·‖_p is real-valued** (`‖x‖_p = p^{-v_p(x)} ∈ {0} ∪ p^ℤ ⊂ ℝ`), so
   `e^{2πi ‖x‖_p}` is just a complex exponential of a real number and carries no
   p-adic information about `x` modulo `p^k`. Whatever this is, it is not the
   p-adic analogue of `e^{−x²}` on ℝ.
2. **Integration is against Haar measure on (ℚ_[p], +)**, which is σ-finite but
   *infinite* on ℚ_[p] itself. So `∫_{ℚ_[p]} f dx` for `f` non-decaying is
   divergent. The "= 1" can only be correct if either (a) the integration domain
   is restricted to `ℤ_[p]` (compact, Haar-mass-1 under the standard
   normalization) or (b) the integrand decays rapidly in `‖x‖_p` (Schwartz–Bruhat).

The OQ author almost certainly intended one of the three well-defined facts below.
Session S1 deliberately surfaces all three so a later session can pick the right
target; we do not yet pin a single formal statement.

## Three candidate formal statements

We expect S2 to commit to **(C2)** (the self-Fourier identity), since it is the
literal p-adic analogue of "the Gaussian is its own Fourier transform" — which is
the deep fact behind `∫ exp(−x²) dx = √π` and the parent file's polar-coordinates
argument. (C1) is a trivial restatement and (C3) is much heavier.

### (C1) Restriction-of-character identity (trivial)

Let `ψ_p : ℚ_[p] → ℂ` be the standard additive character (i.e. `ψ_p(x) = 1` for
`x ∈ ℤ_[p]`; on `ℚ_[p]/ℤ_[p]`, `ψ_p` is determined by `ψ_p(p^{-n}) = e^{2πi/p^n}`).
Then with Haar measure normalised by `μ(ℤ_[p]) = 1`:

```
∫_{ℤ_[p]} ψ_p(x) dx = 1.
```

This is trivial: `ψ_p ≡ 1` on `ℤ_[p]` and `μ(ℤ_[p]) = 1`. Worth recording as the
"obvious base case" but not the intended theorem.

### (C2) Self-Fourier identity for `𝟙_{ℤ_[p]}` (the intended p-adic Gaussian)

The Bruhat–Schwartz function `f = 𝟙_{ℤ_[p]} : ℚ_[p] → ℂ` plays the role of the
Gaussian `e^{−πx²}` on ℝ: under the standard self-dual additive character `ψ_p`
and self-dual Haar measure (i.e. `μ(ℤ_[p]) = 1`), `f` is fixed by Fourier
transform.

```
(F f)(ξ) := ∫_{ℚ_[p]} f(x) · ψ_p(ξ · x) dx = 𝟙_{ℤ_[p]}(ξ).
```

Evaluating at `ξ = 0` gives `μ(ℤ_[p]) = 1`. The *non-trivial* content is at
`ξ ∉ ℤ_[p]`, where character sums on `ℤ_[p]/p^k ℤ_[p]` vanish for `k` large
enough — this is Gauss's identity `∑_{a ∈ ℤ/p^k} e^{2πi a/p^k} = 0` (`k ≥ 1`)
packaged ultrametrically.

**Why this is the right analogue**: on ℝ, the Gaussian `g(x) = e^{−πx²}`
satisfies `F g = g`, and the area-of-circle / polar-coordinates trick is the
*proof* that `(F g)(0) = ∫ g = 1`. On ℚ_[p], the indicator `𝟙_{ℤ_[p]}` is
self-Fourier, and `(F 𝟙)(0) = μ(ℤ_[p]) = 1` is the same statement.

### (C3) Local Tate functional equation / Igusa local zeta

A genuinely deep p-adic identity in the same circle of ideas: the Tate
local L-factor for the trivial character on ℚ_[p] is

```
ζ_p(s) = ∫_{ℤ_[p] ∖ {0}} ‖x‖_p^{s-1} d^×x · (1 − p^{-1})  =  1 / (1 − p^{-s}),
```

and Igusa's local zeta for `f(x) = x²` is

```
Z_p(s) = ∫_{ℤ_[p]} ‖x‖_p^{2s} dx  =  (1 − p^{-1}) / (1 − p^{-2s-1}).
```

These ARE the p-adic Gaussian integrals in the sense relevant to adelic
analysis (Tate's thesis), but they are several Mathlib milestones away.

## Complex case ("over ℂ")

The OQ source also mentions `over ℂ`. The complex Gaussian
`∫_ℂ e^{−π|z|²} dA(z) = 1` is **already accessible** via Mathlib's existing
machinery: `Complex.measureSpace`, `MeasureTheory.integral_pi`, and the
real `∫ e^{−πx²} dx = 1` from `Mathlib.Analysis.SpecialFunctions.Gaussian.*`.
This is a small bridge lemma, not a research-level open problem.

The S1 recommendation is therefore:
- Treat the complex case as a *follow-on companion theorem*, ~30 lines, low
  risk, suitable for a small S2/S3 commit.
- Treat the p-adic case (C2) as the main S2 target.

## Why this OQ matters

1. **Pedagogical**: makes the role of "the Gaussian as eigenfunction of Fourier
   transform" explicit, by exhibiting the discrete-Fourier analogue on ℚ_[p].
2. **Mathlib infrastructure check**: forces an audit of what's available in
   `Mathlib.NumberTheory.Padics` and `Mathlib.MeasureTheory.Measure.Haar.*`.
   See `knowledge.md` for the survey.
3. **Adelic bridge**: the OQ tagline ("Are adelic Gaussian integrals …") points
   toward the Iwasawa–Tate decomposition `ζ(s) = ζ_∞(s) · ∏_p ζ_p(s)`, where
   the real Gaussian and the p-adic indicator are the local-factor analogues
   at the archimedean and non-archimedean places respectively. A successful
   formalization of (C2) is the first step in that direction.

## Next action (S2 candidate)

State (C2) as a Lean theorem in a new file `Proofs/AreaOfCircleOQ05OQ04.lean`,
once we have either (a) Haar measure on (ℚ_[p], +) wired up via Mathlib's general
locally-compact-group Haar machinery, or (b) a hand-rolled `MeasureTheory.Measure`
on ℚ_[p] from the proper-metric-space structure already in Mathlib. See
`knowledge.md` §Mathlib gaps.
