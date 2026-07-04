# Knowledge Base: fourier-series-oq-02-oq-03-wip-01

Sharp constant in the Fourier-coefficient decay bound for Hölder functions on the circle.

---

## Problem Understanding

For `f ∈ C^{0,α}(𝕋_T)` (α-Hölder, seminorm `[f]_α ≤ C`) the Fourier coefficients satisfy
a decay bound. The **upper bound** with constant `1/2`,

```
‖ĉ_n(f)‖ ≤ (C/2) · (T / (2|n|))^α ,   n ≠ 0,
```

is already **fully proven, 0 sorries**, in `proofs/Proofs/FourierSeriesOQ02.lean`
(`fourierCoeff_holder_decay`, line 242), via the half-period averaging identity
(`fourierCoeff_difference_formula`, line 127):

```
2 ĉ_n = (1/T) ∫₀^T (f(x) − f(x + T/(2n))) · e_{-n}(x) dx.
```

The **stated goal** of this WIP entry is to prove that the constant `1/2` is **sharp**.

---

## ⚠️ KEY FINDING (Session 2026-07-04, s01): the "1/2 is sharp" claim is FALSE

The half-period upper bound chains two inequalities:

1. **(phase)** `‖∫ g · e_{-n}‖ ≤ ∫ ‖g‖`   where `g(x) = f(x) − f(x+h)`, `h = T/(2n)`;
2. **(saturation)** `(1/T)∫ ‖g‖ ≤ C h^α`   (Hölder bound at shift distance `h`).

For the final constant `1/2` to be attained, **both** must be equalities simultaneously.
That forces `g(x) = C h^α · e_{+n}(x)` (constant modulus `C h^α`, phase locked to `e_{+n}`).
The unique periodic solution of `f(x) − f(x+h) = C h^α e_{+n}(x)` is the single sinusoid
`f(x) = (C h^α / 2) e_{+n}(x)`. But that `f` has **Hölder seminorm strictly larger than `C`**
(its true α-seminorm is `C · 2^{-α} M(α)` with `M(α) = sup_{u>0} |sin πu|/u^α > 2^{α-1}`),
so it is **inadmissible**. Hence the two tightness conditions are mutually incompatible for
any admissible `f`, and `1/2` is **not** attained — and in fact not even approached.

### The correct sharp constant for the Lipschitz case (α = 1): 4/π² ≈ 0.4053

For genuinely Lipschitz `f` (`|f'| ≤ C` a.e.), integration by parts gives the exact identity

```
ĉ_n(f) = (T/(2πi n)) · ĉ_n(f')          ⟹   ‖ĉ_n(f)‖ = (T/(2π|n|)) · ‖ĉ_n(f')‖.
```

Maximise `‖ĉ_n(f')‖ = ‖(1/T)∫ f' e_{-n}‖` over `|f'| ≤ C`. This is a **linear functional on the
L^∞ ball**, so the optimum is a bang-bang extreme point `f'(x) = C · sign(cos(2πnx/T − θ))`
(a ±C square wave), giving `‖ĉ_n(f')‖ = C · (2/π)` at the aligned phase. Therefore

```
max ‖ĉ_1(f)‖ = (T/2π)·(2C/π) = C T /π²,     bound value = (C/2)(T/2)^1 = C T /4,
⟹  sharp ratio k(1) = (C T/π²)/(C T/4) = 4/π² ≈ 0.4053  <  1/2.
```

The extremizer `f` is the **triangle wave** (antiderivative of the ±1 square wave), i.e. the
continuous, 1-Lipschitz "tent" function — **not** the discontinuous sawtooth `f(x)=x−T/2` that
the OQ02OQ03 docstring uses (that sawtooth has a jump at `0`, so it is *not* Lipschitz; its
α=1 seminorm is `+∞`, and comparing its `1/π` ratio to the bound is comparing apples to oranges).

**Numerical ladder (α = 1, ratio to the `1/2`-bound):**
- discontinuous sawtooth `x − T/2`: inadmissible (not Lipschitz) — the file's `1/π` figure is spurious;
- pure sinusoid `e^{2πix/T}`: ratio `1/π ≈ 0.318` (admissible but sub-optimal);
- **triangle wave (bang-bang optimum): ratio `4/π² ≈ 0.405` = sharp `k(1)`**;
- naive upper bound: `1/2 = 0.500` (valid, never attained).

So `1/π < 4/π² < 1/2`, and `4/π²` is the sharp Lipschitz constant.

---

## Consequence for the WIP target

The literal completion target — "discharge the sorries establishing that the constant `1/2`
is sharp" — **asks to prove a false statement** and therefore cannot be completed as written.
Note `FourierSeriesOQ02OQ03.lean` has **0 real sorries**: its "Section 3: Sharpness" consists
only of docstrings; no sharpness *theorem* is ever stated, so nothing is currently *claimed* as
proven. The gallery is not overclaiming, but the roadmap text is wrong.

### Corrected, provable targets (pick one for the ACT phase)

1. **Lower bound / non-sharpness (cleanest first step).** Define the triangle wave `Λ_T` on
   `AddCircle T`, prove it is `HolderWith 1 1` (Lipschitz const 1), and compute
   `‖fourierCoeff Λ_T 1‖ = T/π²` exactly. This yields a theorem giving `k(1) ≥ 4/π² > 1/π`,
   **disproving** the `1/2`-sharpness claim by exhibiting the true extremizer.
2. **Sharp constant upper bound (harder).** Prove `k(1) ≤ 4/π²` via the L^∞-duality / bang-bang
   argument (`‖ĉ_n(f)‖ = (T/2π|n|)‖ĉ_n(f')‖` + `‖ĉ_n(f')‖ ≤ (2/π)C`). Needs an integration-by-parts
   lemma for AbsolutelyContinuous/Lipschitz functions on `AddCircle` and the square-wave L¹→coeff bound.
3. **Correct the roadmap.** Replace the "1/2 sharp" language in `problem.md` and the
   `FourierSeriesOQ02OQ03.lean` Section-3 docstrings with the `4/π²` (α=1) result and the general
   open constant `k(α) < 1/2`.

---

## Dead Ends / Corrections

- **Do NOT** attempt to prove `‖ĉ_n‖ / (C(T/2n)^α) → 1/2`: it is false; the sup is `4/π²` at α=1.
- **Do NOT** use the discontinuous sawtooth `x−T/2` as the α=1 extremizer: it is not Lipschitz.
- The **exponent** α (not the constant) is already known sharp: `holder_decay_is_optimal_seq`
  (OQ02 line 381, proven in `FourierSeriesOQ02OQ04.lean` via a Weierstrass lacunary series).

---

## Mathlib gaps identified

- No packaged **triangle/square-wave** on `AddCircle T` with computed Fourier coefficients.
- No **integration-by-parts for Lipschitz / AbsolutelyContinuous functions on `AddCircle T`**
  relating `ĉ_n(f)` to `ĉ_n(f')`. (Mathlib has IBP on intervals; transfer to the circle is the gap.)
- No **L^∞-ball extremal (bang-bang) lemma** for a linear functional `g ↦ ∫ g·w`.

---

## General α (open)

For `α ∈ (0,1)` the extremizer is no longer a pure square-wave derivative (the constraint is a
Hölder seminorm, not an `L^∞` bound on `f'`), and the sharp `k(α)` is a genuine extremal constant
`< 1/2`, interpolating down to `k(1)=4/π²`. Determining `k(α)` in closed form is itself a small
research question (Favard/Bernstein-type extremal problem) — out of scope for a first completion.

---

## Session Log

### Session 2026-07-04 (s01) — ORIENT — Robb Walters / researcher-8

**Mode**: FRESH (claimed from pool, knowledge score 0)
**Outcome**: scouted/oriented — MATHEMATICAL CORRECTION, no Lean committed

**What I did**: Read the parent proofs (`FourierSeriesOQ02.lean`, `FourierSeriesOQ02OQ03.lean`,
`FourierSeriesOQ02OQ04.lean`). Found OQ02 already proves the `1/2` upper bound and exponent-optimality
(0 sorries). Analyzed the sharpness claim: proved (on paper) that `1/2` is **not** the sharp constant —
the two tightness conditions in the half-period bound are mutually exclusive for admissible `f`.
Computed the correct Lipschitz sharp constant `k(1) = 4/π² ≈ 0.405` via integration-by-parts + L^∞
bang-bang duality, with the **triangle wave** as extremizer. Flagged the file's `1/π`
sawtooth figure as spurious (non-Lipschitz function).

**Why no Lean**: both verification tools were down this session — Docker build unsafe (host swap 98%,
SIGBUS risk) and Aristotle MCP returned `Resource not found`. Committing unverified proof bodies would
risk build-breaking drift, so this is documentation-only ORIENT.

**Next**: implement Corrected Target #1 (triangle-wave lower bound `‖ĉ_1(Λ)‖ = T/π²`) once a build
path is available; it is self-contained and disproves `1/2`-sharpness by construction.
