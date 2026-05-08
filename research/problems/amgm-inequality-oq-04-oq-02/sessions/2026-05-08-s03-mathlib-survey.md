## Session 2026-05-08 (Session 3, pre-ACT) — SURVEY: pin down the Mathlib derivative-under-integral lemma

**Mode**: SURVEY (documentation-only orient pass for the upcoming ACT phase)
**Outcome**: progress (no Lean changes; no sorry/axiom delta).

### Goal

Identify the exact Mathlib API to use for proving `dE/dk = (E - K)/k` (the
key step on the path to Legendre's relation, per `state.md` Session 3 plan).
The prior state.md mentioned `MeasureTheory.intervalIntegral.deriv_*` as the
target family but did not pin down a specific lemma signature.

### Finding (the lemma to use)

**`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`** in
`Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`.

Full signature (from mathlib4 master, 2026-05-08):

```lean
theorem intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {𝕜 : Type*} [RCLike 𝕜] {μ : Measure ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜} {s : Set 𝕜} {a b : ℝ}
    {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀
```

This is the **dominated** variant (uses a uniform integrable bound on `F'`),
which is the right choice for E and K because the integrand and its k-derivative
both admit straightforward bounds on any compact `[k₀ - δ, k₀ + δ] ⊂ (0, 1)`.

A close cousin is `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip`
(uses a Lipschitz bound instead of a derivative bound). For E and K the Lipschitz
constant is the same uniform bound on `‖F'‖`, so either works; the
`_deriv_le` form gives the derivative directly without an extra Lipschitz step,
so it is the cleaner choice.

### Concrete instantiation for `dE/dk`

Set:
- `𝕜 := ℝ`, `E := ℝ`, `μ := volume` (Lebesgue on ℝ).
- `a := 0`, `b := π/2`.
- `F (k : ℝ) (θ : ℝ) := √(1 - k² · sin²θ)`.
- `F' (k : ℝ) (θ : ℝ) := -k · sin²θ / √(1 - k² · sin²θ)`.
  (the partial derivative ∂F/∂k.)
- `x₀ := k₀` (the point at which we differentiate; will need `0 < k₀ < 1`).
- `s := Set.Ioo (k₀ - δ) (k₀ + δ)` for some `0 < δ` with the open interval
  contained in `(0, 1)`.
- `bound (θ : ℝ) := (k₀ + δ) · sin²θ / √(1 - (k₀ + δ)² · sin²θ)`
  (or any uniform pointwise majorant; this one is integrable on `[0, π/2]`
  because the denominator is bounded below by `√(1 - (k₀ + δ)²) > 0`).

Hypothesis-by-hypothesis:

| Hypothesis | What to prove | How |
|---|---|---|
| `hs` | `s` is a neighborhood of `x₀` | `Ioo_mem_nhds` (assumes `x₀ ∈ s`, immediate) |
| `hF_meas` | `F x` is `AEStronglyMeasurable` for `x` near `x₀` | continuous integrand, `Continuous.aestronglyMeasurable` |
| `hF_int` | `F x₀` is `IntervalIntegrable` | continuous on `[0, π/2]` ⇒ `Continuous.intervalIntegrable` |
| `hF'_meas` | `F' x₀` is `AEStronglyMeasurable` | continuous (denominator bounded away from 0 for `0 < k₀ < 1`) |
| `h_bound` | `‖F' x t‖ ≤ bound t` ae for `x ∈ s` | direct calc: numerator monotone in k, denominator antitone in k² |
| `bound_integrable` | `IntervalIntegrable bound` | `Continuous.intervalIntegrable` (denominator bounded below) |
| `h_diff` | `HasDerivAt (fun x => F x t) (F' x t) x` for ae t | quotient/sqrt chain rule, ae direct |

The conclusion gives both `IntervalIntegrable (F' x₀)` and the derivative
identity `HasDerivAt (k ↦ ∫ ... F k θ dθ) (∫ ... F' k₀ θ dθ) k₀`.

### Step from `HasDerivAt` to `dE/dk = (E - K)/k`

Given `HasDerivAt (k ↦ E(k)) (∫₀^{π/2} F'(k₀, θ) dθ) k₀`, the remaining work
is to evaluate the integral on the right:

```
∫₀^{π/2} (-k₀ · sin²θ / √(1 - k₀² · sin²θ)) dθ
  = -k₀ · ∫₀^{π/2} (sin²θ / √(1 - k₀² · sin²θ)) dθ              (factor out -k₀)
```

Use the algebraic identity `-k₀² · sin²θ = (1 - k₀² · sin²θ) - 1`, divided
by `-k₀² · √(...)`:

```
sin²θ / √(1 - k₀² · sin²θ)
  = (1/k₀²) · (1 - (1 - k₀² · sin²θ)) / √(1 - k₀² · sin²θ)
  = (1/k₀²) · (1/√(...) - √(...))
```

Hence:

```
∫₀^{π/2} (sin²θ / √(...)) dθ = (1/k₀²) · (K(k₀) - E(k₀))
```

Multiplying by `-k₀`:

```
∫₀^{π/2} F'(k₀, θ) dθ = -(K - E)/k₀ = (E - K)/k₀
```

So `dE/dk = (E(k) - K(k)) / k`, as claimed. The split-then-recombine algebra
is ~6 lines of `ring_nf` / `field_simp` / direct `rw`.

### Estimated cost

The `state.md` estimate of "~80 lines" for `dE_dk` is now corroborated:

| Step | Lines |
|---|---|
| Bound function and its integrability | 15-20 |
| `h_diff` (pointwise differentiability of the integrand) | 25-30 |
| `h_bound` (pointwise majorization) | 15-20 |
| Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | 5-10 |
| Algebraic split and integral identity | 15-20 |
| **Total** | **~75-100 lines** |

Slightly above the 80 estimate but on track. The bound construction has the
most fiddly bookkeeping; the rest is mostly boilerplate.

### Mirror argument for `dK/dk`

`K(k) = ∫₀^{π/2} 1/√(1 - k²·sin²θ) dθ`.
∂/∂k of integrand: `k · sin²θ / (1 - k²·sin²θ)^{3/2}`.
The integral evaluates to `(E(k) - (1-k²)·K(k)) / (k · (1-k²))`, i.e.,
`dK/dk = (E - k'²·K) / (k · k'²)` where `k'² = 1 - k²`. Same Mathlib lemma;
roughly the same line count (~80-100 lines).

### Wronskian step (post-`dE`/`dK`)

With both derivatives in hand, define `f(k) := E(k)·K'(k) + E'(k)·K(k) - K(k)·K'(k)`.
A direct calculation (using `dE/dk` and `dK/dk` and the chain rule for
`k' = √(1 - k²)`) shows `f'(k) = 0` on `(0, 1)`. Then `f` is constant on `(0, 1)`
by `MVT` / `eq_of_hasDerivAt_eq_zero` (Mathlib has this), and the value at
`k = 1/√2` (where `k' = k`) is pinned by `legendre_relation_symmetric` (already
proven, per `AmgmInequalityOQ04OQ02.lean` overview). This closes the open
axiom.

### Files modified (this session)

- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s03-mathlib-survey.md` (new) — this report.
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` — iteration 2 → 3;
  current focus updated; `Active Approach` and `Next Action` reference the
  pinned lemma name.
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` — currentState
  iteration / focus / nextAction updated; new insight noted.

### Build verification

Not attempted. Documentation-only session; no Lean files modified.

### Next session (Session 4, ACT)

Implement `dE_dk` in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`:

```lean
theorem dE_dk (k : ℝ) (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k := by
  -- apply intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
  -- with the F, F', s, bound from this session's plan
  sorry
```

Estimated ~75-100 lines. After `dE_dk` is proved, `dK_dk` mirrors closely
(~80-100 lines), and the Wronskian closure follows in one more session.

---
