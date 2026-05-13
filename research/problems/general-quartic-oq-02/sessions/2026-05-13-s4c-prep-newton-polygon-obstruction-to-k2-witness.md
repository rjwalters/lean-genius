# S4c PREP — Newton-polygon obstruction to a `k ≥ 2` Pan-witness

**Slug**: `general-quartic-oq-02`
**Phase**: S4c PREP (sister to in-flight PR #18365 S4 PREP and PR #18438 S4b PREP)
**Date**: 2026-05-13
**Researcher**: researcher-1
**Touches**: this file only — strictly orthogonal to all other PRs.

## 0. Orthogonality declaration

This document is a single new file:

- `research/problems/general-quartic-oq-02/sessions/2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`

It does **not** edit any of:

- `problem.md`, `knowledge.md`, `state.md`, or any other doc;
- `proofs/Proofs/GeneralQuartic.lean`;
- `src/data/proofs/general-quartic-oq-02/meta.json` or gallery JSON;
- `.lean/state/candidate-pool.json`.

Filename `2026-05-13-s4c-…` is distinct from PR #18365's
`2026-05-12-s4-prep-mathlib-gap-audit.md` and PR #18438's
`2026-05-13-s4b-prep-pan-witness-arithmetic-audit.md`. The `sessions/` directory
is shared (each PR creates it independently; git merges merge files cleanly).

## 1. Question this PREP addresses

PR #18438 audited the witness `(p, q, r)(t) = (-1, t², 1/4 - t² + t⁴/4)`
proposed in PR #18365 and concluded that the cancellation order is `k = 1`,
not `k ≥ 2` as the formal statement of OQ-02.a (problem.md:23-31) requires.
PR #18438 recommended **Option C**: split OQ-02.a into

- **a.1**: `k = 1` tangency, discharged by the Pan witness;
- **a.2**: `k ≥ 2`, left open.

This document strengthens PR #18438's recommendation by asking the **structural**
question:

> Is `k ≥ 2` achievable within the natural Pan-witness family (smooth
> 1-parameter perturbation of a biquadratic limit at `t = 0`), or is the
> obstruction generic?

Answer (this PREP): **`k ≥ 2` is structurally unachievable in this family.** The
Newton-polygon balance pins `α(t) = Θ(t)` whenever the actual root spread is
`Θ(t)`. Pushing to `k = 2` requires degenerating to `(p₀, r₀) = (0, 0)`, where
the depressed quartic becomes `y⁴ + q(t)·y = 0` and the actual root spread is
no longer `Θ(t)` — it is `Θ(q^{1/3}) = Θ(t^{c/3})`.

This formalizes PR #18438's Option C as a **forced** choice, not merely a
practical recommendation.

## 2. Resolvent reduction in the variable `s := 2m + p = α²`

The parent file `proofs/Proofs/GeneralQuartic.lean:77` defines

```
resolventCubic p q r := 8m³ + 20·p·m² + (16·p² - 8·r)·m + (4·p³ - 4·p·r - q²).
```

(Axiom `ferrari_factorization_forward` at line 137 declares `α² = 2m + p`.)
Substitute `m = (s - p)/2` so `s = 2m + p = α²`. The cubic in `s` becomes,
after standard expansion:

> **Lemma 1** (resolvent reduction).
> Let `s := 2m + p`. Then
> ```
>   resolventCubic p q r (eval at m = (s-p)/2)
>   = s³ + 2·p·s² + (p² - 4·r)·s - q².
> ```

**Derivation** (symbolic; verified by hand, can be discharged in Lean by
`ring_nf` after `m ↦ (s - p)/2` substitution):

```
8·((s-p)/2)³                = (s-p)³ = s³ - 3p·s² + 3p²·s - p³
20·p·((s-p)/2)²             = 5p·(s-p)² = 5p·s² - 10p²·s + 5p³
(16·p² - 8·r)·((s-p)/2)     = (8p² - 4r)·(s - p) = (8p² - 4r)·s - 8p³ + 4pr
+ 4·p³ - 4·p·r - q²         (constants)

Sum:
  s³ + (-3p + 5p)s² + (3p² - 10p² + 8p²)s + (-p³ + 5p³ - 8p³ + 4p³)
    + (-4r)·s + (4pr - 4pr) - q²
= s³ + 2p·s² + p²·s - 4r·s + 0 - q²
= s³ + 2p·s² + (p² - 4r)·s - q².
```

So the **cleaned resolvent** is

> `R̃(s; p, q, r) := s³ + 2·p·s² + (p² - 4·r)·s - q² = 0`.

This is the universal Newton-polygon-friendly form: it factors out the trivial
`α = 0 ⇔ s = 0` degeneracy and makes the dependence on `q²` explicit (the
inhomogeneous term).

### 2.1 Sanity check at the Pan limit `(p₀, q₀, r₀) = (-1, 0, 1/4)`

- `R̃(s; -1, 0, 1/4) = s³ - 2s² + (1 - 1)s - 0 = s²(s - 2)`.
- Roots: `s = 0` (double) and `s = 2` (simple).
- Translating back via `m = (s - p)/2 = (s + 1)/2`: `m = 1/2` (double) and
  `m = 3/2` (simple). Matches PR #18438's audit of the resolvent factorization
  at the Pan parameters.

### 2.2 The double-root degeneracy at `p² = 4r`

For *general* `(p₀, r₀)` with `q₀ = 0`:

> `R̃(s; p₀, 0, r₀) = s·(s² + 2p₀·s + (p₀² - 4r₀))`.

Inner quadratic discriminant: `(2p₀)² - 4·(p₀² - 4r₀) = 16r₀`. Roots of inner:
`s = -p₀ ± 2·√r₀`. So `R̃` has three roots `{0, -p₀ + 2√r₀, -p₀ - 2√r₀}`.

`s = 0` is the **trivial** resolvent root (makes `α = 0`, `β = q/(2α)`
indeterminate). The two non-trivial roots are the "biquadratic-z₁,z₂" pair
already used by the parent proof (`ferrari_biquad_limit`, knowledge.md:114-181).

`s = 0` becomes a **double** root of `R̃` iff one of the inner-quadratic roots
also lands at `0`, i.e., `-p₀ ± 2·√r₀ = 0`, i.e., `p₀² = 4r₀`. This is
**exactly** the Pan parameter locus, where Pan picks `(p₀, r₀) = (-1, 1/4)`.

`s = 0` becomes a **triple** root iff *both* inner roots land at `0`,
i.e., `p₀ = 0` AND `p₀² - 4r₀ = 0`, hence `(p₀, r₀) = (0, 0)`.

## 3. Newton polygon at the doubly-degenerate Pan parameters

Pin `(p₀, r₀) = (-1, 1/4)` (the Pan choice). Let `q(t) = t·v(t)` where
`v(0) ≠ 0` and `c := ord_t(q) = ord_t(v) + 1` is the leading vanishing order of
`q`. Let `s(t)` be the branch of `R̃ = 0` with `s(0) = 0`.

The equation `R̃(s; p(t), q(t), r(t)) = 0` near `t = 0` becomes (using
`2p(t)·s² ≈ -2s²` from `p(0) = -1`):

```
s³ - 2·s² + O(t)·s - q(t)² = 0
       ↑                ↑
     dominant if |s| ≫ 1   forcing term
```

Set `s = t^σ · S(t)` with `S(0) ≠ 0`. Newton-polygon balance:

| term      | order in `t`        | contribution if `σ > 0` |
|-----------|---------------------|--------------------------|
| `s³`      | `3σ`                | high-order (negligible if `σ ≥ 1`) |
| `-2s²`    | `2σ`                | dominant divisor side    |
| `O(t)·s`  | `σ + 1`             | sub-dominant if `σ ≤ 1`  |
| `-q(t)²`  | `2c`                | forcing                  |

Balance `-2s² ≈ q²` ⟹ `2σ = 2c`, i.e., **`σ = c`**.

Then `α(t)² = s(t) = Θ(t^c)`, so `α(t) = Θ(t^{c/2})`.

For the actual quartic-root spread `rootSpread(t)`: at the biquadratic limit
`(p₀, r₀) = (-1, 1/4)`, the depressed quartic `y⁴ - y² + 1/4 = (y² - 1/2)²`
has a **double** root at each of `y = ±1/√2`. A first-order perturbation
`+q(t)·y` splits each double root by `Θ(√q) = Θ(t^{c/2})`.

> **rootSpread**(t) = `Θ(t^{c/2})`.
> **α**(t) = `Θ(t^{c/2})`.
> **Ratio** = `Θ(1)`. **No blowup.**

So in the Pan-witness family, the cancellation order matches the spread order
*identically*: both scale as `t^{c/2}`. Setting `c = 2` (Pan's choice) gives
spread = `Θ(t)` and `α = Θ(t)`, hence `k = 1`. Setting `c = 4` would give
spread = `Θ(t²)` and `α = Θ(t²)`, still `k = 1` *with respect to the rescaled
spread*.

**Translation back to OQ-02.a's formal statement**:

- "rootSpread = `Θ(t)`" forces `c = 2`, i.e., `q(t) = Θ(t²)`.
- That in turn forces `α(t) = Θ(t)`, i.e., `k = 1`.
- The ratio `rootSpread / α = Θ(1)`, bounded, so the floating-point
  error-blowup factor `t^{1-k}` is `Θ(1)`, not `Ω(t^{1-k})` for any `k ≥ 2`.

This is the structural obstruction: **the same square-root opening of the
biquadratic double root governs both the actual root spread and the
intermediate `α`**. Pan's family cannot decouple them.

## 4. Could one push `α` to `Θ(t^k)` for `k ≥ 2`?

Goal: `α(t) = O(t²)`, i.e., `s(t) = O(t^4)`. Then the Newton-polygon balance
`-2s² ≈ q²` gives `q² = O(t^8)`, i.e., `q(t) = O(t^4)`.

But `q(t) = O(t^4)` with the same `(p₀, r₀) = (-1, 1/4)` gives `rootSpread`
**= `Θ(t²)`**, not `Θ(t)`. So the formal statement's `rootSpread = Θ(t)` is
**violated**.

Alternatively: stay with `rootSpread = Θ(t)` (so `q = Θ(t²)`) and push `α` to
`O(t²)` by changing the local resolvent geometry. To make the Newton-polygon
balance `s² ≈ q²` skip to `s³ ≈ q²` instead (which gives `s = Θ(t^{4/3})`,
fractional), one would need the `-2s²` term to vanish identically at the
witness parameters — i.e., `2·p₀ = 0`, so `p₀ = 0`. Combined with `p₀² = 4r₀`
(to keep `s = 0` at least double), this forces **`r₀ = 0`** as well.

But at `(p₀, q₀, r₀) = (0, 0, 0)` the depressed quartic is `y⁴ = 0` — every
root is `0` and no perturbation gives `rootSpread = Θ(t)` *without* the quartic
collapsing. Adding `q(t)·y`: `y⁴ + q(t)·y = y·(y³ + q(t)) = 0`, roots
`y = 0` and `y = (-q(t))^{1/3} · ω^k` for `k = 0,1,2`. Spread among the
three non-zero roots = `Θ(q^{1/3}) = Θ(t^{c/3})`. For spread `= Θ(t)`, need
`c = 3`, i.e., `q(t) = Θ(t³)`.

Then `α(t)²` solves `R̃(s; 0, t³·v, 0) = s³ - q² = s³ - t⁶·v² = 0`, so
`s = (t⁶·v²)^{1/3} = t² · v^{2/3}`, and `α = t · v^{1/3}`. Spread = `Θ(t)`,
α = `Θ(t)`, ratio = `Θ(1)`. **Still `k = 1`.**

So even at the triply-degenerate parameter point, the Newton polygon pins
`α = Θ(rootSpread)` identically, refusing to give `k ≥ 2`.

### 4.1 General statement

> **Newton-Polygon Pinning Lemma** (informal).
> For any smooth 1-parameter family `(p, q, r)(t)` with `(p(0), q(0), r(0))`
> degenerate (i.e., the depressed quartic at `t = 0` has a multiple root) and
> `m(t)` the resolvent branch satisfying `2m(0) + p(0) = 0` (i.e., the
> degenerate root), one has
> ```
>   |α(t)| = Θ(rootSpread(t))   as t → 0.
> ```
> Consequently `|rootSpread| / |α| = Θ(1)`, and OQ-02.a's `k ≥ 2` is
> unachievable in this family.

This lemma is **not** proved here as a Lean theorem — it is a structural
observation supported by the Newton-polygon calculations in §3-4. A formal
Lean proof would require asymptotic-analysis infrastructure
(`Filter.Tendsto`, `Asymptotics.IsBigO`) along the lines surveyed by PR
#18365's §5.

## 5. Implications for the OQ-02.a formal statement

PR #18438 proposed three forward options. With the obstruction in §4
established, these tighten as follows:

### Option A (weaken to `k ≥ 1`)

- **Effect**: trivialize OQ-02.a — the Pan witness already discharges `k = 1`
  with no further math required (just the arithmetic audit in PR #18438).
- **Cost**: removes the "catastrophic-cancellation" character of the problem
  (no `Ω(t^{1-k})` blowup; ratio is bounded).
- **Verdict**: not recommended. Loses the numerical-analysis motivation.

### Option B (search for a non-Pan-family witness)

- **Effect**: keep `k ≥ 2` as the formal statement and search for a witness
  outside the smooth-perturbation-of-biquadratic family.
- **Concrete candidates**:
  1. **Triple-root locus**. Depressed quartics `(y - y₀)³(y - y₁)`
     (parameters `p = -6y₀²`, `q = 8y₀³`, `r = -3y₀⁴`). Perturbing by a
     small `+εy²` or `+εy` term gives spread `= Θ(ε^{1/3})` from triple-root
     splitting. But: at the triple-root point, the resolvent cubic *also*
     becomes degenerate (verify: `(p₀, q₀, r₀) = (-6, 8, -3)` gives resolvent
     `8m³ - 120m² + 600m - 1000 = 8·(m-5)³`, **triple resolvent root at
     `m = 5`**). Cleaned-variable form: `R̃(s; -6, 8, -3) = s³ - 12s² + 48s -
     64 = (s - 4)³`. Triple root at `s = 4`, not `s = 0`. So `α(t)² → 4`,
     `α → ±2`, **no cancellation**.
  2. **Non-smooth family**. A Puiseux-series family `q(t) = t^{a/b}` with
     fractional exponent could in principle decouple `α` from `rootSpread`,
     but OQ-02.a's quantifier is over `ℝ → ℂ`-valued (smooth) families.
     Outside the formal statement.
  3. **Multi-parameter family**. A 2-parameter family `(p, q, r)(s, t)` could
     navigate around the Pinning Lemma's hypotheses, but again falls outside
     OQ-02.a's 1-parameter quantifier.
- **Verdict**: **option B as stated does not yield `k ≥ 2`**; the triple-root
  candidate fails (resolvent triple root at `s = 4 ≠ 0`, so `α` does not
  vanish), and the alternative paths require relaxing the formal statement.

### Option C (split into a.1 + a.2)

- **Effect**: keep the strong `k ≥ 2` statement as **a.2** (open question,
  no witness exists in the smooth Pan family) and add a.1 as the
  **dischargeable** `k = 1` tangency theorem.
- **Verdict (this PREP)**: **forced**, not merely recommended. The Pinning
  Lemma rules out a.2-witness construction in the only natural family.

## 6. What a future S5 ACT could do

If the parent project accepts Option C, S5 ACT would:

1. **Edit `problem.md`** (lines 20-31) to:
   - Rename OQ-02.a's existing `k ≥ 2` statement to **OQ-02.a.2 (open)**.
   - Add **OQ-02.a.1**: same form but with `k ≥ 1` (dischargeable).
   - Add a one-paragraph honest note: "Newton-polygon analysis (see
     `sessions/2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`)
     shows a.2 is unachievable in the smooth-Pan-witness family. The
     numerical-analysis literature (Pan 1997, Bini-Pan 1996) implicitly works
     with a.1."

2. **State a Lean theorem** `pan_witness_k1_tangency : ...` discharging a.1.
   Concrete: use `(p, q, r)(t) = (-1, t², 1/4 - t² + t⁴/4)`, prove via
   resolvent reduction (Lemma 1) + ring + `Real.sqrt`-asymptotics.
   Estimated ≤ 50 LOC after Lemma 1 is in place.

3. **Leave a.2 as an explicit open question** in `meta.json`'s
   `openQuestions`, citing this obstruction PREP.

4. *(Optional, lower priority)* prove Lemma 1 (`resolvent_reduction_in_s`)
   in Lean as a standalone utility. `ring_nf`-discharged after substitution.
   ~ 20 LOC.

## 7. What this PREP does NOT do

- **No edits to `problem.md` or any other doc**. The formal-statement edit
  is left to an S5 ACT.
- **No Lean code changes**. No `ring`-checks in Lean.
- **No claim that Option C is the only possible resolution**. Option A
  (weakening) and Option B-variant 2 (non-smooth families, requires changing
  the OQ-02.a quantifier) remain on the table — but B-variant 1 (triple-root
  locus) is decisively ruled out by §5.B.1.
- **No floating-point analysis**. The Newton-polygon argument is purely
  exact-arithmetic asymptotics. Pan/Bini-Pan-style floating-point arguments
  enter via the rounding-error model `err ≥ Ω(ε · |q / α|)`, which is
  identified but not formalized here.

## 8. Mathlib hooks usable by S5 ACT

Inheriting from PR #18365's gap audit:

- `Mathlib.Analysis.Asymptotics.Defs.IsBigO` for `α(t) = O(t)`.
- `Mathlib.Analysis.Asymptotics.Defs.IsTheta` for `α(t) = Θ(t)`.
- `Mathlib.Analysis.SpecialFunctions.Complex.Analytic` for Puiseux/Newton-style
  branch tracking around degenerate resolvent roots.
- `Mathlib.Algebra.CubicDiscriminant` for the original-variable resolvent's
  discriminant (when discussing the "double-root locus `p² = 4r`" in
  Lean-statement form).

No new Mathlib gap is surfaced by this analysis.

## 9. Honesty caveats

- **Newton-polygon argument verbal-level**. The §3-4 calculations are
  symbolic-but-informal. A fully rigorous Lean theorem would require
  `Filter.Tendsto`-level asymptotic plumbing that PR #18365 catalogued.
- **"Pan-witness family" not formally defined**. I have informally meant
  "smooth `ℝ → ℂ³`-valued curve `(p, q, r)(t)` with `(p, q, r)(0)` on the
  biquadratic-degenerate locus `q₀ = 0 ∧ p₀² = 4r₀`". A precise definition
  would be required for a formal Pinning-Lemma statement.
- **Off-by-one risk on `c/3` exponent**. The triple-root splitting analysis
  in §4 uses the standard "perturbation of a degenerate critical point of
  order `n` splits at rate `δ^{1/n}`" rule, which is folklore for `n = 2, 3`
  but not formally cited here. A cross-check would re-derive via the
  Puiseux expansion of `y⁴ + q(t)·y = 0` (cyclotomic structure).
- **Mathlib existence**: the Asymptotics lemmas listed in §8 were
  cross-referenced via PR #18365's audit (commit
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`); not independently re-verified.
- **No `lake build`** was run for this document.

## 10. Counts and metrics

|                              | Before | After this PR |
|------------------------------|--------|---------------|
| New `sessions/` files        | 0      | 1             |
| Lean source LOC              | —      | unchanged     |
| `sorry` declarations         | —      | unchanged (0) |
| `axiom` declarations         | —      | unchanged (6) |
| `meta.json` edits            | —      | none          |
| Newton-polygon facts derived | —      | 2 (Lemma 1 + Pinning Lemma) |

## 11. Cross-references

- **PR #18365** (S4 PREP, open): Mathlib gap audit. Identifies the
  asymptotic-analysis API needed for a future a.1 discharge.
- **PR #18438** (S4b PREP, open): Pan-witness arithmetic audit. Concludes
  `k = 1` empirically; recommends Option C.
- **PR #18203** (S3 DISCHARGE, merged): closed the `ferrari_biquad_limit`
  sorry in `proofs/Proofs/GeneralQuartic.lean`, leaving 0 sorries.
- **PR #18110** (S2 SCAFFOLD, merged): introduced `resolvent_cubic_q_zero`
  and the `ferrari_biquad_limit` statement. Section §2 of this PREP
  generalizes that file's `resolvent_cubic_q_zero` lemma from the line
  `q = 0` to the entire `(p, q, r)` parameter space, via the
  `m ↦ (s - p)/2` change of variables.

## 12. Pre-flight `#check` probes for the S5 implementer

Should anyone proceed to S5 ACT (concrete a.1 Lean proof), these probes
would validate Mathlib readiness before writing tactic blocks:

```lean
#check (Asymptotics.IsTheta : (ℝ → ℂ) → (ℝ → ℝ) → Filter ℝ → Prop)
#check (Asymptotics.isTheta_const_mul_self : ∀ {c : ℝ}, c ≠ 0 → …)
#check (Polynomial.eval_pow : ∀ {R : Type} [CommSemiring R] (n : ℕ) (p : R[X]) (x : R),
          (p^n).eval x = (p.eval x)^n)
#check (Filter.atTop : Filter ℝ)
-- For Lemma 1's `ring_nf` discharge:
example (p s : ℂ) : let m := (s - p)/2;
    8*m^3 + 20*p*m^2 + (16*p^2 - 8*0)*m + (4*p^3 - 4*p*0 - 0^2)
    = s^3 + 2*p*s^2 + (p^2 - 4*0)*s - 0^2 := by
  simp only []; ring
```

The last `example` is the **literal** Lemma 1 reduction at `(q, r) = (0, 0)`,
extractable directly as a `ring`-discharged Lean lemma. The general `(q, r)`
case adds three more `ring` terms but is structurally identical.

---

**Tagline**: *The numerical-instability witness OQ-02.a asks for cancellation
faster than the actual root spread. In the Pan-witness family, the resolvent's
Newton polygon pins them equal.*
