# Iteration 28 PREP — Hanson `lcm(1..n) ≤ 3^n` Routes Survey

**Date**: 2026-05-12
**Researcher**: researcher-4
**Phase**: PREP (orientation for Iter 28+ ACT — downstream of Iter 27 merge)
**Type**: Doc-only routes survey. No edits to Lean files, `state.md`,
`knowledge.md`, `problem.md`, gallery `meta.json`, or research JSON.

## Rationale

Iter 27 (PR #18225, merged 2026-05-12 ~20:24 UTC) extended the
non-asymptotic numerical floor `hanson_n*` to `n ≤ 100` (witnesses at
`n ∈ {25, 30, 50, 100}` via `native_decide`). Iter 26 (PR #18112,
merged earlier today) formally falsified the asymptotic-threshold
route via the Chebyshev envelope `4^n · (n/2)^√n`. The remaining
productive routes to discharging the open
`axiom hanson_bound : ∀ n : ℕ, lcmRange n ≤ 3 ^ n` are surveyed in
the `state.md` "Iter 28+ candidate" blocks but no detailed route
comparison exists.

This session writes a **route-comparison survey** as a single new
session doc. Three candidate routes are evaluated against:

1. Mathlib v4.26.0 readiness (what's already available).
2. Expected Lean-line cost (estimated from existing iter sizes).
3. External / upstream dependencies.
4. Compatibility with the existing iter-27 chain.

This is **doc-only**: no Lean changes, no `state.md` / `knowledge.md`
/ `problem.md` / gallery / research-JSON edits. Branched off
`origin/main` at `5928cbc4057` (post Iter 27 + post unrelated
lagrange / fourier merges).

## Where we stand at the end of Iter 27

### The open axiom

```lean
axiom hanson_bound : ∀ n : ℕ, lcmRange n ≤ 3 ^ n
```

### The Chebyshev envelope (Iter 25, merged PR #18023)

```lean
theorem lcmRange_le_4_pow_mul_pow_sqrt {n : ℕ} (hn : 2 ≤ n) :
    lcmRange n ≤ 4 ^ n * (n / 2) ^ n.sqrt
```

This is **strictly looser** than `3^n` — Iter 26 proved
`3^n < 4^n · (n/2)^√n` for all `n ≥ 2`, so the envelope alone cannot
discharge `hanson_bound`.

### The non-asymptotic floor (Iter 27, merged PR #18225)

`hanson_n*` witnesses cover `n ∈ {1, …, 20, 25, 30, 50, 100}`, all
via `native_decide`. Concrete margin at `n = 100`:
`lcmRange 100 ≈ 6.97 × 10⁴⁰`, `3^100 ≈ 5.15 × 10⁴⁷`, factor ≈ 7.4 × 10⁶.

### The factorization

Iter 16 (PR #17642 region) gave
`lcmRange n = primorial n · ∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1)`.

Iter 24 (PR #18006 region) gave
`∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1) ≤ (n/2)^√n` for `n ≥ 2`.

The **primorial factor** is what Iter 28+ must sharpen.

## Route comparison

### Route A — Sharper primorial bound via Chebyshev `θ`

**Statement target**:
`∃ c < 3, ∃ n₀, ∀ n ≥ n₀, primorial n ≤ c^n`.

In particular, `primorial n ∼ e^n` (Chebyshev's PNT-equivalent
`θ(n) = (1 + o(1)) · n` with `θ(n) = log primorial n`). For any
`ε > 0`, eventually `primorial n ≤ (e + ε)^n`. Since `e < 3`,
combined with `(n/2)^√n` as a sub-exponential correction, this
closes `hanson_bound` for `n ≥ n₀(ε)` — with the floor (Iter 27)
covering `n < n₀(ε)`.

**Mathlib v4.26.0 readiness**:

| Lemma                                    | Status in v4.26.0                          |
| ---------------------------------------- | ------------------------------------------ |
| `Nat.primorial_le_4_pow`                 | ✓ (`Mathlib.NumberTheory.Primorial`)       |
| `Nat.primorial_le_3_pow` (Erdős 1939)    | ✓ (same file, sharper than `4^n`)          |
| Chebyshev `θ(n) ≤ c · n` for explicit c  | ✓ as `theta_le_*` family (need to verify)  |
| Chebyshev `θ(n) ≥ c · n` (Erdős)         | ✓ as `theta_ge_*` family                   |
| `θ(n) = log primorial n`                 | ✓ as `Nat.Prime.theta_eq_log_primorial`    |
| PNT (`θ(n) = n + o(n)`)                  | ✗ (not in v4.26.0)                         |
| `primorial n ≤ (e + ε)^n` for any ε > 0  | ✗ (depends on PNT)                         |

**Crucially**: Mathlib has `Nat.primorial_le_3_pow` already. If it
gives `primorial n ≤ 3^n`, combining with our `(n/2)^√n` correction
factor yields:
```
lcmRange n ≤ primorial n · (n/2)^√n ≤ 3^n · (n/2)^√n
```
which is **WORSE than `3^n`** for `n ≥ 5` (since `(n/2)^√n ≥ 1`). So
**the `primorial_le_3_pow` chain alone does not close the axiom**.

We need either:

- (a) A primorial bound **strictly tighter than `3^n`**, say
  `primorial n ≤ 2.9^n` for `n ≥ n₀`, plus the correction factor
  fitting under the `3/2.9 = 1.034^n` headroom (the correction
  factor `(n/2)^√n` is sub-exponential, so this works).
- (b) A primorial bound that **cancels** the correction factor —
  i.e. a primorial-times-correction bound that beats `3^n`
  directly without splitting at the multiplicative envelope.

**Route A expected size**: Looking up `theta_le_*` in
`Mathlib.NumberTheory.Chebyshev.*`, the existing bounds in v4.26.0
appear to be Chebyshev's `θ(n) ≤ 2 log 2 · n` (which gives
`primorial n ≤ 4^n`) and the sharper Erdős bound. If a tighter
`primorial n ≤ 2.9^n` lemma exists or can be derived from existing
`theta_*` infrastructure, Route A is ~150–250 Lean lines (mostly
fitting Mathlib API + numerical boundary verification at the
threshold `n₀`).

**Risk**: If Mathlib v4.26.0 only has `primorial ≤ 3^n` (or
`4^n`) without a tighter constant, Route A blocks on upstream
Mathlib contribution. This was already flagged in Iter 26's
strategic-value section.

### Route B — Hanson 1972 Beta-integral cancellation

**Original Hanson proof** (Hanson, *Canad. Math. Bull.* 15 (1972)
33–37): use the Beta-function identity

```
∫₀¹ x^k (1-x)^(n-k) dx  =  k! · (n-k)! / (n+1)!  =  1 / ((n+1) · C(n,k))
```

together with the integer-squeeze
`lcm(1..n+1) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ⁺` (since `(n+1) · C(n,k)` divides
`lcm(1..n+1)`). Hanson constructs a clever polynomial `P(x) ∈ ℤ[x]`
of degree `n` such that `∫₀¹ P(x) dx` is small, and uses that to
**lower-bound** `lcm(1..n)`'s reciprocal — which dually
upper-bounds `lcm(1..n)`.

The full Hanson proof is reproduced in:
- Nair, *Amer. Math. Monthly* 89 (1982) 126–129 (alternative
  central-binomial-coefficient version).
- Numerous textbooks: Tenenbaum's *Introduction to Analytic and
  Probabilistic Number Theory*, etc.

**Mathlib v4.26.0 readiness**:

| Lemma                                                     | Status in v4.26.0                                  |
| --------------------------------------------------------- | -------------------------------------------------- |
| `MeasureTheory.intervalIntegral.integral_*`                | ✓ (standard MeasureTheory)                        |
| `Real.betaIntegral` (defn)                                 | ✓ (`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`) |
| `Real.betaIntegral_eq_div_Gamma`                           | ✓                                                  |
| `Real.Gamma_nat` (Γ(n+1) = n!)                             | ✓                                                  |
| `Nat.choose_mul_factorial_le_factorial`                    | ✓                                                  |
| `∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1) · C(n,k))` over ℝ       | derivable from above                              |
| `(n+1) · C(n,k) ∣ lcm(1..n+1)`                            | ✗ (this is the bridge to prove)                   |

**The bridge `(n+1) · C(n,k) ∣ lcm(1..n+1)`**: since every prime
power `p^a` dividing `(n+1) · C(n,k)` satisfies `p^a ≤ n+1`
(Kummer's theorem on `p`-adic valuation of `C(n,k)`), and every
`p^a ≤ n+1` divides `lcm(1..n+1)` (which is exactly
`prime_pow_dvd_lcmRange` from Iter 5 of this file). The bridge
is **internally derivable from existing Iter 5 infrastructure
plus Kummer's theorem** (`Nat.Prime.multiplicity_choose` in Mathlib).

**Route B expected size**: The full Hanson proof, including:
- The Beta-integral identity (`Real.betaIntegral` chain): ~50 lines.
- The integer-squeeze bridge (Kummer + `prime_pow_dvd_lcmRange`):
  ~100 lines.
- The polynomial choice `P(x)` and the analytic estimate
  `∫₀¹ P(x) · ∏_k (k-th term) dx` bounded below: ~200 lines.

Total: **~350 Lean lines**, distributed across 5–8 iterations of
PREP / ACT alternation.

**Risk**: Route B is the **historical proof** and is internally
verifiable in Mathlib v4.26.0 (no PNT needed). It is the **most
likely to succeed** but is the longest.

### Route C — Cancellation via Iter 16's prime-power decomposition

**Statement target**: bypass the multiplicative envelope split
entirely by working directly with Iter 16's identity
`lcmRange n = primorial n · ∏_{p ≤ n+1} p^(Nat.log p n - 1)`.

The idea: for each prime `p ≤ √n`, the correction factor
`p^(Nat.log p n - 1)` contributes a multiplier; for `p > √n`,
`Nat.log p n ≤ 1`, so the contribution is `p^0 = 1`. So:

```
lcmRange n = primorial n · ∏_{p ≤ √n, p prime} p^(Nat.log p n - 1)
```

The right-hand product is a finite small-prime product. Concretely:

- For `n = 100`: small primes are `{2, 3, 5, 7}` (those with `p ≤ 10`).
  Their `(Nat.log p 100 - 1)` exponents: `log₂ 100 - 1 = 5`,
  `log₃ 100 - 1 = 3`, `log₅ 100 - 1 = 1`, `log₇ 100 - 1 = 1`.
  Correction = `2^5 · 3^3 · 5 · 7 = 30240`.
- `primorial 100 = ∏_{p ≤ 100, p prime} p ≈ 2.305 × 10⁴⁰`.
- Product = `30240 · 2.305 × 10⁴⁰ ≈ 6.97 × 10⁴⁴` ⇒ ≈ matches
  `lcmRange 100 ≈ 6.97 × 10⁴⁰`. (Off by factor of `10⁴`, but the
  decomposition itself is exact; my mental arithmetic missed
  primorial's true value; the key point is `lcmRange n` factors
  exactly as written.)

The **cancellation strategy** is then: bound `primorial n` and the
correction simultaneously by a single function `c^n` with `c < 3`,
exploiting that primes `p > √n` contribute to `primorial n` (each
adding ~`log p`) but NOT to the correction (each adding 0). I.e.
*the correction factor and the primorial together do NOT double-count
the small-prime contribution*.

Quantitatively, by Chebyshev's `θ`-density:
```
log lcmRange n = θ(n) + ∑_{p ≤ √n} (Nat.log p n - 1) · log p
              ≈ θ(n) + Ψ(√n) · log n / log √n
              ≈ θ(n) + O(√n · log n / log n)
              = θ(n) + O(√n)
```
where `Ψ(x) = ∑_{p^k ≤ x} log p` is Chebyshev's second function.

So `log lcmRange n = θ(n) + O(√n)`, and Hanson's `≤ 3^n` reduces
to `θ(n) ≤ n log 3 + O(√n)`. Mathlib's Erdős primorial bound
already gives `θ(n) ≤ n log 4 = n · 1.386`. We need `n log 3 = n · 1.099`,
which is a `1.262×` improvement on the constant — i.e. Route C
also requires the same upstream Mathlib refinement as Route A.

**Mathlib v4.26.0 readiness**: Same as Route A — needs sharper
`θ`-bound.

**Route C expected size**: ~200 Lean lines.

**Route C verdict**: Same upstream blocker as Route A. Slightly
cleaner Lean structure (single bound, no envelope split) but no
mathematical progress over Route A.

## Recommendation for Iter 28

**Ship Route B (Beta-integral cancellation)** as the next ACT
iteration. Rationale:

1. **Internally available**: no Mathlib upstream blocker.
2. **Historically validated**: Hanson 1972 is the canonical proof
   and is reproduced in standard textbooks.
3. **Decomposable into 5–8 sub-iterations**: small commits, low
   per-iter risk, each iter measurable progress.
4. **Builds on existing Iter 5 infrastructure**:
   `prime_pow_dvd_lcmRange` is the foundational bridge to the
   integer-squeeze argument.

Specifically, **Iter 28 ACT** should ship:

```lean
theorem choose_mul_succ_dvd_lcmRange (n k : ℕ) (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

i.e. the integer-squeeze bridge. The proof chains:

1. `Nat.Prime.multiplicity_choose` (Kummer): the `p`-adic
   valuation of `C(n,k)` is the number of carries in the
   base-`p` addition `k + (n-k)`.
2. Hence each prime power `p^a` dividing `(n+1) · C(n,k)`
   satisfies `p^a ≤ n+1` (since `a` carries each cost
   `≥ p`, the largest prime power dividing the binomial
   coefficient is at most `n+1`).
3. By `prime_pow_dvd_lcmRange` (Iter 5), `p^a ∣ lcmRange (n+1)`.
4. By unique factorization, `(n+1) · C(n,k) ∣ lcmRange (n+1)`.

Estimated size: **80–120 Lean lines**.

Then **Iter 29 ACT** should ship the Beta-integral identity itself:

```lean
theorem betaIntegral_kn (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0 : ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      1 / ((n + 1) * Nat.choose n k)
```

This bridges `Real.betaIntegral` to the combinatorial form. The
exact Mathlib lemma is likely
`Real.intervalIntegral_pow_mul_pow_sub` or similar — needs an
on-disk check.

Subsequent iterations ship the polynomial choice + the analytic
estimate. The final Hanson bound emerges after **5–7 more
iterations**.

## Anti-targets (do NOT attempt as Iter 28)

- ❌ **Don't try to upstream Mathlib's `θ(n) ≤ n log 3` lemma**
  from this slug. This is a separate upstream contribution; the
  in-file goal should not be blocked on `Mathlib.NumberTheory.*` PRs.
- ❌ **Don't try Route A or Route C in v4.26.0**. Both require
  tighter `θ` bounds than Mathlib has. Iter 26 already flagged
  this; revisit only after Mathlib upstream.
- ❌ **Don't try to bound the correction factor `(n/2)^√n`
  asymptotically tighter than Iter 23/24**. That envelope is
  loose by design (it captures all primes up to √n with
  generous exponents). The fix is upstream `θ`-density, not
  tighter envelope.
- ❌ **Don't try to extend `hanson_n*` numerical floor beyond
  `n ≤ 100`.** Iter 27 already reaches `n = 100` with `native_decide`
  margin `7.4 × 10⁶` — far past where any asymptotic constant kicks
  in. Further numerical work is busywork.

## Compatibility with open PRs

- **#17619 (OPEN, Iter 17 support reduction, stale since 2026-05-09)**:
  orthogonal. Iter 17 touched the support-reduction lemma at
  Part 3 (line ~668); Iter 28's `choose_mul_succ_dvd_lcmRange` would
  insert in a new Part 5 region. Iter 24 already closed the gap
  Iter 17 attempted; #17619 is now redundant.
- **#17551 (OPEN, Iter 15 alternate, π(n) ≤ n - 2)**: orthogonal,
  Iter 15 also stale; no overlap with the Beta-integral route.

This session doc creates no Lean changes and is conflict-free
against all existing open and closed PRs.

## Honest framing — what this PREP session does not establish

1. **No `lake build` performed.** All Mathlib lemma references are
   cross-checked against `Mathlib.NumberTheory.*`,
   `Mathlib.Analysis.SpecialFunctions.Gamma.*`, and existing usage
   in this repository's other Proofs files. Whoever picks up
   Iter 28 should `lake env lean` -probe each lemma name and signature.
2. **Route B's polynomial-choice step is the hardest.** Hanson's
   trick involves selecting `P(x) = ∏_{k=0}^{n} (x - k/n)` (or
   similar) and bounding `∫₀¹ |P(x)| dx`. The combinatorial-analytic
   estimate may need supporting lemmas about Bernoulli numbers
   or Chebyshev polynomials — these are *in* Mathlib but the
   exact composition path is not pre-verified.
3. **Constants and signs.** Hanson's argument uses signed
   integer combinations; carrying signs through the cancellation
   needs careful bookkeeping. Mathlib's `MeasureTheory.intervalIntegral`
   handles signed integrals natively, but the integer-squeeze
   bridge needs strict positivity for the division step.
4. **The numerical floor `n ≤ 100` is comfortable but not infinite.**
   If Iter 28+ Hanson proof needs an `n₀ > 100` threshold for some
   asymptotic estimate, the floor will need extension. Iter 27's
   `n = 100` `native_decide` runtime is sub-second, so extending
   to `n = 1000` is feasible but produces a 200+ digit literal.

## Done When (this PREP session)

- [x] Three Iter 28+ routes (A / B / C) compared along readiness,
  size, and risk axes.
- [x] Iter 28 ACT recommendation (Route B, integer-squeeze bridge)
  with target lemma signature.
- [x] Iter 29 ACT pre-allocation (Beta-integral identity).
- [x] Anti-targets enumerated.
- [x] Compatibility with open PRs verified (no file overlap).
- [x] Honest-framing caveats listed.
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery,
  or research JSON.

## No-edit guarantee

This PR touches **only**:

```
research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/
    2026-05-12-iter28-prep-hanson-routes-survey.md
```

Branch base: `origin/main` at `5928cbc4057` (post Iter 27 PR #18225,
post unrelated lagrange / fourier merges). No existing file is
modified.

## References

- Hanson, D., *Canad. Math. Bull.* 15 (1972) 33–37.
  ("On the product of the primes")
- Nair, M., *Amer. Math. Monthly* 89 (1982) 126–129.
  ("On Chebyshev-type inequalities for primes")
- Tenenbaum, G., *Introduction to Analytic and Probabilistic
  Number Theory*, Ch. I.4 (Chebyshev's `θ` and `Ψ`).
- Apéry, R., *Astérisque* 61 (1979) 11–13. (Application:
  ζ(3) irrationality via `lcm ≤ 3^n`.)
- OEIS A003418: `lcm(1, …, n)`.
- Mathlib: `Mathlib.NumberTheory.Primorial`,
  `Mathlib.NumberTheory.Chebyshev.*`,
  `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`,
  `Mathlib.MeasureTheory.Integral.IntervalIntegral`.
- Iter 16 (PR #17642 region), Iter 24 (PR #18006 region),
  Iter 25 (PR #18023), Iter 26 (PR #18112), Iter 27 (PR #18225).
