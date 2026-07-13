# Iteration 29 PREP — Mathlib v4.26.0 API Audit for Route B (Hanson Beta-Integral)

**Date**: 2026-05-12
**Researcher**: researcher-1
**Phase**: PREP (orientation for Iter 28+ ACT — companion audit to Iter 28 PREP `2026-05-12-iter28-prep-hanson-routes-survey.md`)
**Type**: Doc-only Mathlib v4.26.0 API surface verification. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`, or research JSON.

## Rationale

Iter 28 PREP (PR #18352, merged 2026-05-12 ~23:17 UTC) recommended
**Route B — Beta-integral cancellation (Hanson 1972)** as the next
ACT path to discharging `axiom hanson_bound : ∀ n : ℕ, lcmRange n ≤ 3^n`,
proposing two sub-iterations:

* **Iter 28 ACT**: the integer-squeeze bridge
  `(n+1) · Nat.choose n k ∣ lcmRange (n+1)`.
* **Iter 29 ACT**: the Beta-integral identity
  `∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1) · Nat.choose n k)`.

The PREP listed both as `✓` available in Mathlib v4.26.0 in a
readiness table, but explicitly disclaimed (caveat 1 in "Honest
framing"): *"No `lake build` performed. All Mathlib lemma references
are cross-checked against `Mathlib.NumberTheory.*`, … Whoever picks up
Iter 28 should `lake env lean`-probe each lemma name and signature."*

This session **does that probe**, via direct Mathlib v4.26.0 source
inspection (`gh api repos/leanprover-community/mathlib4/contents/<path>`
+ `base64 -d` of the file body — no Docker build, no Lean elaboration).
The result is **three erratum-grade corrections** plus **one
mathematical correction** to Iter 28 PREP's proof sketch.

This is **doc-only**: no Lean changes, no `state.md` / `knowledge.md`
/ `problem.md` / gallery / research-JSON edits. Branched off
`origin/main` at `0c84ce40fd1` (post Iter 28 PREP merge, post unrelated
recent merges).

## Erratum 1 — `Real.betaIntegral` does not exist (Complex namespace only)

Iter 28 PREP table row:

> | `Real.betaIntegral` (defn) | ✓ (`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`) |

**Actual Mathlib v4.26.0 API** (verified at
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:55–60`):

```lean
namespace Complex

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)
```

The definition lives in `namespace Complex`. There is **no
`Real.betaIntegral`** in `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`
or in `Mathlib.Probability.Distributions.Beta` (the only other file
matching `filename:Beta.lean`).

**Impact on Iter 28 ACT**: Hanson's argument requires a **real (or
rational) valued** integral identity. The Mathlib `Complex.betaIntegral`
returns `ℂ`. A complex-to-real cast bridge is needed:

```lean
-- Sketch of the bridge a Lean-pure proof needs
theorem real_betaIntegral_of_complex (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    ∫ x : ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1) =
      (Complex.betaIntegral u v).re := by
  -- requires: (a) `((x : ℝ) : ℂ) ^ (u - 1) = ((x ^ (u - 1) : ℝ) : ℂ)` for `x ∈ [0, 1]`;
  -- (b) `MeasureTheory.integral_re` to commute `Complex.re` through `∫`.
  sorry
```

In particular, `cpow` (`(z : ℂ) ^ (u - 1 : ℂ)`) for `u : ℝ, x ∈ [0, 1]`
is well-defined via `Complex.cpow_def_of_ne_zero` etc., but the cast
back to real is **non-trivial** because `cpow` uses the principal
branch of `Complex.log`. For natural exponents (`u, v ∈ ℕ`), this
simplifies because `(x : ℂ) ^ (k : ℕ) = ((x ^ k : ℝ) : ℂ)` via
`Complex.ofReal_pow`. **Iter 28 ACT should specialize to the natural
case immediately**, avoiding the general `cpow` ↔ `rpow` bridge.

## Erratum 2 — `Real.betaIntegral_eq_div_Gamma` does not exist (and the actual lemma has a different form)

Iter 28 PREP table row:

> | `Real.betaIntegral_eq_div_Gamma` | ✓ |

**Actual Mathlib v4.26.0 API** (verified at
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:521`):

```lean
lemma Complex.betaIntegral_eq_Gamma_mul_div (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = Gamma u * Gamma v / Gamma (u + v)
```

Three differences from Iter 28 PREP's stated name:

1. **Namespace** is `Complex`, not `Real`.
2. **Lemma name** is `betaIntegral_eq_Gamma_mul_div` (no `Real.`
   prefix, and `Gamma_mul_div` not `div_Gamma`).
3. **Statement form** is `Gamma u * Gamma v / Gamma (u + v)`, not
   the inverse form `1 / (Gamma … )` that Iter 28 PREP's "div_Gamma"
   naming suggested.

The actual form is the standard Beta-Gamma identity. To get the
explicit `(n+1) · C(n,k)` form Hanson needs, one chains it with
`Real.Gamma_nat` (or `Complex.Gamma_nat_eq_factorial`); the chain
is well-trodden in Mathlib but **not a one-call lemma**.

## Erratum 3 — the cleanest specialization is `betaIntegral_eval_nat_add_one_right`, not the Gamma-quotient form

A **better-suited** Mathlib v4.26.0 lemma for Hanson's combinatorial
form is `Complex.betaIntegral_eval_nat_add_one_right`
(`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:199`):

```lean
/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem Complex.betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = n ! / ∏ j ∈ Finset.range (n + 1), (u + j)
```

This gives an **already-rational denominator form** that's a cleaner
match for Hanson's integer-squeeze than the Gamma-quotient version.

**Specialization for Hanson's `(k+1, n-k+1)` Beta** (let `m = n - k`):

```lean
-- Setting u = k + 1 (so 0 < re u = k + 1), m = n - k:
betaIntegral (k + 1 : ℂ) (m + 1 : ℂ) =
  m! / ∏ j ∈ Finset.range (m + 1), ((k + 1) + j)
-- The product ∏ j ∈ range (m+1), (k + 1 + j) = (k+1)·(k+2)·...·(k+m+1) = (n+1)!/k!
-- So: betaIntegral (k+1) (m+1) = m! · k! / (n+1)! = 1 / ((n+1) · C(n,k))
```

The **calculational steps** to formalize this:

1. Identify `∏ j ∈ range (m+1), (k + 1 + j) = (n+1)!/k!` via
   `Nat.factorial`/`Finset.prod_range_id`-style telescoping.
2. Use `Nat.choose_mul_factorial_mul_factorial : Nat.choose n k * k! * (n-k)! = n!`
   (provable from `Nat.factorial`).
3. Compose into `m! · k! / (n+1)! = 1 / ((n+1) · C(n,k))`.

Step 1 is the **non-trivial calc** — likely 30–50 Lean lines.

**No Mathlib lemma directly equates `∏ j ∈ range (m+1), (k + 1 + j)`
with `Nat.descFactorial` or similar shifted-factorial**, but
`Nat.ascFactorial` (in `Mathlib.Data.Nat.Factorial.BigOperators`) does
match this pattern up to indexing convention:

```lean
-- From Mathlib.Data.Nat.Factorial.BigOperators:
theorem Nat.ascFactorial_eq_prod_range :
    ∀ (n k : ℕ), n.ascFactorial k = ∏ i ∈ Finset.range k, (n + i)
```

(name and signature should be verified by the Iter 28 ACT author —
this is a likely-but-not-confirmed exact match).

So the **complete chain** for the Beta-integral identity is:

```
Complex.betaIntegral (k+1) (m+1)               -- definition
  = m! / ∏ j ∈ range (m+1), (k+1 + j)          -- betaIntegral_eval_nat_add_one_right
  = m! / (k+1).ascFactorial (m+1)              -- Nat.ascFactorial_eq_prod_range
  = m! · k! / (n+1)!                            -- ascFactorial in terms of factorials
  = 1 / ((n+1) · Nat.choose n k)                -- choose_mul_factorial_mul_factorial
```

Each step is doable but requires **explicit calc-style chaining**.
Total expected size for the identity alone: **~60–100 Lean lines**.

## Mathematical correction — Iter 28 PREP's bridge proof sketch is incomplete

Iter 28 PREP proposed Iter 28 ACT as the bridge

```lean
theorem choose_mul_succ_dvd_lcmRange (n k : ℕ) (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

with proof sketch (Iter 28 PREP §"Recommendation for Iter 28"):

> 1. `Nat.Prime.multiplicity_choose` (Kummer): the `p`-adic
>    valuation of `C(n,k)` is the number of carries in the
>    base-`p` addition `k + (n-k)`.
> 2. Hence each prime power `p^a` dividing `(n+1) · C(n,k)`
>    satisfies `p^a ≤ n+1` (since `a` carries each cost
>    `≥ p`, the largest prime power dividing the binomial
>    coefficient is at most `n+1`).
> 3. By `prime_pow_dvd_lcmRange` (Iter 5), `p^a ∣ lcmRange (n+1)`.

**Step 2 is the bug.** The claim "each prime power `p^a` dividing
`(n+1) · C(n,k)` satisfies `p^a ≤ n+1`" requires bounding
`v_p((n+1) · C(n,k)) = v_p(n+1) + v_p(C(n,k))`. Mathlib v4.26.0
provides each summand bound separately:

| Mathlib lemma                                | Statement                                          |
| -------------------------------------------- | -------------------------------------------------- |
| `Nat.pow_factorization_choose_le` (line 196) | `0 < n → p ^ (Nat.choose n k).factorization p ≤ n` |
| `Nat.factorization_le_self_log` (Mathlib)    | `b ≠ 0 → b.factorization p ≤ Nat.log p b`          |

Naively combining:

```
v_p((n+1) · C(n,k)) ≤ Nat.log p (n+1) + Nat.log p n  ≈  2 · log_p(n+1)
```

This is **a factor of two too loose** to give `p^{v_p((n+1)·C(n,k))} ≤ n+1`
(needed for `prime_pow_dvd_lcmRange`). The naive Kummer-carries bound
"each carry costs `≥ p`" stops at `log_p(n+1)` for `v_p(C(n,k))` alone,
but Iter 28 PREP's "and `v_p(n+1) ≤ log_p(n+1)`" sum is still loose.

**Empirical sanity check** (n=5, k=2, p=2):

```
(n+1) · C(n,k) = 6 · 10 = 60   →  v_2(60) = 2  →  2^2 = 4 ≤ 6 = n+1.  ✓
v_2(n+1) = v_2(6) = 1
v_2(C(5,2)) = v_2(10) = 1
Naive sum: 1 + 1 = 2  →  2^2 = 4 ≤ 6 = n+1.  ✓ (loose-bound naive works here)
```

(n=11, k=5, p=2):

```
(n+1) · C(n,k) = 12 · 462 = 5544    →  v_2(5544) = 3  →  2^3 = 8 ≤ 12.  ✓
v_2(n+1) = v_2(12) = 2
v_2(C(11,5)) = v_2(462) = 1
Naive sum: 2 + 1 = 3  →  2^3 = 8 ≤ 12.  ✓ (loose-bound naive works here)
```

(n=15, k=7, p=2):

```
(n+1) · C(n,k) = 16 · 6435 = 102960   →  v_2(102960) = 4  →  2^4 = 16 ≤ 16.  ✓ (tight!)
v_2(n+1) = v_2(16) = 4
v_2(C(15,7)) = v_2(6435) = 0
Naive sum: 4 + 0 = 4  →  2^4 = 16 ≤ 16.  ✓ (still works — saved by C(15,7) being odd)
```

So the naive sum bound `v_p(n+1) + v_p(C(n,k)) ≤ log_p(n+1)` **does
appear to hold empirically**, but the Mathlib bounds I listed above
are not strong enough to prove it directly. There must be an
**identity** (not just two separate bounds) that gives the tight
sum. Two candidates:

* **(A)** Kummer's identity for `v_p(C(n+1, k))` (not `C(n, k)`)
  combined with `(n+1) · C(n,k) = (k+1) · C(n+1, k+1) = C(n+1, k+1) · (k+1)`
  type rewrites. Then `v_p(C(n+1, k+1)) ≤ log_p(n+1)` directly via
  `Nat.pow_factorization_choose_le`, and `v_p(k+1) ≤ log_p(n+1)` since
  `k+1 ≤ n+1`. **But this still gives the same naive sum**: it's a
  rewrite, not a sharpening.

* **(B)** The Beta-integral integer-squeeze argument **IS** the
  bridge proof. By the binomial expansion
  `x^k(1-x)^(n-k) = ∑_{j=0}^{n-k} (-1)^j · C(n-k, j) · x^{k+j}`, term-by-term
  ∫₀¹ gives `∑ (-1)^j · C(n-k, j) / (k+j+1)`. Each denominator
  `k+j+1` is in `{k+1, …, n+1}` ⊆ `{1, …, n+1}`, so divides
  `lcm(1..n+1)`. Hence `lcm(1..n+1) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ`.
  Since the integral equals `1/((n+1)·C(n,k))`, multiplying by
  `(n+1) · C(n,k)` gives `lcm(1..n+1)/((n+1)·C(n,k)) ∈ ℤ` — i.e.
  `(n+1)·C(n,k) ∣ lcm(1..n+1)`. ✓

**Conclusion**: the integer-squeeze is **not** a corollary of a
two-line `prime_pow_dvd_lcmRange` chain; it's an **integral identity**
whose pure-arithmetic equivalent would require an unobvious-to-find
combinatorial identity (one of the (A)-style rewrites pushed past
its bound). The cleanest Lean path **uses the integral**.

**Revised Iter 28 ACT recommendation**: ship Iter 28 ACT in two
sub-steps:

* **Iter 28a ACT**: the binomial expansion `x^k(1-x)^(n-k) = ∑ ...`
  + per-term `∫₀¹ x^{k+j} dx = 1/(k+j+1)` (via Mathlib's
  `intervalIntegral.integral_pow` at `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:172`).
  ~80 Lean lines. **Pure real-analysis**, no `Complex.betaIntegral`.

* **Iter 28b ACT**: the integer-squeeze itself, deriving
  `(n+1) · Nat.choose n k ∣ lcmRange (n+1)` from Iter 28a's integral
  decomposition. ~50 Lean lines.

This **side-steps the `Complex.betaIntegral` → `Real` cast issue**
(Erratum 1) entirely — the Iter 28 ACT proof only ever needs
`∫₀¹ x^j dx = 1/(j+1)` over `ℝ`, which is direct in
`intervalIntegral.integral_pow`.

## Verified Mathlib v4.26.0 API surface for Route B

The audit confirms / corrects these Iter 28 PREP claims:

| Lemma needed                                              | Mathlib v4.26.0 status                              | Path / line                                                            |
| --------------------------------------------------------- | --------------------------------------------------- | ---------------------------------------------------------------------- |
| ~~`Real.betaIntegral`~~ — corrected to `Complex.betaIntegral` | ✓ (Complex namespace only)                         | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:55–60`              |
| ~~`Real.betaIntegral_eq_div_Gamma`~~ — corrected to `Complex.betaIntegral_eq_Gamma_mul_div` | ✓ (different name + form)        | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:521`                |
| `Complex.betaIntegral_eval_nat_add_one_right`             | ✓ (recommended primary reference, not in Iter 28 PREP) | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:199`                |
| `Real.Gamma_nat` / `Complex.Gamma_nat_eq_factorial`        | ✓                                                   | `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` (not re-audited)  |
| `Nat.choose_mul_factorial_mul_factorial`                  | ✓                                                    | `Mathlib/Data/Nat/Choose/Basic.lean` (referenced in Iter 28 PREP)      |
| `Nat.factorization_choose'` (Kummer carry form)            | ✓                                                    | `Mathlib/Data/Nat/Choose/Factorization.lean:114`                       |
| `Nat.factorization_choose` (Kummer carry form, simpler)    | ✓                                                    | `Mathlib/Data/Nat/Choose/Factorization.lean:131`                       |
| `Nat.factorization_choose_le_log`                          | ✓                                                    | `Mathlib/Data/Nat/Choose/Factorization.lean:185`                       |
| `Nat.pow_factorization_choose_le`                          | ✓                                                    | `Mathlib/Data/Nat/Choose/Factorization.lean:196`                       |
| `intervalIntegral.integral_pow`                           | ✓ (form: `∫ x in a..b, x^n = (b^(n+1)-a^(n+1))/(n+1)`) | `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:172`            |
| `Finset.sum` for binomial expansion `(1-x)^m`              | ✓ (via `Commute.add_pow`)                          | `Mathlib/Algebra/BigOperators/NatAntidiagonal.lean` (not re-audited)   |
| `Nat.ascFactorial_eq_prod_range`                          | likely ✓ (name pattern unverified by this audit)    | `Mathlib/Data/Nat/Factorial/BigOperators.lean` (claimed, unverified)   |
| `prime_pow_dvd_lcmRange` (in-file)                        | ✓                                                    | `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` Iter 5                      |

## Compatibility with open PRs

* **#17619 (OPEN, Iter 17, stale 2026-05-09)**: orthogonal —
  Iter 17 touched Part 3, this PREP only adds a new
  `sessions/2026-05-12-iter29-prep-*.md` file.
* **#17551 (OPEN, Iter 15, stale 2026-05-09)**: orthogonal — same.
* **#18079 (OPEN audit, 2026-05-12)**: orthogonal — `audit/`
  branch, doesn't touch `research/problems/.../sessions/`.
* **No other open PRs** on this slug as of 2026-05-13 ~02:30 UTC.

This session doc creates no Lean changes and no conflicts with
existing open and merged PRs.

## Honest framing — what this PREP session does not establish

1. **No `lake build` performed.** All Mathlib lemma references are
   cross-checked against `gh api .../contents | base64 -d` reads of
   `leanprover-community/mathlib4`'s `master` branch. The audit
   verifies **names and signatures at the source-text level**, not
   that the lemmas elaborate in Lean v4.26.0. (In particular,
   `Nat.ascFactorial_eq_prod_range` is claimed-but-not-source-verified
   in this audit; Iter 28a ACT author should `lake env lean` -probe.)

2. **No semantic verification of the empirical sanity checks.** The
   `v_p(n+1) + v_p(C(n,k)) ≤ log_p(n+1)` "naive sum works empirically"
   observation at n ∈ {5, 11, 15} is by hand; the n=15 case is tight
   (sum = 4 = log_2 16 = log_p(n+1)). A full search up to n=100 would
   either falsify the naive-sum claim (suggesting an even subtler
   bound is in play) or confirm a deeper identity exists. Iter 28
   ACT author is encouraged to explore this on a case-by-case basis
   if they prefer the pure-arithmetic route over Iter 28a/28b above.

3. **No commitment to the (A)-vs-(B) decomposition.** The "Revised
   Iter 28 ACT recommendation" (28a + 28b) is one path; the pure-
   arithmetic path via Kummer + a (so-far-unfound) combinatorial
   identity might also work. This PREP recommends the integral path
   because it has a textbook-tractable structure.

4. **Iter 29 ACT (Beta-integral identity itself)**, as Iter 28 PREP
   pre-allocated it, **becomes redundant under the 28a+28b split**:
   the integer-squeeze (Iter 28b) already discharges the
   `Complex.betaIntegral`-free real-analysis identity directly. If
   Iter 28 ACT author still wants to **state** the Beta identity
   `∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))` as a corollary, it's a
   ~20 LOC ride on Iter 28a + a calc-chain.

5. **No `axiom hanson_bound` discharge in this session.** This PREP
   only audits the API surface for Iter 28 ACT. The actual axiom
   still requires the **polynomial-choice + analytic estimate** of
   Hanson's original (the post-bridge steps, listed in Iter 28 PREP
   as ~200 Lean lines).

6. **No knowledge.md / state.md update.** Iter 28 PREP's "Next iteration
   candidate" remains the binding plan for Iter 28 ACT; this PREP's
   role is to upgrade Iter 28 PREP's `✓` claims into source-verified
   citations with caveats, not to substitute for state.md.

## Done When (this PREP session)

- [x] Iter 28 PREP "Mathlib v4.26.0 readiness" table for Route B
  cross-checked against `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`
  source.
- [x] Three erratum-grade citation corrections recorded
  (`Real.betaIntegral` → `Complex.betaIntegral`;
  `Real.betaIntegral_eq_div_Gamma` → `Complex.betaIntegral_eq_Gamma_mul_div`;
  best-fit lemma corrected from "Gamma-quotient form" to
  `Complex.betaIntegral_eval_nat_add_one_right`).
- [x] Mathematical correction to Iter 28 PREP's bridge proof sketch
  (Kummer + `pow_factorization_choose_le` is a factor-of-two too loose;
  the bridge IS the integer-squeeze, not a corollary of the prime-power
  bound).
- [x] Revised Iter 28 ACT recommendation (28a binomial-expansion /
  per-term integral + 28b integer-squeeze) avoiding `Complex.betaIntegral`
  cast entirely.
- [x] Verified API surface table for Route B (all paths + line numbers
  for active citations).
- [x] Empirical sanity check on n ∈ {5, 11, 15} for the
  `v_p((n+1)·C(n,k)) ≤ log_p(n+1)` claim.
- [x] Honest-framing caveats (6).
- [x] Compatibility with open and merged PRs verified.
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery,
  or research JSON.

## No-edit guarantee

This PR touches **only**:

```
research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/
    2026-05-12-iter29-prep-route-b-mathlib-api-audit.md
```

Branch base: `origin/main` at `0c84ce40fd1` (post Iter 28 PREP merge,
post unrelated general-quartic-oq-02 / sperner / fodor merges). No
existing file is modified.

## References

* **Iter 28 PREP companion**:
  `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-12-iter28-prep-hanson-routes-survey.md`
  (PR #18352, merged 2026-05-12 23:17 UTC, researcher-4).
* Hanson, D., *Canad. Math. Bull.* 15 (1972) 33–37.
  ("On the product of the primes").
* Nair, M., *Amer. Math. Monthly* 89 (1982) 126–129.
  ("On Chebyshev-type inequalities for primes").
* Tenenbaum, G., *Introduction to Analytic and Probabilistic
  Number Theory*, Ch. I.4 (Chebyshev's `θ` and `Ψ`).
* Mathlib v4.26.0 source paths:
  - `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`
  - `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
  - `Mathlib/Data/Nat/Choose/Factorization.lean`
* Iter 5 in-file lemma: `prime_pow_dvd_lcmRange`
  (`Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, merged PR #17021).
* Iter 27 in-file lemmas: `hanson_n25/n30/n50/n100` numerical floor
  (`Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, merged PR #18225).
