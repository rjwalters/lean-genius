# Problem: Uniform even Dirichlet eta values η(2k) = (1 − 2^{1−2k})ζ(2k) via `hasSum_zeta_nat`

**Slug**: basel-problem-oq-13-oq-01-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap (open-question child of basel-problem-oq-13-oq-01)

## Problem Statement

### Formal Statement

The parent entry `basel-problem-oq-13-oq-01` proves a single fixed instance — the
Dirichlet eta value at `s = 4`:

$$\eta(4) = \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^4} = \frac{7\pi^4}{720},$$

by hand-assembling two hard-coded numerical ingredients (λ(4) = π⁴/96 and the
even-fourth-power sum π⁴/1440). This problem asks for the **uniform** statement
over all positive `k`.

For every integer `k ≥ 1`, the even Dirichlet eta value is

$$\eta(2k) \;=\; \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^{2k}}
   \;=\; \bigl(1 - 2^{\,1-2k}\bigr)\,\zeta(2k),$$

where the closed form for the even zeta value is Euler's formula

$$\zeta(2k) \;=\; \frac{(-1)^{k+1}\,B_{2k}\,(2\pi)^{2k}}{2\,(2k)!}
   \;=\; (-1)^{k+1}\,2^{\,2k-1}\,\pi^{2k}\,\frac{B_{2k}}{(2k)!}.$$

The second form is *exactly* the value supplied by Mathlib's `hasSum_zeta_nat`
(see Known Results), so no separate re-derivation of the zeta closed form is
needed.

The target **Lean theorem** is a single statement quantified over `k` (not a
fixed numeral), of roughly the following shape:

```lean
open scoped Nat  -- for the factorial notation `!`

/-- Uniform even Dirichlet eta value:
    `∑ (-1)^(n+1)/n^(2k) = (1 - 2^(1-2k)) * ζ(2k)` for every `k ≥ 1`. -/
theorem hasSum_eta_nat {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ (2 * k))
      ((1 - (2 : ℝ) ^ (1 - 2 * (k : ℤ)))
        * ((-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k)
            * bernoulli (2 * k) / (2 * k)!)) := by
  sorry
```

A cleaner corollary factors the answer through the zeta value directly, so the
Bernoulli constant never has to be manipulated:

```lean
/-- η(2k) as `(1 - 2^(1-2k))` times the Mathlib zeta value. -/
theorem hasSum_eta_nat' {k : ℕ} (hk : k ≠ 0)
    (Z : ℝ) (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k)) Z) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ (2 * k))
      ((1 - (2 : ℝ) ^ (1 - 2 * (k : ℤ))) * Z) := by
  sorry
```

Deriving `hasSum_eta_nat` from `hasSum_eta_nat'` is then a one-liner: instantiate
`Z` and `hZ` with the value and proof from `hasSum_zeta_nat hk`. Recovering the
parent's `hasSum_eta_four` as the `k = 2` specialization (with `ring`/`norm_num`
to check `(1 − 2^{−3})·π⁴/90 = 7π⁴/720`) should be included as a sanity check.

### Plain Language

The Riemann zeta function `ζ(s) = ∑ 1/n^s` sums the reciprocals of the `s`-th
powers with all-positive signs. The **Dirichlet eta function**
`η(s) = ∑ (-1)^{n+1}/n^s` is its *alternating* cousin: odd-indexed terms keep a
`+` sign and even-indexed terms flip to `−`. The two are linked by the clean
scalar identity `η(s) = (1 − 2^{1−s})ζ(s)`, which comes from removing twice the
even-index part of the zeta series.

At even arguments `s = 2k`, Euler's theorem gives `ζ(2k)` as an explicit rational
multiple of `π^{2k}` (through the Bernoulli numbers). Consequently every even
eta value `η(2k)` also has a closed form: `η(2) = π²/12`, `η(4) = 7π⁴/720`,
`η(6) = 31π⁶/30240`, and so on. The parent gallery entry establishes just the
`η(4)` line, and it does so by re-using two numbers (`π⁴/96` and `π⁴/1440`) that
were themselves computed by hand for the `k = 2` case.

The generalization asks: prove the whole family at once. Replace the fixed
numerical ingredients by a single application of Mathlib's general zeta-value
lemma `hasSum_zeta_nat`, so that the parity-split "eta-from-zeta" template is
formalized **uniformly in `k`** rather than recompiled for each individual
exponent.

### Why This Matters

The parent proof is a pleasant but narrow artifact: it hard-codes `π⁴/96` and
`π⁴/1440`, so producing `η(6)` would require repeating the entire construction
with fresh constants (`λ(6)`, the even-sixth-power sum, etc.). That does not
scale and hides the actual mathematical content, which is a single scalar
identity `η(s) = (1 − 2^{1−s})ζ(s)` that is completely independent of the
particular exponent.

Formalizing the uniform version:

- **Decouples the result from hand-computed constants.** The only analytic input
  becomes Mathlib's `hasSum_zeta_nat`; everything else is algebra on the scalar
  factor `(1 − 2^{1−2k})`.
- **Yields the entire even eta family as free specializations** (`η(2)`, `η(4)`,
  `η(6)`, …) — and re-derives the parent's `η(4)` as one corollary, tying the
  gallery together.
- **Isolates a reusable lemma.** The even/odd parity split that turns a zeta-type
  sum into an eta-type sum is exactly the same idiom used for the lambda values
  `λ(2k) = (1 − 2^{−2k})ζ(2k)` and the alternating beta values; a uniform proof
  gives a template other entries can import instead of re-deriving.

## Known Results

**From the parent chain (verified, 0-axiom):**

- `basel-problem-oq-13-oq-01` (`BaselProblemOQ13OQ01.lean`) — proves the single
  case `η(4) = 7π⁴/720` via `HasSum.even_add_odd` applied to
  `f n = (-1)^{n+1}/n⁴`, with the two subseries values imported from the parent.
- `basel-problem-oq-13` (`BaselProblemOQ13.lean`) — proves
  `hasSum_even_zeta_four : ∑ 1/(2k)⁴ = π⁴/1440` and
  `hasSum_odd_zeta_four : ∑ 1/(2k+1)⁴ = π⁴/96`, itself built on Mathlib's
  `hasSum_zeta_four`.

**From Mathlib (`Mathlib.NumberTheory.ZetaValues`) — verified to exist:**

- `hasSum_zeta_nat {k : ℕ} (hk : k ≠ 0) : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k)) ((-1)^(k+1) * 2^(2*k-1) * π^(2*k) * bernoulli (2*k) / (2*k)!)`
  — the *uniform* even zeta value. This is the key lemma the parent chain does
  not use; the whole point of the generalization is to route through it.
- `hasSum_zeta_two`, `hasSum_zeta_four` — the `k = 1, 2` specializations, proved
  in Mathlib as `convert hasSum_zeta_nat _ using 1` corollaries (a model for how
  to specialize the general form).
- `bernoulli`, `bernoulliFun`, and the Bernoulli-number API (`bernoulli'_two`,
  `bernoulli'_four`, `bernoulli_eq_bernoulli'_of_ne_one`) used to evaluate the
  closed form at particular `k`.

**Standard scalar identity (to be formalized, elementary):**

- `η(s) = (1 − 2^{1−s})ζ(s)`. At `s = 2k`: the even-index subseries of the zeta
  series is `∑ 1/(2m)^{2k} = 2^{−2k} ζ(2k)`, so the odd-index (lambda) part is
  `(1 − 2^{−2k})ζ(2k)`, and `η(2k) = (odd) − (even) = (1 − 2·2^{−2k})ζ(2k) =
  (1 − 2^{1−2k})ζ(2k)`.

## Suggested Approach

The cleanest architecture proves the parity split **once**, parameterized by the
zeta value `Z` and its `HasSum` witness, then specializes.

1. **Even subseries as a scaled zeta.** For fixed `k ≥ 1`, show
   `HasSum (fun m : ℕ => 1 / ((2*m : ℕ) : ℝ)^(2*k)) (2^(-2*k) * Z)` from
   `hZ : HasSum (fun n => 1/(n:ℝ)^(2*k)) Z`. Rewrite `1/(2m)^{2k} = 2^{−2k}·(1/m^{2k})`
   (`push_cast; ring` under the sum, then `hZ.mul_left (2^(-2*k))` — the same
   `.mul_left` move the parent uses with the fixed `1/16`).

2. **The two signed subseries.** Following the parent's `hasSum_eta_four_even` /
   `hasSum_eta_four_odd`, reduce the alternating signs by parity:
   `(-1)^(2m+1) = -1` and `(-1)^(2m+2) = 1` via `pow_succ`, `pow_mul`, `norm_num`.
   This turns the even alternating subseries into `−2^{−2k}·Z` (apply `HasSum.neg`
   to step 1) and the odd alternating subseries into the lambda value
   `(1 − 2^{−2k})·Z`. Obtain the odd/lambda value the way the parent does: the
   full zeta series `hZ` splits as `even + odd` under `HasSum.even_add_odd`, and
   `HasSum.unique` pins the odd part to `Z − 2^{−2k}Z = (1 − 2^{−2k})Z`.

3. **Reassemble η(2k).** Apply `HasSum.even_add_odd` with
   `f n = (-1)^(n+1)/n^(2k)` and the two signed subseries from step 2 to get
   `HasSum f ((−2^{−2k}Z) + (1 − 2^{−2k})Z)`, then `convert … using 1; ring` to
   normalize the scalar to `(1 − 2^{1−2k})·Z`. The `n = 0` term is
   `(-1)^1/0^{2k} = 0` under Lean's division-by-zero convention, exactly as in the
   parent. This yields `hasSum_eta_nat'`.

4. **Instantiate the zeta value.** Define `hasSum_eta_nat` by feeding
   `hasSum_zeta_nat hk` as the `(Z, hZ)` pair into `hasSum_eta_nat'`. The Bernoulli
   closed form rides along untouched.

5. **Recover the parent as a corollary.** Specialize `k = 2` and check
   `(1 − 2^{−3}) · (π⁴/90) = 7π⁴/720` with `norm_num`/`ring`; likewise `k = 1`
   gives `η(2) = π²/12`. Use these as regression tests against
   `hasSum_zeta_two` / `hasSum_zeta_four`.

**Anticipated friction points:**

- **Integer vs. natural exponents on the scalar `2^{1−2k}`.** `2^{1−2k}` needs an
  integer (or real `zpow`) exponent since `1 − 2k < 0`. Keep the exponent as
  `(1 - 2*(k:ℤ))` with `zpow`, or carry `2^{−2k}` as `((2:ℝ)^(2*k))⁻¹` and let
  `field_simp`/`ring` reconcile it. `hasSum_zeta_nat` itself uses `2^(2*k-1)`
  (a `ℕ` subtraction, valid since `k ≥ 1`); mind that `Nat` subtraction when
  cross-checking constants.
- **`open scoped Nat`** is required for the factorial notation `(2*k)!` to parse
  (the parent chain does not use `!`, but the general zeta value does).
- **`push_cast`** discipline on `((2*m : ℕ) : ℝ)` and `((n : ℕ) : ℝ)` casts —
  the parent already relies on this for `1/(2k)⁴ = (1/16)(1/k⁴)`.
- **Summability side-goals** for `even_add_odd` come from `hZ.summable` composed
  with the injections `m ↦ 2m` / `m ↦ 2m+1` (`comp_injective`, as in the parent's
  `hasSum_odd_zeta_four`).

Overall this is a faithful "lift the fixed numerals to a parameter" refactor of
proofs already present in the parent chain, with one genuinely new (but
elementary) lemma: the even subseries equals `2^{−2k}` times the zeta value for
general `k`. No new hard analysis is required.

## Classification
```yaml
tier: B
significance: 6
tractability: 6
tags:
  - number-theory
  - analysis
  - zeta-function
  - eta-function
  - series
```

## Related Gallery Proofs
| Proof | Relevance |
|-------|-----------|
| basel-problem-oq-13-oq-01 | Parent: proves the fixed `s = 4` case (η(4) = 7π⁴/720) this generalizes; supplies the parity-split template |
| basel-problem-oq-13 | Grandparent: even/odd fourth-power sums (π⁴/1440, λ(4) = π⁴/96) built on `hasSum_zeta_four` |
| basel-problem-oq-08 | ζ(4) = π⁴/90; η(4) = (1 − 1/8)ζ(4) is its alternating restriction |
| basel-problem | Root: ζ(2) = π²/6, the `k = 1` seed of the even zeta/eta family |
