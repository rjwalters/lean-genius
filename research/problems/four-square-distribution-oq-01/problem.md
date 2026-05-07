# Problem: Jacobi's Four-Square Formula r₄(n) = 8·σ*(n) in Lean 4

**Slug**: four-square-distribution-oq-01
**Source**: gallery-gap (parent: `four-square-distribution`, OQ-01 in `meta.json` `conclusion.openQuestions[0]`)

## Problem Statement

### Formal Statement

For every integer n ≥ 1,
$$
r_4(n) \;:=\; \#\{(a,b,c,d) \in \mathbb{Z}^4 \;:\; a^2 + b^2 + c^2 + d^2 = n\} \;=\; 8 \sum_{\substack{d \mid n \\ 4 \nmid d}} d.
$$

In the Lean file `Proofs/FourSquareDistributionOQ01.lean`, this is encoded as
```lean
axiom jacobi_r4_formula : ∀ n : ℕ, 0 < n → r4Count n = jacobiR4 n
```
where `r4Count` is the brute-force enumeration over signed integer 4-tuples and
`jacobiR4 n := 8 * sigmaStar n`.

### Plain Language

Lagrange (1770) showed that every non-negative integer is a sum of four
squares, but his proof gives only existence. Jacobi (1834) proved a much
stronger quantitative fact: the *exact number* of ways to write n as a sum
of four squares (counting signed, ordered tuples) equals
$8 \sum_{d \mid n,\, 4 \nmid d} d$ — eight times the sum of those divisors
of n that are not divisible by four.

This file's parent — `four-square-distribution` — already analyses the
*relative* distribution among representation types (sorted absolute-value
4-tuples), proving e.g. that type (0,0,0,1) contributes 8 and type
(1,2,3,4) contributes 384. The parent OQ-01 asks the *absolute* question:
**can we prove Jacobi's exact-count formula in Lean 4?**

### Why This Matters

1. **Bridges combinatorics and analytic number theory.** The factor of 8 in
   r₄(n) = 8σ*(n) is opaque from a purely combinatorial viewpoint, but
   transparent once one identifies r₄(n) as the n-th Fourier coefficient
   of θ(q)⁴, recognizes θ⁴ as a weight-2 modular form on Γ₀(4), and
   computes its q-expansion via Eisenstein series.
2. **Foundational testcase for Mathlib's modular-forms infrastructure.**
   Mathlib has `JacobiTheta` and `EisensteinSeries`, but no fully worked
   example bridging to a classical arithmetic identity. Jacobi's r₄ is
   the smallest such bridge: weight 2, level 4, single explicit identity.
3. **Cross-validates the gallery's combinatorial work.** The numerical
   verifications in this file independently confirm `four-square-distribution`'s
   per-type contribution sums (n = 1..7, 9, 10) by an entirely different
   route (divisor sums), giving extra confidence in the gallery.

## Known Results

### What's Already Proven

- **Lagrange (1770) — existence**: every n ≥ 0 is a sum of four squares.
  Mathlib: `Nat.sum_four_squares` in `Mathlib.NumberTheory.SumFourSquares`.
- **Jacobi (1834) — exact count**: r₄(n) = 8 σ*(n) for n ≥ 1.
  *Pencil-and-paper*; not yet formalized in Lean / Mathlib.
- **Distribution among types** (this gallery): for n = 1..7, 9, 10, the
  contribution sum across sorted types matches the classical r₄ values.
  See `four-square-distribution` (verified, 38 theorems, 0 axioms).
- **Numerical verification of Jacobi's formula for n = 1..10** (this file):
  proved here by `native_decide` from three independent definitions
  (brute enumeration, divisor sum, type decomposition).

### What's Still Open

- **General Jacobi formula in Lean**: the axiom `jacobi_r4_formula`
  asserting r4Count n = jacobiR4 n for all n ≥ 1 is the open target.
- **Q-expansion infrastructure for `jacobiTheta`** in Mathlib: no general
  lemma extracting Fourier coefficients of `jacobiTheta τ` as a function
  of `τ`.
- **Identification of θ⁴ as a weight-2 Eisenstein combination**: there is
  no Lean theorem yet stating that `jacobiTheta τ ^ 4` equals the
  Eisenstein-series combination `1 + 8 (E₂(τ) − 4 E₂(4τ))` (up to
  normalization).

### Our Goal

The goal of this OBSERVE/ORIENT phase is:
1. Pin down the formal Lean target (`r4Count n = jacobiR4 n`).
2. Provide numerical evidence for n = 1..10 via three independent
   definitions converging to the same answer.
3. Catalogue the Mathlib infrastructure currently available and the gaps
   that must be closed before the axiom can be replaced by a theorem.
4. State the axiom in a form that future ACT-phase work can refine
   incrementally (replace with theorem when modular-form bridge lands).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `four-square-distribution` | Parent. Proves the *relative* type contributions sum to 8σ*(n) for n = 1..7, 9, 10. | `RepType` structure, `native_decide`, multinomial coefficients. |
| `lagrange-four-squares` | Existence theorem (Lagrange 1770). | Mathlib `Nat.sum_four_squares`. |
| `lagrange-four-squares-oq-01` | Three-square theorem (Legendre). Sister problem. | Same. |
| `lagrange-four-squares-oq-02` | Distribution analysis (overlapping with this OQ). | `RepType`, type enumeration. |

## Initial Thoughts

### Potential Approaches

1. **Modular-form bridge** (Approach A — canonical). State and prove
   that `jacobiTheta τ ^ 4` is a weight-2 modular form on Γ₀(4),
   identify it as `1 + 8 (E₂(τ) − 4 E₂(4τ))` up to normalization, and
   extract the q-expansion. Requires:
   - q-expansion lemma for `jacobiTheta` (currently absent).
   - Eisenstein series E₂ at level 4 (partial in `Mathlib.NumberTheory.ModularForms.EisensteinSeries`).
   - A 1-dimensionality argument for the relevant modular-form space.
   - Why it might work: the proof is classical and very well understood.
   - Risk: requires Mathlib upstream work; may take many person-months.

2. **Gauss sum / quadratic reciprocity route** (Approach B). Express
   r₄(n) via Gauss sums and use multiplicativity. Could potentially
   avoid full modular-form infrastructure but still needs character
   theory mod 4. Mathlib has Gauss sums (`Mathlib.NumberTheory.Cyclotomic.Gaussian`).
   - Why it might work: more elementary infrastructure required.
   - Risk: still needs the multiplicative case-analysis, which is itself
     non-trivial.

3. **Structural reduction via Hurwitz quaternions** (Approach C). Identify
   `r₄(n)` with the count of Hurwitz integers of norm n. The Hurwitz
   order has class number 1 and 24 left-units, and divisibility-by-4
   in σ* corresponds to ramification at the prime 2. Mathlib has
   quaternions but no Hurwitz-integer arithmetic.
   - Why it might work: gives a fully algebraic proof avoiding analysis.
   - Risk: requires development of Hurwitz arithmetic in Mathlib;
     larger upstream cost than (A).

### Key Difficulties

- **Q-expansion machinery for `jacobiTheta`** is the central missing
  piece. Without it, no identification of Fourier coefficients is
  possible in Lean.
- **Modular-form theorem of identification** (E₂ characterization) needs
  a finite-dimensionality result: weight-2 modular forms on Γ₀(4) form
  a 2-dimensional space spanned by `E₂(τ)` and `E₂(2τ)` (or equivalent).
- **Bookkeeping between conventions**: many Mathlib normalizations
  (jacobiTheta uses τ vs q, summing over Z vs N⁺) require care.

### What Would a Proof Need?

- Key lemma 1: `jacobiTheta τ = ∑' k : ℤ, exp (π * I * k^2 * τ)` with
  Fourier coefficient extraction.
- Key lemma 2: `jacobiTheta τ ^ 4` is a weight-2 modular form on Γ₀(4).
- Key lemma 3: identification with `1 + 8 (E₂(τ) − 4·E₂(4τ))`.
- Key lemma 4: Fourier coefficient of `E₂(τ) − 4·E₂(4τ)` equals σ*(n).
- Technical requirements: q-expansion of `jacobiTheta` (Mathlib gap),
  `MeromorphicAt` infrastructure for modular-form identification.

## Tractability Assessment

**Difficulty**: High (a multi-month, multi-file Mathlib upstream
contribution; not single-session work).

**Justification**:
- The mathematical content is classical and well-understood.
- The Lean obstacles are infrastructural, not mathematical.
- Comparable formalization efforts (e.g. PNT in Mathlib) took several
  person-years.
- A bottom-up incremental approach (q-expansion → E₂ identification →
  r₄ bridge) is feasible.

**Estimated Effort**:
- Exploration / OBSERVE (this file): ~1 session (DONE).
- Mathlib q-expansion of `jacobiTheta`: months.
- Full Jacobi r₄ formalization: a year+.

## References

### Papers
- Jacobi, *Fundamenta nova theoriae functionum ellipticarum* (1834) —
  original proof via theta-function identities.
- Lagrange, *Démonstration d'un théorème d'arithmétique* (1770) —
  existence theorem.
- Hardy & Wright, *An Introduction to the Theory of Numbers*, Ch. XX —
  modern presentation of Jacobi's theorem.

### Online Resources
- Wikipedia: *Jacobi's four-square theorem* — historical and proof
  overview.

### Mathlib
- `Mathlib.NumberTheory.SumFourSquares` — Lagrange existence theorem.
- `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` —
  `jacobiTheta` definition with `_T_sq_smul` and `_S_smul`.
- `Mathlib.NumberTheory.ModularForms.EisensteinSeries.*` — Eisenstein
  series, modular invariance, bounded-at-cusp.
- `Mathlib.NumberTheory.Divisors` — `Nat.divisors`, used for `sigmaStar`.

## Metadata

```yaml
tags:
  - number-theory
  - sums-of-squares
  - jacobi
  - modular-forms
  - open-question
  - research-bootstrap
related_proofs:
  - four-square-distribution
  - lagrange-four-squares
  - lagrange-four-squares-oq-01
difficulty: high
source: gallery-gap
created: 2026-05-06T16:07:08+03:00
updated: 2026-05-07
```

**Significance**: 7/10
**Tractability**: 3/10 (full proof is a long Mathlib upstream effort)
