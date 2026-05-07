# Problem: Hanson's Bound lcm(1,...,n) ≤ 3^n in Lean 4

**Slug**: basel-problem-oq-01-oq-01-oq-02-oq-03
**Source**: gallery-extracted (parent: `basel-problem-oq-01-oq-01-oq-02`, axiom `lcm_hanson_bound`)

## Problem Statement

### Formal Statement

For every n ≥ 1,
$$
\operatorname{lcm}(1, 2, \ldots, n) \leq 3^n.
$$

In the Lean file `Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean`, this is encoded as
```lean
axiom hanson_bound : ∀ n : ℕ, lcmRange n ≤ 3 ^ n
```
where `lcmRange n := (Finset.range n).lcm (· + 1)` matches the parent file's `lcmUpTo`.

### Plain Language

The least common multiple of `{1, 2, ..., n}` grows roughly like `eⁿ` by the
prime number theorem, but explicit non-asymptotic bounds are non-trivial
to prove. Hanson (1972) gave the explicit bound `lcm(1,...,n) ≤ 3ⁿ`,
which is the tightest known constant in this form.

### Why This Matters

1. **Apéry's irrationality theorem depends on Hanson's exact constant.**
   Apéry's 1979 proof that ζ(3) is irrational uses the integer-squeeze
   argument: rational approximations `(aₙ, bₙ)` satisfying `bₙ·ζ(3) - aₙ → 0`
   fast enough force ζ(3) irrational. The threshold is precisely
   `c = (1/(17 - 12√2))^{1/3} ≈ 3.245`. Any bound `lcm(1,...,n) ≤ cⁿ`
   with `c ≥ 3.245` fails. Hanson's `3ⁿ` succeeds; the easier `4ⁿ`
   fails. This is the entire reason `lcm_hanson_bound` is one of
   the five axioms in `BaselProblemOQ01OQ01OQ02.lean`.

2. **Foundational testcase for non-asymptotic prime-distribution bounds.**
   The function `ψ(n) = log lcm(1,...,n)` is the Chebyshev psi
   function; its asymptotic `ψ(n) ~ n` is the prime number theorem.
   Hanson's bound is a non-asymptotic version: `ψ(n) ≤ n log 3`.
   Mathlib has the asymptotic PNT but no explicit constants.

3. **Bridges Mathlib's primorial and lcm infrastructure.**
   Mathlib has `primorial_le_4_pow` but no `lcm(1,...,n)`-specific
   bound. The bridge `lcm(1,...,n) ≤ n · primorial(n)` (and the
   stronger Hanson identity) would unlock many number-theoretic
   formalization projects.

## Known Results

### What's Already Proven

- **Hanson's bound (Hanson 1972)**: `lcm(1,...,n) ≤ 3ⁿ` for all `n ≥ 1`.
  *Pencil-and-paper*; not yet formalized in Lean / Mathlib.
- **Erdős-style bound**: `lcm(1,...,n) ≤ 4ⁿ` follows from `primorial(n) ≤ 4ⁿ`
  (Mathlib `primorial_le_4_pow`) plus the unproved bridge
  `lcm(1,...,n) ≤ (some function of n) · primorial(n)`.
- **Trivial bounds** (proved in this file, no axioms):
  `lcm(1,...,n) ≤ n!` (each k divides n! and divides lcm).
  `lcm(1,...,n) ≤ nⁿ` (via Mathlib's `Nat.factorial_le_pow`).
- **Numerical verification** (proved in this file via decide):
  `lcm(1,...,n) ≤ 3ⁿ` for n ∈ {1..10, 12, 15, 20}.

### What's Still Open

- **General Hanson bound in Lean**: `axiom hanson_bound` for all n.
- **Mathlib intermediate**: a primorial→lcm bridge, e.g.
  `lcm(1,...,n) ≤ n · primorial(n)`.
- **Mathlib analytical**: the Beta-integral identity
  `∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))` over `ℝ` or over `ℚ`,
  needed for Hanson's specific approach.

### Our Goal

The bootstrap goal of this OQ is:

1. Pin down the formal Lean target (`lcmRange n ≤ 3^n`).
2. Prove the elementary bounds chain (`≤ n!`, `≤ nⁿ`).
3. Provide numerical verification for n ≤ 20.
4. Catalogue Mathlib's existing infrastructure and gaps.
5. State the axiom for refinement in future ACT-phase work.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `basel-problem-oq-01-oq-01-oq-02` | **Parent**. Uses `lcm_hanson_bound` as one of 5 axioms in `apery_theorem` (ζ(3) irrationality). | Apéry's integer-squeeze; recurrence WZ-theory; Chebyshev. |
| `basel-problem` | Grandparent. Sum 1/n² = π²/6. | Fourier; integral representation; ζ(2). |
| `basel-problem-oq-01-oq-01-oq-02-oq-02` | Sister OQ. Proves `denominator_control` axiom from same parent. | Apéry rationals; lcm³·aₙ ∈ ℤ. |

## Initial Thoughts

### Potential Approaches

1. **Hanson 1972 (canonical)**. Use the Beta-integral identity
   `∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))`. Combine with
   `lcm(1,...,n) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ` and a careful
   summing argument over `k ∈ {0,...,n}`.
   Requires: Mathlib Beta-function machinery; `Nat.choose`-divisibility.
   Risk: Beta integrals over rationals may need dedicated infrastructure.

2. **Erdős's combinatorial route**. Use that for each prime `p ≤ n`,
   the largest `p^k ≤ n` divides the central binomial coefficient
   `C(2n, n)`, and `C(2n, n) ≤ 4ⁿ`. This gives `lcm ≤ 4ⁿ`, not
   Hanson's tighter `3ⁿ`. Useful as an intermediate.
   Risk: gives the easier bound; doesn't reach Hanson.

3. **Nair 1982**. Different constant via different identity. Comparable
   complexity to Hanson; may be slightly simpler in Lean.
   Risk: same as Hanson — requires the Beta-integral machinery.

### Key Difficulties

- **Mathlib has no `lcm(1,...,n)`-specific bound**, so any approach
  starts from scratch.
- **Beta-function integrals** are in `Mathlib.Analysis.SpecialFunctions.Beta`
  but not in a form usable for the rational-denominator argument.
- **Discrete arithmetic vs. continuous integral**: the proof requires
  bridging `ℕ`-valued lcm and `ℝ`-valued integrals.

### What Would a Proof Need?

- Key lemma 1: `Beta_integral_eq : ∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))`.
- Key lemma 2: `lcm_clears_beta : (lcmRange (n+1) : ℚ) * Beta(k, n-k) ∈ ℤ`.
- Key lemma 3: numerical-summing argument bounding `Σ_k weights / lcm` over a cleverly chosen subset.

## Tractability Assessment

**Difficulty**: High (a multi-week, multi-file Mathlib upstream
contribution; not single-session work for the full theorem).

**Justification**:
- Mathematical content is classical and well-understood.
- The Lean obstacles are infrastructural (Beta-integrals over ℚ).
- A bottom-up incremental approach (provable bounds → 4ⁿ via primorial bridge → 3ⁿ via Hanson) is tractable in stages.

**Estimated Effort**:
- Bootstrap (this file, OBSERVE/ORIENT): ~1 session (DONE).
- 4ⁿ bound via primorial bridge: ~1-2 weeks.
- Full Hanson 3ⁿ bound: a few months.

## References

### Papers
- Hanson, "On the product of the primes", *Canad. Math. Bull.* 15 (1972) 33-37 — the original 3ⁿ bound.
- Nair, "On Chebyshev-type inequalities for primes", *Amer. Math. Monthly* 89 (1982) 126-129.
- Apéry, "Irrationalité de ζ(2) et ζ(3)", *Astérisque* 61 (1979) — uses Hanson's bound critically.

### Online Resources
- Wikipedia: *Chebyshev function*, *Bertrand's postulate*.
- OEIS: A003418 (`lcm(1, 2, ..., n)`).

### Mathlib
- `Mathlib.NumberTheory.Primorial` — `primorial`, `primorial_le_4_pow`.
- `Mathlib.NumberTheory.Bertrand` — Bertrand's postulate.
- `Mathlib.Data.Nat.Lcm`, `Mathlib.Data.Finset.Lattice` — lcm definitions.
- `Mathlib.Data.Nat.Factorial.Basic` — `factorial_le_pow`, `dvd_factorial`.
- `Mathlib.Analysis.SpecialFunctions.Beta` — Beta-function integral.

## Metadata

```yaml
tags:
  - number-theory
  - lcm
  - hanson
  - chebyshev
  - apery
  - open-question
  - research-bootstrap
related_proofs:
  - basel-problem
  - basel-problem-oq-01-oq-01-oq-02
  - basel-problem-oq-01-oq-01-oq-02-oq-02
difficulty: high
source: gallery-extracted
created: 2026-04-26T08:56:57.649Z
updated: 2026-05-07
```

**Significance**: 7/10
**Tractability**: 3/10 (full proof is a long Mathlib upstream effort)
