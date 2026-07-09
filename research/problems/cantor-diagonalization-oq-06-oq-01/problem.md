# Problem: Explicit Diagonal Real Missing From Any Listed Enumeration

**Slug**: cantor-diagonalization-oq-06-oq-01
**Created**: 2026-07-09T16:43:20-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\, f : \mathbb{N} \to \mathbb{R},\ \exists\, x \in [0,1],\ \forall\, n \in \mathbb{N},\ x \neq f(n),
$$

where $x$ is produced by an **explicit construction** — the classical diagonal real whose $n$-th binary (or decimal) digit differs from the $n$-th digit of $f(n)$ — rather than deduced from the cardinal inequality $\aleph_0 < \#\mathbb{R}$.

### Plain Language

The parent gallery entry proves that the reals are uncountable, but it does so abstractly: it invokes Mathlib's cardinal-arithmetic fact $\#\mathbb{R} = \mathfrak{c} > \aleph_0$ and concludes that no list $f : \mathbb{N} \to \mathbb{R}$ can hit every real. This problem asks for the *constructive* version of Cantor's 1891 argument. Given any sequence $f(0), f(1), f(2), \dots$ of reals, we want to write down — as a definable function of $f$ — a specific real number $x$ and then prove directly that $x \neq f(n)$ for every $n$, because $x$ was engineered to disagree with $f(n)$ at digit position $n$. No cardinal arithmetic is used: the witness is exhibited, and the missing-ness is proven digit by digit.

### Why This Matters

The diagonal argument is one of the most reused ideas in mathematics: it powers Cantor's theorem $\#A < \#\mathcal{P}(A)$, Turing's proof that the halting problem is undecidable, Gödel's incompleteness theorems, and Russell's paradox. A self-contained, digit-level formalization makes the *mechanism* explicit rather than hiding it inside a cardinality lemma, so it can serve as a reusable template for those downstream diagonalizations. It also gives a constructive witness (an actual real, not merely an existence claim), which is stronger than the non-constructive cardinal statement and is closer to how the argument is taught.

## Known Results

### What's Already Proven

- `Cardinal.not_countable_real` — ¬ (Set.univ : Set ℝ).Countable, the abstract uncountability of ℝ — Mathlib.Analysis.Real.Cardinality
- `not_surjective_nat_real` — no surjection ℕ → ℝ, the enumeration form — parent gallery proof `cantor-diagonalization-oq-06`

### What's Still Open

- An explicit, definable map `diagonalReal : (ℕ → ℝ) → ℝ` producing a witness with `diagonalReal f ≠ f n` for all `n`, proven by direct digit comparison rather than via cardinality.
- A clean digit-extraction / digit-comparison lemma in Mathlib usable for the disagreement step (nth binary or decimal digit of a real in [0,1]).

### Our Goal

Formalize the diagonal construction concretely: define the witness `x` as an explicit function of the enumeration `f` (e.g. via a bit sequence `b n = if nthDigit (f n) n = 0 then 1 else 0`), embed it into [0,1] ⊆ ℝ, and prove `x ≠ f n` for every `n` by exhibiting the digit at which they differ — with **no** appeal to `Cardinal.not_countable_real` or `#ℝ = 𝔠`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cantor-diagonalization-oq-06 | Parent entry: proves ℝ uncountable via cardinality; this problem replaces that route with an explicit diagonal witness | Cardinal arithmetic, `Cardinal.not_countable_real`, `Set.countable_univ_iff` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Binary digit diagonalization into [0,1]**: Define a bit sequence `b : ℕ → Fin 2` by flipping the `n`-th binary digit of `f n`, then set `x = ∑ₙ b n / 2^(n+1)` (a convergent series in [0,1]). Prove `x ≠ f n` by showing their `n`-th binary digits differ.
   - Why it might work: mirrors Cantor's original construction exactly; the series converges by comparison with a geometric series, and Mathlib has `tsum`/`Summable` machinery for geometric series.
   - Risk: binary expansions are non-unique (dyadic rationals have two expansions), so "the n-th digit" must be pinned down carefully to avoid the `0.0111… = 0.1000…` ambiguity; the digit-disagreement must survive this.

2. **Approach B — Decimal diagonalization avoiding 0 and 9**: Build `x` digit by digit in base 10, choosing each digit `d n ∈ {1, …, 8}` to differ from the `n`-th decimal digit of `f n`, deliberately avoiding 0 and 9 so the expansion is unique and no two constructed reals collide.
   - Why it might work: restricting to digits in {1,…,8} sidesteps the non-uniqueness of decimal expansions entirely, making the "differs at digit n ⟹ different real" step clean.
   - Risk: formalizing a base-10 digit-extraction function for an arbitrary real and proving its basic properties is more setup than the binary route; Mathlib support for decimal digits of reals is thinner than for binary.

### Key Difficulties

- Non-uniqueness of positional expansions: the same real can have two digit sequences, so "differs at digit n" does not immediately imply "different real" without a normalization or a digit-range restriction.
- Extracting the `n`-th digit of an arbitrary real as a total, computable/definable function and relating it back to the real's value (need lemmas of the form `nthDigit x n = d → …`).
- Convergence and membership in [0,1]: proving the constructed series is `Summable` and lands in the unit interval.

### What Would a Proof Need?

- Key lemma 1: a digit-extraction function `nthDigit : ℝ → ℕ → Fin k` (k = 2 or 10) with the property that if two reals in [0,1] have a specific digit differing under a uniqueness-guaranteeing normalization, they are unequal.
- Key lemma 2: `Summable (fun n => (b n : ℝ) / k^(n+1))` and that the resulting sum lies in [0,1], via geometric-series comparison (`summable_geometric_of_lt_one` / `tsum` bounds).
- Technical requirements: a normalization convention (avoid trailing all-9s / all-1s, or restrict digit alphabet) so the diagonal disagreement is preserved as an inequality of reals.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is elementary and classical (Cantor 1891); the challenge is entirely in the Lean formalization of digit extraction and expansion non-uniqueness.
- Mathlib already provides geometric-series summability, `tsum`, and the interval [0,1], plus real-analysis tools, so the analytic side is well-supported.
- Similar digit/expansion constructions exist (e.g. `Nat.digits`, `Real.exists…` expansions), but a reusable real-digit API is not fully turnkey, which raises the effort above Low.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks
- If hard: unknown (depends on how much digit-extraction API must be built from scratch)

## References

### Papers
- Cantor, Georg, "Über eine elementare Frage der Mannigfaltigkeitslehre", 1891 — introduces the diagonal argument in its now-standard digit-flipping form.
- Cantor, Georg, "Über eine Eigenschaft des Inbegriffes aller reellen algebraischen Zahlen", 1874 — the first proof that the reals are uncountable.

### Online Resources
- https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument — statement and standard digit-flip construction.

### Mathlib
- Mathlib.Analysis.Real.Cardinality — the parent's `Cardinal.not_countable_real` and the {0,1}^ℕ ↪ ℝ binary-expansion machinery this construction parallels.
- Mathlib.Analysis.SpecificLimits.Basic — geometric-series summability (`summable_geometric_of_lt_one`) for convergence of the digit series.
- Mathlib.Topology.Algebra.InfiniteSum.Basic — `tsum` / `Summable` API for defining and bounding the constructed real.
- Mathlib.Data.Nat.Digits — positional-digit lemmas as a model for a real-digit extraction API.

## Metadata

```yaml
tags:
  - set-theory
  - cardinality
  - cantor
  - uncountability
  - real-numbers
  - extension
  - research
related_proofs:
  - cantor-diagonalization-oq-06
difficulty: medium
source: open-question
created: 2026-07-09T16:43:20-07:00
```
