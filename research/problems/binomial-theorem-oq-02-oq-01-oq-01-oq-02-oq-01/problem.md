# Problem: A clean Finset equiv for the degree-1 multinomial support piAntidiag s 1 ≃ s

**Slug**: binomial-theorem-oq-02-oq-01-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a finite set `s` (the support of a multinomial), construct and prove a clean equivalence
$$
\mathrm{piAntidiag}\, s\, 1 \;\simeq\; s,
$$
expressed via `Finset.sum_nbij` / `Finset.equiv_of_eq` (or an explicit `Equiv`), where `piAntidiag s 1` is the finset of functions `s → ℕ` with total sum `1` — each such function is the indicator of a single element of `s`.

### Plain Language

In the parent multinomial-entropy formalization, the degree-1 layer of the multinomial support, `piAntidiag s 1`, is the set of nonnegative integer tuples indexed by `s` that sum to `1`. There is exactly one such tuple per element of `s` (put the single unit on that coordinate), so the layer is in natural bijection with `s` itself. This leaf asks to make that bijection explicit and *clean* — using the standard `Finset` bijection combinators rather than an ad-hoc construction — so it can be reused as a rewrite/counting lemma.

### Why This Matters

`piAntidiag s 1 ≃ s` is the base case that makes multinomial/entropy sums telescope: it identifies the "one event happened" layer with the underlying outcome set, giving `|piAntidiag s 1| = |s|` and a clean reindexing for sums over that layer. A tidy `Equiv` (or `sum_nbij` lemma) removes friction wherever the parent's multinomial expansion is specialized to the linear term.

## Known Results

### What's Already Proven

- Parent `binomial-theorem-oq-02-oq-01-oq-01-oq-02`: multinomial entropy formalization (uses `Finset.piAntidiag` layers of the multinomial support).
- Mathlib: `Finset.piAntidiag`, `Finset.sum_nbij`, `Finset.sum_nbij'`, `Finset.equiv_of_eq`, `Equiv`, `Finset.card_nbij`.

### What's Still Open

- A clean, reusable equivalence `piAntidiag s 1 ≃ s` (and the corresponding `card`/`sum` reindexing lemmas) stated with the standard combinators.

### Our Goal

Define the forward map `f ↦ (the unique i with f i = 1)` and inverse `i ↦ Pi.single i 1` (restricted to `s`), prove they are mutually inverse on `piAntidiag s 1`, and package as `Equiv` plus a `Finset.sum_nbij` rewrite; conclude `(piAntidiag s 1).card = s.card`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `binomial-theorem-oq-02-oq-01-oq-01-oq-02` | parent: multinomial entropy, `piAntidiag` layers | `Finset.piAntidiag`, multinomial coefficients |
| `binomial-theorem` | base binomial/multinomial expansion | `Finset.sum`, `Nat.choose` |

## Initial Thoughts

### Potential Approaches

1. **Explicit `Equiv` via `Finset.sum_nbij'`**: give both directions and the two round-trip proofs; the membership conditions characterize a degree-1 tuple as `Pi.single i 1`.
   - Why it might work: `piAntidiag` has good membership lemmas (`Finset.mem_piAntidiag`); the unit-sum condition forces a single nonzero coordinate equal to 1.
   - Risk: handling the dependent function type `s → ℕ` and the "unique support element" extraction cleanly.

2. **Reduce to an existing Mathlib lemma**: check whether `Finset.piAntidiag` already has a `… 1` characterization or a `card` lemma to apply via `equiv_of_eq`.
   - Why it might work: small, standard object; Mathlib may already expose `piAntidiag_one` or similar.
   - Risk: such a lemma may not exist, requiring the explicit construction.

### Key Difficulties

- Extracting "the unique coordinate that equals 1" as a function into `s` with a clean proof of uniqueness.
- Picking `sum_nbij` vs an `Equiv` to best fit downstream use in the parent.

### What Would a Proof Need?

- Key lemma 1: `f ∈ piAntidiag s 1 ↔ ∃ i ∈ s, f = Pi.single i 1` (membership characterization).
- Key lemma 2: the `Equiv`/`sum_nbij` packaging.
- Key lemma 3: `(piAntidiag s 1).card = s.card`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Small, self-contained `Finset`/`Equiv` engineering with strong Mathlib support.
- Parent is verified and 0-axiom; this is pure combinatorial plumbing, no new mathematics.
- Good first-issue-sized formalization.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: 0.5–2 days
- If hard: unlikely; worst case is fiddly dependent-type rewriting

## References

### Papers
- (None required — standard combinatorial identity.)

### Online Resources
- Mathlib docs for `Finset.piAntidiag` and bijection combinators.

### Mathlib
- `Mathlib/Combinatorics/Enumerative/...` / `Mathlib/Algebra/BigOperators/...` — `Finset.piAntidiag`, `Finset.sum_nbij`, `Finset.equiv_of_eq`.
- `Mathlib/Logic/Equiv/Basic.lean` — `Equiv`.

## Metadata

```yaml
tags:
  - combinatorics
  - multinomial
  - finset
  - bijection
  - information-theory
related_proofs:
  - binomial-theorem-oq-02-oq-01-oq-01-oq-02
  - binomial-theorem
difficulty: low
source: gallery-gap
created: 2026-06-24
```
