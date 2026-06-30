# Problem: Two-Sided Abel-Summation Trap for Bounded-Variation Coefficients

**Slug**: alternating-series-test-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent (Abel-summation error bounds for alternating series with bounded-variation
coefficients) gives a one-sided remainder estimate carrying a boundary term `|a(M−1)|`.
The goal is to absorb that boundary term into a clean **two-sided** trap:

$$
L - \varepsilon_M \;\le\; \sum_{n=0}^{M-1} (-1)^n a_n \;\le\; L + \varepsilon_M,
$$
where `L = ∑_{n=0}^∞ (-1)^n a_n` and the envelope `ε_M` is expressed purely in terms of the
total variation tail of `(a_n)` (no leftover isolated `|a(M−1)|` boundary term), mirroring the
antitone two-term trap of the sibling entry.

### Plain Language

For an alternating series whose coefficients have bounded variation, the parent bounded how
far a partial sum is from the limit, but the bound included an extra boundary term
`|a(M−1)|`. We want to fold that term into the main estimate so the partial sum is trapped
*between* a lower and an upper bound expressed only via the variation tail — a symmetric,
self-contained error envelope.

### Why This Matters

Two-sided traps are what make error bounds usable: they pin the limit `L` inside a shrinking
interval around each partial sum, giving both existence of the limit and an effective
convergence rate. Matching the antitone sibling's clean two-term form unifies the gallery's
treatment of alternating-series remainders.

## Known Results

### What's Already Proven

- `alternating-series-test-oq-01-oq-02` — Abel-summation error bounds (one-sided, with `|a(M−1)|` boundary term) for bounded-variation coefficients (verified, 0-axiom).
- Sibling antitone entry — a clean two-term trap for antitone coefficients (the model to match).
- Mathlib: `Finset.sum_range_succ`, Abel summation (`Finset.sum_Ioo_eq_sub` style telescoping), `tsum`/`HasSum` API, total-variation sums.

### What's Still Open

- A two-sided bound (both upper and lower) for the bounded-variation case with the boundary term absorbed.
- The explicit form of the envelope `ε_M` in terms of the variation tail.

### Our Goal

Prove the two-sided trap for bounded-variation coefficients, removing the standalone
`|a(M−1)|` boundary term by combining the one-sided bound with its complementary direction,
and express the envelope via the variation tail.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| alternating-series-test-oq-01-oq-02 | Parent: one-sided Abel bound | Abel summation, bounded variation |
| alternating-series-test-oq-01-oq-01 | Sibling: antitone two-term trap | telescoping, monotone tails |

## Initial Thoughts

### Potential Approaches

1. **Approach A — pair the two one-sided bounds**: Apply the parent bound to both the partial
   sum and the shifted partial sum (or to `+` and `−` directions), then combine so the
   boundary term cancels into the variation tail.
   - Why it might work: reuses the parent lemma as a black box; only algebra to combine.
   - Risk: bookkeeping on indices `M`, `M−1`; sign of the alternation.

2. **Approach B — re-derive via Abel summation directly**: Redo the Abel/summation-by-parts
   step keeping both bracketing partial sums, so the trap appears symmetric from the start.
   - Why it might work: cleaner final envelope.
   - Risk: duplicates parent work; more to verify.

### Key Difficulties

- Identifying the right complementary inequality so the `|a(M−1)|` term merges into `ε_M`.
- Expressing the envelope in a way that visibly matches the antitone sibling's two-term form.

### What Would a Proof Need?

- Key lemma 1: the parent's one-sided Abel bound, instantiated at the relevant indices.
- Key lemma 2: total-variation tail control `∑_{n≥M} |a_{n+1} − a_n|` bounding the boundary term.
- Technical requirements: `Finset` telescoping, `abs_le`, `tsum_le_tsum`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard analytic content (Abel summation, bounded-variation bound) is already in the parent.
- This is largely a combination/refinement of existing one-sided estimates.
- The antitone sibling provides a concrete target form to aim for.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days
- If hard: up to a week if the envelope needs careful reformulation

## References

### Mathlib
- `Mathlib.Analysis.SumOverResidueClass` / `Mathlib.Algebra.BigOperators` — summation-by-parts and `Finset` sums.
- `Mathlib.Topology.Algebra.InfiniteSum` — `HasSum`, `tsum`, tail estimates.

## Metadata

```yaml
tags:
  - analysis
  - series
  - bounded-variation
related_proofs:
  - alternating-series-test-oq-01-oq-02
  - alternating-series-test-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
