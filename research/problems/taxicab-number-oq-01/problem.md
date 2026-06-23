# Problem: Hardy–Ramanujan Taxicab Number 1729

**Slug**: taxicab-number-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\mathrm{Ta}(2) = 1729 = 1^3 + 12^3 = 9^3 + 10^3,
$$
and $1729$ is the least positive integer with two essentially distinct representations as a sum of two positive cubes.

### Plain Language

The "taxicab number" 1729 is famous from the Hardy–Ramanujan anecdote: it is the
smallest positive integer expressible as a sum of two positive cubes in two
different ways. We want a machine-checked proof that (a) 1729 has the two
representations above and (b) no positive integer below 1729 has two distinct
such representations.

### Why This Matters

A clean, self-contained finite-search formalization that anchors the broader
study of taxicab numbers $\mathrm{Ta}(n)$ and sums of two cubes. Good
decidability showcase: the whole statement reduces to a bounded search.

## Known Results

### What's Already Proven

- Existence of the two representations is a direct arithmetic check.
- Taxicab numbers $\mathrm{Ta}(n)$ exist for all $n$ (Hardy–Wright), but explicit
  values grow rapidly and are not needed here.

### What's Still Open (for this entry — engineering, not mathematics)

- A Lean formalization of "two distinct representations as a sum of two positive
  cubes" and the minimality search are not present in Mathlib or the gallery.

### Our Goal

Prove `Ta(2) = 1729` in Lean: define the multiset of unordered pairs
$\{(a,b) : a^3 + b^3 = n,\ 1 \le a \le b\}$, show 1729 has cardinality $\ge 2$,
and show every $0 < n < 1729$ has cardinality $\le 1$ — the latter by
`Decidable`/`decide`-style finite enumeration over $a,b \le 12$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramanujan-sum-fallacy | shares the Ramanujan name only; mathematically unrelated | analytic divergence |
| perfect-numbers | finite arithmetic characterization | decidability, divisor sums |

## Initial Thoughts

### Potential Approaches

1. **Direct decidable search**: encode representation count as a `Finset.filter`
   over `Finset.range 13 ×ˢ Finset.range 13`; prove the two facts by `decide` or
   `Finset` computation.
   - Why it might work: the bound $a,b \le 12$ for $n \le 1729$ is tiny.
   - Risk: `decide` on cubes may be slow; may need `Nat`-level `rfl` lemmas.

2. **Native `decide` / `Decidable` instance** on the full minimality statement.
   - Risk: kernel reduction cost; might prefer interval_cases.

### Key Difficulties

- Defining "distinct representations" so that $(a,b)$ and $(b,a)$ are identified.
- Keeping the minimality search within kernel-reduction budget.

### What Would a Proof Need?

- `cubeReps n := (range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 ≤ p.2 ∧ p.1^3 + p.2^3 = n)`
- `1729 ∈` two-rep set; `∀ n < 1729, (cubeReps n).card ≤ 1`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Entirely finite and decidable; bounds are small.
- Similar finite-search proofs (perfect numbers) already exist in the gallery.
- Mathlib `Finset`, `decide`, `interval_cases` suffice.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Online Resources
- OEIS A011541 (taxicab numbers) — context.
- Hardy & Wright, *An Introduction to the Theory of Numbers* — taxicab numbers.

### Mathlib
- `Mathlib.Data.Finset.Basic`, `Finset.filter`, `decide` — finite enumeration.

## Metadata

```yaml
tags:
  - number-theory
  - cubes
  - taxicab
  - ramanujan
  - sums-of-powers
  - decidable
related_proofs:
  - ramanujan-sum-fallacy
  - perfect-numbers
difficulty: low
source: gallery-gap
created: 2026-06-16
```
