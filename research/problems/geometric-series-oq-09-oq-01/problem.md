# Problem: q-Fold Splitting of the Geometric Series

**Slug**: geometric-series-oq-09-oq-01
**Created**: 2026-06-23
**Status**: Active
**Source**: gallery-gap <!-- open question of verified parent geometric-series-oq-09 -->

## Problem Statement

### Formal Statement

For a real (or complex) ratio $r$ with $|r| < 1$, a modulus $q \ge 1$, and a residue $a$ with $0 \le a < q$:

$$
\sum_{n=0}^{\infty} r^{\,q n + a} \;=\; \frac{r^{a}}{1 - r^{q}} .
$$

Equivalently, the full geometric series $\sum_{m\ge 0} r^m$ splits into $q$ residue subseries (indexed by $a = 0,1,\dots,q-1$), each itself geometric with ratio $r^q$ and leading term $r^a$, and the $q$ closed forms sum back to $\frac{1}{1-r}$ via $\sum_{a=0}^{q-1} r^a = \frac{1-r^q}{1-r}$.

### Plain Language

The geometric series $1 + r + r^2 + \cdots = \frac{1}{1-r}$ is one of the most familiar sums in mathematics. This problem asks what happens when you keep only every $q$-th term, starting from position $a$: $r^a + r^{a+q} + r^{a+2q} + \cdots$. Because the gaps are uniform, this thinned-out series is *again* geometric — with ratio $r^q$ — so it has the clean closed form $\frac{r^a}{1-r^q}$. Formalizing this makes precise the intuitive "split a series by residue class mod $q$" operation and confirms the pieces reassemble into the whole.

### Why This Matters

Residue-class (or "$q$-fold") splitting of geometric series is the engine behind generating-function manipulations: extracting even/odd parts ($q=2$), bisection/multisection of power series, roots-of-unity filters, and the term-by-term handling of Lambert and theta-type series. It is also the discrete shadow of partial-fraction decomposition over cyclotomic factors. A clean, reusable Lean lemma — "a geometric series re-indexed by $qn+a$ is geometric with ratio $r^q$" — supports many downstream analysis and number-theory entries (e.g. multisection identities, the $\sum n^k r^n$ family in sibling OQs).

## Known Results

### What's Already Proven

- $\sum_{n} r^n = \frac{1}{1-r}$ for $|r|<1$ — Mathlib `tsum_geometric_of_lt_one` / `hasSum_geometric_of_lt_one` (real) and `tsum_geometric_of_norm_lt_one` (normed field).
- Summability of geometric series under the norm bound — `summable_geometric_of_norm_lt_one`.
- Reindexing / composition of `HasSum` along injective maps — `Function.Injective.hasSum_iff`, `HasSum.comp_injective`.
- Finite geometric partial sums and $\sum_{a<q} r^a = \frac{1-r^q}{1-r}$ — `geom_sum_eq` / `Finset.geom_sum_eq`.

### What's Still Open (here)

- The thinned-subseries closed form $\sum_n r^{qn+a} = \frac{r^a}{1-r^q}$ as a `HasSum`/`tsum` statement (real and/or normed field).
- The reassembly statement: the $q$ residue subseries sum to the full series (a `HasSum`-level partition over `Fin q`).

### Our Goal

Ship $\sum_n r^{qn+a} = \frac{r^a}{1-r^q}$ as a verified `tsum` (or `HasSum`) theorem for $\|r\|<1$, obtained by recognizing the subseries as geometric with ratio $r^q$ (note $\|r^q\| = \|r\|^q < 1$) and factoring the constant $r^a$. As a corollary, prove the $q$-fold reassembly $\sum_{a<q} \sum_n r^{qn+a} = \frac{1}{1-r}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| geometric-series-oq-09 | direct parent | `tsum`, geometric closed form |
| geometric-series | base closed-form/summability API | `hasSum_geometric_of_norm_lt_one` |
| geometric-series-oq-07 / -oq-10 | sibling weighted/multisection variants | reindexing, `HasSum.mul_left` |

## Initial Thoughts

### Potential Approaches

1. **Recognize-and-rescale** (primary): Write $r^{qn+a} = r^a \cdot (r^q)^n$. Apply `hasSum_geometric_of_norm_lt_one` to ratio $s := r^q$ (with $\|s\| = \|r\|^q < 1$ from `norm_pow` and `pow_lt_one`), then `HasSum.mul_left r^a` to pull out the constant. The closed form is $r^a \cdot \frac{1}{1-r^q}$.
   - Why it might work: every step is a named Mathlib lemma; no genuine analysis is re-proved.
   - Risk: the bound $\|r\|^q < 1$ needs $q \ge 1$ (handle $q=0$ as degenerate or exclude); minor `pow`/`norm` plumbing.

2. **Reindex the full series along `n ↦ qn+a`** (alternative): use injectivity of $n\mapsto qn+a$ and a `HasSum.comp_injective`-style argument to extract the subseries from the full geometric `HasSum`.
   - Why it might work: directly yields the reassembly/partition statement.
   - Risk: assembling the disjoint-union-over-`Fin q` partition of $\mathbb{N}$ is fiddlier than approach 1.

### Key Difficulties

- Establishing $\|r^q\| < 1$ from $\|r\| < 1$ cleanly (`norm_pow`, `pow_lt_one_iff`/`pow_lt_one`).
- Choosing real vs. normed-field generality; the normed-field version is more reusable.
- Edge cases $q=0$ / $r=0$.

### What Would a Proof Need?

- Key lemma 1: `hasSum_geometric_of_norm_lt_one` applied to $r^q$.
- Key lemma 2: `HasSum.mul_left` to factor $r^a$.
- Technical requirements: `norm_pow`, `pow_lt_one`, `tsum_mul_left`, possibly `Finset.geom_sum_eq` for the reassembly corollary.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The core is a recognize-and-rescale of an existing Mathlib closed form; no new analysis.
- The only real work is the $\|r^q\|<1$ bound and constant-factoring, both standard.
- Sibling geometric-series OQs already ship `HasSum`-level manipulations of this kind.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: half a day to a day

## References

### Papers
- Wilf, *generatingfunctionology* — multisection of power series via residue classes.

### Online Resources
- Standard treatments of series bisection / roots-of-unity filter.

### Mathlib
- `Mathlib.Analysis.SpecificLimits.Basic` — `hasSum_geometric_of_norm_lt_one`, `tsum_geometric_of_norm_lt_one`.
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `HasSum.mul_left`, `tsum_mul_left`.
- `Mathlib.Algebra.GeomSum` — `geom_sum_eq` for the finite reassembly factor.

## Metadata

```yaml
tags:
  - analysis
  - geometric-series
  - infinite-series
  - power-series
  - summability
related_proofs:
  - geometric-series-oq-09
  - geometric-series
difficulty: low
source: gallery-gap
created: 2026-06-23
```
