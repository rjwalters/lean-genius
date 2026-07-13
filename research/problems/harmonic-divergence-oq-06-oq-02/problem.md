# Problem: Divergence of Σ 1/(a·n+b) for b ≥ 0 (including the b = 0 scaled-harmonic case)

**Slug**: harmonic-divergence-oq-06-oq-02
**Created**: 2026-06-30T22:49:26-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For real $a > 0$ and $b \ge 0$, the reciprocal series along the arithmetic
progression $a\,n + b$ diverges:

$$
\forall\, a > 0,\ \forall\, b \ge 0,\qquad
\sum_{n \ge 1} \frac{1}{a\,n + b} = +\infty
\quad\Longleftrightarrow\quad
\neg\,\text{Summable}\ \Bigl(n \mapsto \tfrac{1}{a\,n + b}\Bigr).
$$

The new content over the parent (which requires $b > 0$) is the endpoint
$b = 0$, where the series is exactly the harmonic series rescaled by $1/a$:

$$
\sum_{n \ge 1} \frac{1}{a\,n} \;=\; \frac{1}{a}\sum_{n \ge 1} \frac{1}{n}
\;=\; +\infty .
$$

Because $\tfrac{1}{a\cdot 0}=\tfrac{1}{0}$ is undefined, the $b=0$ series must be
indexed from $n = 1$: the $n = 0$ term is excised. Equivalently, in Lean one
either sums over `fun n : ℕ => 1/(a*(n+1))` or invokes the index-shift lemma so
that only strictly positive multiples $a, 2a, 3a, \dots$ appear.

### Plain Language

The parent proof shows that the reciprocals of any arithmetic progression
$b, a+b, 2a+b, \dots$ add up to infinity, **provided the progression starts at a
strictly positive value** ($b > 0$). This open question closes the last gap:
allow $b = 0$ as well.

When $b = 0$ the progression is just $0, a, 2a, 3a, \dots$. The very first term
$1/0$ makes no sense, so we throw it away and sum the reciprocals of the
positive multiples of $a$: $\tfrac1a + \tfrac1{2a} + \tfrac1{3a} + \cdots$.
Factoring out $1/a$ turns this into $\tfrac1a\,(1 + \tfrac12 + \tfrac13 + \cdots)$
— exactly $1/a$ times the harmonic series. Since the harmonic series diverges,
so does its constant multiple, and the whole family $\Sigma\,1/(a n + b)$ for
$a > 0$, $b \ge 0$ is handled uniformly.

### Why This Matters

- **Completes the arithmetic-progression divergence family.** The parent settles
  $b > 0$; this settles $b = 0$. Together they give one clean statement covering
  every $a > 0$, $b \ge 0$ — including the pure "multiples of $a$" case that is
  the most natural starting point and the one closest to the raw harmonic series.
- **Uniform treatment of $\Sigma\,1/(a n + b)$.** Rather than special-casing the
  endpoint, the whole progression family becomes a single theorem, ready to be
  reused by any downstream result that needs "linear-density reciprocal series
  diverge."
- **Illustrates the scaling principle.** The $b = 0$ case is a textbook example
  that summability is invariant under multiplication by a nonzero constant, and
  that a divergent series stays divergent when rescaled. This is precisely the
  content of Mathlib's `summable_mul_left_iff`.

## Known Results

### What's Already Proven

- **Parent, `not_summable_one_div_arith`** (gallery `harmonic-divergence-oq-06`,
  VERIFIED, 0-axiom): for $a > 0$, $b > 0$,
  $\neg\,\text{Summable}\,(n \mapsto 1/(a n + b))$, by comparison with the
  harmonic series via $a n + b \le (a+b)(n+1)$. — `Proofs/HarmonicDivergenceOQ06.lean`
- **Corollaries in the parent**: `not_summable_one_div_odd` ($a=2,b=1$),
  `not_summable_one_div_even` ($a=2,b=2$), and
  `tendsto_sum_one_div_odd_atTop` (odd partial sums $\to +\infty$).
- **Harmonic divergence**, `Real.not_summable_one_div_natCast`:
  $\neg\,\text{Summable}\,(n \mapsto 1/(n:\mathbb{R}))$ — Mathlib
  `Mathlib.Analysis.PSeries`. This is the engine everything reduces to.

### What's Still Open

- The $b = 0$ endpoint: $\neg\,\text{Summable}\,(n \mapsto 1/(a n))$ for $a > 0$,
  handled by excising $n = 0$ (index from $1$) and factoring out $1/a$. **(This
  problem.)**
- Sibling OQ (oq-01): the explicit odd-harmonic asymptotic
  $\Sigma_{i<n}\,1/(2i+1) = \tfrac12(\ln n + \gamma + \ln 4) + o(1)$.
- Sibling OQ (oq-03): Cesàro / Abel summability and the contrast with the
  conditionally convergent alternating series $\Sigma\,(-1)^n/(2n+1) = \pi/4$.

### Our Goal

Prove the $b \ge 0$ statement, i.e. extend the parent to admit $b = 0$. The core
new lemma is the scaled-harmonic divergence

$$
\neg\,\text{Summable}\ \Bigl(n \mapsto \tfrac{1}{a\,(n+1)}\Bigr)\quad (a > 0),
$$

then package a single theorem `not_summable_one_div_arith'` with hypothesis
`0 ≤ b` that dispatches to the parent when $b > 0$ and to the scaled-harmonic
lemma when $b = 0$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| harmonic-divergence-oq-06 | Direct parent; supplies the $b>0$ case and the comparison machinery | comparison test, index shift, `nlinarith` |
| harmonic-divergence | Divergence of $\Sigma\,1/n$, the ultimate engine | Oresme dyadic blocking / `PSeries` |
| p-series | $\Sigma\,1/n^p$ converges iff $p>1$; here is the borderline $p=1$ linear case | `Real.summable_one_div_nat_rpow` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — scaling reduction (recommended).**
   For $b = 0$, write $1/(a(n+1)) = (1/a)\cdot 1/(n+1)$ and use
   `summable_mul_left_iff` (needs $a \ne 0$, available from $a > 0$):
   `Summable (fun n => 1/(a*(n+1)))` $\leftrightarrow$
   `Summable (fun n => 1/(n+1))`. The right side fails by
   `Real.not_summable_one_div_natCast` transported through `summable_nat_add_iff`.
   - Why it might work: it is essentially the parent's endgame minus the
     comparison inequality — the scaling makes the reduction *exact* rather than
     by domination.
   - Risk: aligning the `1/(a*(n+1))` shape with the `(1/a) * (1/(n+1))` shape
     needs a `field_simp` / `mul_one_div` massage; and choosing whether to index
     from `n+1` or apply `summable_nat_add_iff` on `fun n => 1/(a*n)`.

2. **Approach B — comparison, reusing the parent verbatim.**
   Keep the parent inequality but at $b = 0$: $a n \le a(n+1)$ trivially, and
   $1/(n+1) \le a \cdot 1/(a n)$ for $n \ge 1$. This mirrors the parent's
   `Summable.of_nonneg_of_le` structure and dominates the shifted harmonic
   series directly, avoiding the iff lemma.
   - Why it might work: maximal code reuse; the parent proof already establishes
     every supporting lemma.
   - Risk: the comparison bound must start at $n = 1$ (the excised term), so the
     shift bookkeeping is slightly fussier than Approach A's clean iff.

### Key Difficulties

- **Excising $n = 0$.** The only genuine subtlety: at $b = 0$, $1/(a\cdot 0)$ is
  the junk value $1/0 = 0$ in Lean's `ℝ`, which would silently *shrink* the tail
  and could mask divergence if handled naively. Index from $n = 1$ (or use
  `summable_nat_add_iff` with shift $1$) so only positive denominators occur.
- **Shape matching.** Getting `1/(a*(n+1))` into the exact form consumed by
  `summable_mul_left_iff` / `Summable.mul_left`.
- **Unifying $b = 0$ and $b > 0$** into one hypothesis `0 ≤ b` via
  `rcases eq_or_lt_of_le hb` (or `lt_or_eq`) without duplicating the whole proof.

### What Would a Proof Need?

- Key lemma 1: `not_summable_one_div_scaled_harmonic (a : ℝ) (ha : 0 < a) :
  ¬ Summable (fun n : ℕ => 1/(a*(n+1)))` — via `summable_mul_left_iff` (or
  `Summable.mul_left` on the contrapositive) reducing to
  `Real.not_summable_one_div_natCast`.
- Key lemma 2 (packaging): `not_summable_one_div_arith' (a b : ℝ)
  (ha : 0 < a) (hb : 0 ≤ b) : ¬ Summable (fun n : ℕ => 1/(a*n+b))` splitting on
  `b = 0` vs `b > 0`.
- Technical requirements: `summable_mul_left_iff`, `Summable.mul_left`,
  `summable_nat_add_iff`, `Real.not_summable_one_div_natCast`, `mul_one_div`,
  `field_simp`, and `ne_of_gt` for `a ≠ 0`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The $b = 0$ case is a near-mechanical reduction to the already-formalized
  harmonic divergence via a single scaling step; no new mathematical idea beyond
  "constant multiple of a divergent series diverges."
- The parent proof already ships every supporting lemma (comparison, index
  shift, harmonic non-summability), so most of the work is plumbing.
- The one care point — excising $n = 0$ and matching the `mul_left` shape — is a
  standard Mathlib manipulation with well-known lemmas.

**Estimated Effort**:
- Exploration: a few hours (confirm `summable_mul_left_iff` signature and the
  cleanest index-shift path).
- If tractable: 1–2 days for the scaled lemma plus the unified `0 ≤ b` wrapper
  and a couple of corollaries (e.g. $\Sigma\,1/(3n)$).
- If hard: unlikely; worst case is fiddly rewriting, not a genuine obstruction.

## References

### Papers
- Nicole Oresme, *Quaestiones super Geometriam Euclidis*, c. 1350 — first proof
  that the harmonic series diverges (dyadic blocking); the scaled series here is
  an immediate corollary.
- Leonhard Euler, *Variae observationes circa series infinitas*, 1737 — study of
  reciprocal series, including $\Sigma\,1/p$ over primes.

### Online Resources
- Divergence of arithmetic-progression reciprocal series — the general fact that
  $\Sigma\,1/n_k$ diverges when $n_k$ grows at most linearly.

### Mathlib
- `Mathlib.Analysis.PSeries` — `Real.not_summable_one_div_natCast` /
  `Real.not_summable_nat_cast_inv`: divergence of the harmonic series.
- `Mathlib.Topology.Algebra.InfiniteSum.*` — `Summable.mul_left`,
  `summable_mul_left_iff` (scaling a series by a nonzero constant preserves
  summability), `summable_nat_add_iff` (index-shift), and the comparison test
  `Summable.of_nonneg_of_le` / `summable_of_nonneg`.
- `Finset.sum` and `not_summable_iff_tendsto_nat_atTop_of_nonneg` — for phrasing
  the divergence as partial sums $\to +\infty$.

## Metadata

```yaml
tags:
  - analysis
  - series
  - harmonic-series
  - summability
  - arithmetic-progression
  - comparison-test
related_proofs:
  - harmonic-divergence-oq-06
  - harmonic-divergence
  - p-series
difficulty: medium
source: gallery-gap
created: 2026-06-30T22:49:26-07:00
```
