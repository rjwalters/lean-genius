# Problem: Linear lower bound N = Omega(n) for collinear integer distance sets

**Slug**: erdos-100-oq-01-oq-03
**Created**: 2026-07-09T16:03:13-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $x_1 < x_2 < \dots < x_n$ be $n$ distinct points on a line whose pairwise
distances $|x_i - x_j|$ are all integers. The diameter is
$D = x_n - x_1 = \max_{i,j} |x_i - x_j|$. We claim the linear lower bound

$$
D \;=\; x_n - x_1 \;=\; \sum_{i=1}^{n-1} (x_{i+1} - x_i) \;\ge\; \binom{n}{2}^{1/2}\text{-type growth is not needed:} \quad D \ge \sum_{k=1}^{n-1} k \;\ge\; n - 1 = \Omega(n).
$$

More precisely, order the points so that $d_i := x_{i+1} - x_i > 0$ are the
consecutive gaps. Each $d_i$ is a positive integer, so $d_i \ge 1$ and hence

$$
D = \sum_{i=1}^{n-1} d_i \;\ge\; \sum_{i=1}^{n-1} 1 = n - 1 \;=\; \Omega(n).
$$

The target theorem to formalize is: **for every collinear $n$-point set with
all pairwise distances integers, the diameter satisfies $D \ge n - 1$**, giving
the linear bound $N = \Omega(n)$ in the collinear case.

### Plain Language

Erdős Problem #100 asks whether $n$ points in the plane with all pairwise
distances integers must have diameter growing at least linearly in $n$. In full
generality this is open (only the Guth–Katz bound $\Omega(n/\log n)$ is known).
This sub-problem restricts to the *easy but instructive* collinear case: all
points lie on a single line. Then the consecutive gaps between neighboring
points are positive integers (each at least 1), and the diameter is their sum,
so it is at least $n-1$. The goal is to formalize this clean linear lower bound
in Lean, isolating the arithmetic structure that the general planar problem
lacks.

### Why This Matters

- It establishes the conjectured linear bound $\Omega(n)$ in the one regime where
  it is provable, sharpening intuition for why the *non*-collinear case is hard
  (there the gaps are no longer forced to be integers along a single axis).
- The collinear case is exactly the configuration the Anning–Erdős theorem
  *excludes* from its finiteness conclusion — infinite collinear integer
  distance sets exist ($\mathbb{Z}$ itself). Formalizing the diameter bound here
  clarifies the boundary between the collinear (linear-diameter, infinite
  families allowed) and non-collinear (finite, gap open) worlds.
- It supplies a self-contained, fully verifiable lemma that can be cited by the
  parent OQ-01 gap analysis without any `sorry`.

## Known Results

### What's Already Proven

- Guth–Katz distinct distances theorem (2015, *Annals of Mathematics* 181:155–190)
  — gives $\ge cn/\log n$ distinct distances for any planar $n$-point set, hence
  $\text{diam} \ge cn/\log n$ for integer distance sets (the best *general* bound).
- Anning–Erdős theorem (1945) — no infinite *non-collinear* integer distance set
  exists; collinear ones (e.g. $\{0,1,\dots,n-1\} \subset \mathbb{Z}$) are the
  exception and are unbounded.
- Elementary: on a line, integer pairwise distances force integer consecutive
  gaps, so the diameter is a sum of $n-1$ positive integers $\ge n-1$.

### What's Still Open

- The full planar conjecture $\text{diam} = \Omega(n)$ for non-collinear integer
  distance sets (Erdős #100) — closing the $\log n$ gap.
- Whether the collinear bound $n-1$ is tight in stronger senses (e.g. sum of
  *distinct* gaps giving $\binom{n}{2}$-type diameter when distances must be
  distinct), a natural strengthening.

### Our Goal

Formalize in Lean the statement and proof that any collinear $n$-point set with
all pairwise distances integers has diameter $\ge n - 1$, i.e. $\Omega(n)$. This
is a fully verifiable ($0$-sorry) target that grounds the linear bound in the
collinear special case of Erdős #100.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-100-oq-01 | Parent OQ: analyzes the $\log n$ gap between known $\Omega(n/\log n)$ and conjectured $\Omega(n)$ diameter bounds; this sub-problem proves the $\Omega(n)$ bound in the collinear case | Filter.atTop asymptotics, Real.log divergence, conjecture formalization |
| erdos-100-oq-02 | Sibling OQ on Erdős #100 exploring complementary aspects of the diameter question | discrete geometry, integer distance sets |

## Initial Thoughts

### Potential Approaches

1. **Approach A — sort and sum consecutive gaps**: Represent the point set as a
   finite set $S \subset \mathbb{Z}$ (WLOG after translation/embedding, since
   collinear integer-distance points can be placed at integer coordinates).
   Sort as $x_1 < \dots < x_n$, define gaps $d_i = x_{i+1}-x_i \ge 1$, and prove
   $x_n - x_1 = \sum d_i \ge n-1$ by a telescoping sum plus `Finset.sum` lower
   bound.
   - Why it might work: Mathlib has strong `Finset.sum` and telescoping support
     (`Finset.sum_range_succ_comm`, `Finset.sum_le_sum`); the arithmetic is
     elementary.
   - Risk: Justifying the reduction "collinear integer-distance ⇒ integer
     coordinates" rigorously (up to a common rational scaling) may need care;
     one may instead take the integer-coordinate model as the definition.

2. **Approach B — direct diameter bound via cardinality**: Show that an integer
   interval $[x_1, x_n]$ containing $n$ points has length $\ge n-1$ because it
   contains at least $n$ distinct integers, so $x_n - x_1 \ge n-1$.
   - Why it might work: reduces to `Finset.card_le_of_subset` on
     $\{x_1,\dots,x_n\} \subseteq \mathbb{Z} \cap [x_1,x_n]$ and the size of an
     integer interval.
   - Risk: requires the same integer-coordinate reduction as Approach A.

### Key Difficulties

- Formalizing "collinear with integer pairwise distances" cleanly. The cleanest
  model takes the points as distinct integers (or `Fin n ↪ ℤ`), which makes the
  bound almost immediate; the modeling choice is the main design decision.
- Deciding whether to prove the general "integer distances on a line ⇒ integer
  coordinates (after scaling)" reduction or to adopt the integer-coordinate
  model as the problem statement.

### What Would a Proof Need?

- Key lemma 1: For a strictly increasing $\mathbb{Z}$-valued sequence $x$ of
  length $n$, $x_{n-1} - x_0 = \sum_{i<n-1}(x_{i+1}-x_i)$ (telescoping).
- Key lemma 2: each gap $x_{i+1}-x_i \ge 1$ (strict monotonicity over $\mathbb{Z}$).
- Technical requirements: `Finset.sum` telescoping, `Int`/`Nat` order lemmas,
  optionally `StrictMono` and `Finset.card` for the interval-counting variant.

## Tractability Assessment

**Difficulty**: Low | **Medium** | High | Moonshot

**Justification**:
- The core inequality is elementary (sum of $n-1$ positive integers $\ge n-1$).
- The only nontrivial part is the modeling of the hypothesis; with the
  integer-coordinate model the proof is short and fully verifiable.
- Mathlib provides all needed `Finset.sum` / `StrictMono` / `Int` order lemmas.

**Estimated Effort**:
- Exploration: a few hours (choosing the model)
- If tractable: 1–3 days for a clean, sorry-free Lean file
- If hard: unlikely; the collinear case is genuinely elementary

## References

### Papers
- Guth, L. and Katz, N. H., *On the Erdős distinct distances problem in the
  plane*, Annals of Mathematics 181(1):155–190, 2015 — best general bound.
- Anning, N. H. and Erdős, P., *Integral distances*, Bull. Amer. Math. Soc.
  51:598–600, 1945 — finiteness of non-collinear integer distance sets.

### Online Resources
- https://erdosproblems.com/100 — problem statement and status.
- OEIS A186704 — minimum diameter of $n$-point integer distance sets (planar).

### Mathlib
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum`, telescoping sums.
- `Mathlib.Order.Monotone.Basic` — `StrictMono` for the sorted point sequence.
- `Mathlib.Data.Int.Order` / `Mathlib.Data.Finset.Card` — integer interval
  cardinality and order lemmas for the counting variant.

## Metadata

```yaml
tags:
  - discrete-geometry
  - erdos
  - distance-sets
  - guth-katz
related_proofs:
  - erdos-100-oq-01
  - erdos-100-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-07-09T16:03:13-07:00
```
