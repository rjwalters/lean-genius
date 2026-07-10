# Problem: Complete Achievable Line-Count Spectrum for Small n (n ≤ 20)

**Slug**: erdos-606-oq-02
**Created**: 2026-07-09T16:59:48-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{For each } n \le 20,\ \text{determine } L(n) := \Big\{\, \ell(P) : P \subseteq \mathbb{R}^2,\ |P| = n \,\Big\}, \quad \text{where } \ell(P) = \big|\{\, \overline{pq} : p,q \in P,\ p \ne q \,\}\big|.
$$

Here $\ell(P)$ is the number of distinct lines determined by the point set $P$, ranging over $1$ (all points collinear) and $\binom{n}{2}$ (general position, no three collinear). The Erdős–Salamon theorem asserts that **for sufficiently large $n$**,
$$
L(n) = \{1\} \cup \Big([n,\ \tbinom{n}{2}] \setminus \{\tbinom{n}{2}-1,\ \tbinom{n}{2}-3\}\Big).
$$
The open question is to compute $L(n)$ **exactly** for each small $n$ (say $n \le 20$), where the asymptotic characterization is not known to apply and the answer must be pinned down combinatorially.

### Plain Language

If you place $n$ dots on a piece of paper, connect every pair with a straight line, and count how many *distinct* lines you drew, which totals are actually possible? For very large $n$ the answer is known: every number from $n$ up to $\binom{n}{2}$ works, except the two values $\binom{n}{2}-1$ and $\binom{n}{2}-3$, plus the special value $1$ when all points are on one line. But for small $n$ (like $n = 7, 10, 20$) the clean asymptotic rule is not guaranteed to hold, and nobody has published the full list of achievable counts. The goal is to determine, for each small $n$, exactly which line-counts can occur.

### Why This Matters

The parent problem (`erdos-606`) is an *asymptotic* spectrum theorem: it says what happens for large $n$ but gives no effective threshold $N_0$ and no information about small cases. Small-$n$ enumeration is where the geometry is subtlest — near-degenerate configurations, the boundary between "few lines" (dense collinearity) and "many lines" (near general position), and the discrete "gaps" all interact. A complete small-$n$ table would (a) reveal whether extra gaps appear below the asymptotic threshold, (b) provide ground-truth data to calibrate the constant $N_0$, and (c) supply verified test cases that any formalization of the general theorem must respect. It is a finite but genuinely hard combinatorial-geometry computation, closely tied to the orchard problem and to the enumeration of point-line configurations.

## Known Results

### What's Already Proven

- **Erdős–Salamon characterization (1988)** — `erdos-606`: for sufficiently large $n$, $L(n) = \{1\} \cup [n, \binom{n}{2}] \setminus \{\binom{n}{2}-1, \binom{n}{2}-3\}$. The threshold $N_0$ is not made explicit.
- **Sylvester–Gallai / Motzkin lower bound** — `erdos-606` (axiom `numDistinctLines_min_noncollinear`, `sylvester_gallai`): any set of $n \ge 3$ non-collinear points determines at least $n$ distinct lines (Motzkin 1951, via the ordinary line guaranteed by Gallai 1944). Hence $L(n) \subseteq \{1\} \cup [n, \binom{n}{2}]$.
- **Gap values are genuinely excluded for all $n$** — `erdos-606` (axioms `not_achievable_max_minus_1`, `not_achievable_max_minus_3`): $\binom{n}{2}-1$ and $\binom{n}{2}-3$ are *never* achievable, because each collinear triple drops the count by $\binom{3}{2}-1 = 2$, each collinear $k$-tuple by $\binom{k}{2}-1 \ge 2$, and $1$ and $3$ are not expressible as sums of integers $\ge 2$. This impossibility is elementary and holds for *every* $n$, small or large.
- **$\binom{n}{2}-2$ is achievable** — `erdos-606` (axiom `achievable_max_minus_2`): exactly one collinear triple with all other points in general position.

### What's Still Open

- The **exact set** $L(n)$ for each fixed small $n \le 20$ (only endpoints and the top few values are pinned down rigorously; the low range $[n, \sim cn^{3/2}]$ is the open part).
- Whether any **additional gaps** (beyond $\binom{n}{2}-1$ and $\binom{n}{2}-3$) occur for small $n$ below the asymptotic threshold.
- The precise **smallest $n$** at which the full Erdős–Salamon interval structure first holds.

### Our Goal

Rigorously determine $L(n)$ for the smallest tractable cases — begin with $n \le 7$, where $\binom{n}{2} \le 21$ and complete enumeration of order types is feasible — and formalize (i) the universal exclusion of $\binom{n}{2}-1$ and $\binom{n}{2}-3$, (ii) explicit witnessing configurations for each *claimed-achievable* value, and (iii) a certified statement of the finite achievable set for at least $n \in \{3,4,5,6,7\}$. Extending the certified table toward $n = 20$ is the stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-606 | Parent problem: the asymptotic characterization whose small-$n$ instances we enumerate | Sylvester–Gallai, Beck's theorem, Szemerédi–Trotter, gap analysis |
| erdos-606-oq-01 | Sibling open question on the same #606 configuration; shares the point/line/collinearity Lean scaffolding | Incidence combinatorics |
| combinations-formula | Supplies $\binom{n}{2} = n(n-1)/2$, the maximum line count and the reference frame for the "gap" values | Binomial coefficient identities |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Exhaustive order-type enumeration (small $n$)**: For $n \le 7$ (and possibly up to $n \approx 10$), enumerate all combinatorial *order types* (equivalently, all realizable oriented matroids of rank 3) of $n$ points, compute the number of distinct lines for each, and take the set of values. The order-type databases (Aichholzer et al.) tabulate exactly these up to $n = 11$.
   - Why it might work: for small $n$ the number of order types is finite and known; each determines $\ell(P)$ purely combinatorially (which triples are collinear), so no floating-point geometry is needed.
   - Risk: realizability of a collinearity pattern is not automatic (Mnëv universality lurks), so one must use *realizable* order types, not abstract matroids; the databases handle this but must be trusted or re-derived.

2. **Approach B — Constructive filling + exclusion proofs**: Prove membership by exhibiting explicit rational point sets (all-collinear → $1$; general position → $\binom{n}{2}$; one triple → $\binom{n}{2}-2$; grids and near-pencils for the low range), and prove non-membership only for the two universal gaps via the reduction-sum argument.
   - Why it might work: the endpoints and top values have clean witnesses; the exclusion argument is elementary number theory and is already axiomatized in the parent proof.
   - Risk: the *low* range $[n, \sim cn^{3/2}]$ is exactly where constructions are hardest and where Salamon's original argument is delicate; naive grids leave holes that are hard to certify for each individual small $n$.

### Key Difficulties

- Certifying **collinearity/non-collinearity** of explicit configurations rigorously (exact-arithmetic determinant tests) rather than by picture.
- The **low end** $[n, cn^{3/2}]$ of the spectrum, where achievability requires clever constructions (near-pencils, grids, points on conics) and is not covered by the simple "top values" arguments.
- Distinguishing **realizable** point configurations from merely combinatorial collinearity patterns (an abstract "which triples are collinear" table need not be geometrically realizable).

### What Would a Proof Need?

- Key lemma 1: an **exact-arithmetic collinearity predicate** for rational points via the $2\times 2$ determinant $\det\!\big(q-p,\ r-p\big) = 0$, letting each candidate configuration's line count be computed by kernel-checkable rational arithmetic.
- Key lemma 2: the **reduction-sum exclusion** — the achievable *deficits* $\binom{n}{2}-\ell(P)$ form a subset of the numerical semigroup generated by $\{\binom{k}{2}-1 : k \ge 3\} = \{2,5,9,14,\dots\}$-style contributions, so deficits $1$ and $3$ are impossible.
- Technical requirements: a finite library of explicit witness configurations (all-collinear, general-position, single-triple, near-pencil, small grid) with machine-checked line counts, ideally reusing the `PointConfig`/`Collinear`/`onLine` definitions from `Erdos606Problem.lean`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The universal exclusion of $\binom{n}{2}-1$ and $\binom{n}{2}-3$ and the endpoint achievability are genuinely tractable and could be formalized cleanly; but the *complete* enumeration of $L(n)$ for the low range even at a single small $n$ requires either trusted order-type data or a substantial construction library.
- Similar finite-geometry enumerations (order types up to $n = 11$, the orchard problem's optimal-line configurations) have been carried out computationally but their *formal* verification in Lean is largely unexplored.
- Mathlib provides affine independence and the Euclidean plane but no incidence-geometry or order-type infrastructure, so much scaffolding must be built.

**Estimated Effort**:
- Exploration: several days (survey order-type data, fix the rational-collinearity framework)
- If tractable (endpoints + gaps + $n \le 5$): 1–2 weeks
- If hard (certified $L(n)$ for all $n \le 20$): unknown / research-scale

## References

### Papers
- P. Erdős, G. Purdy, *Extremal problems in combinatorial geometry*, in Handbook of Combinatorics (1995) — survey context for line-counting spectra.
- P. Erdős, "Problems and results in combinatorial geometry" — origin of Problem #606 (1985).
- J. Beck, *On the lattice property of the plane and some problems of Dirac, Motzkin, and Erdős in combinatorial geometry*, Combinatorica 3 (1983) — the dichotomy underlying the spectrum's shape.
- O. Aichholzer, F. Aurenhammer, H. Krasser, *Enumerating order types for small point sets with applications*, Order 19 (2002) — the enumeration data that makes small-$n$ computation possible.

### Online Resources
- https://erdosproblems.com/606 — the canonical statement and status of Problem #606.
- http://www.ist.tugraz.at/staff/aichholzer/research/rp/triangulations/ordertypes/ — Aichholzer's order-type database for small point sets.

### Mathlib
- `Mathlib.LinearAlgebra.AffineSpace.Independent` — affine independence, the basis for a rigorous collinearity predicate (three points collinear ⟺ affinely dependent).
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` — the concrete Euclidean plane `EuclideanSpace ℝ (Fin 2)` used by the parent proof.
- `Mathlib.Data.Finset.Card` — cardinality reasoning for counting the finite set of distinct lines.

## Metadata

```yaml
tags:
  - discrete-geometry
  - incidence-geometry
  - combinatorial-geometry
  - erdos
related_proofs:
  - erdos-606
  - erdos-606-oq-01
  - combinations-formula
difficulty: high
source: gallery-gap
created: 2026-07-09T16:59:48-07:00
```
