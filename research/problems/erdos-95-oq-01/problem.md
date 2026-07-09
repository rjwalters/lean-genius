# Problem: Necessity of the log n Factor in the Guth–Katz Distance Bound

**Slug**: erdos-95-oq-01
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

For $n$ points $x_1, \ldots, x_n \in \mathbb{R}^2$ with distance multiplicities $f(u_i)$ (the number of ordered pairs realizing distance $u_i$), Guth–Katz (2015) proved the upper bound

$$
\sum_{i=1}^{t} f(u_i)^2 \; \le \; C \cdot n^3 \log n .
$$

The open question is whether the $\log n$ factor is intrinsic. Concretely: does there exist an absolute constant $C'$ such that every planar $n$-point configuration satisfies $\sum_i f(u_i)^2 \le C' \cdot n^3$, or is the $\log n$ factor forced by some family of configurations? The formalizable core is the *tightness* direction — that the $\sqrt{n}\times\sqrt{n}$ integer lattice $L_n$ attains

$$
\sum_{i} f(u_i)^2 \; \ge \; c \cdot n^3 \log n \qquad (c > 0),
$$

so the $\log n$ cannot be removed in general, while for configurations *avoiding* lattice-like additive structure the bound $O(n^3)$ may hold.

### Plain Language

The Guth–Katz theorem says that if you take $n$ points in the plane and, for each distance value, count how many pairs of points are exactly that far apart, then the sum of the squares of these counts is at most about $n^3 \log n$. The question here is: is that extra $\log n$ genuinely needed, or is it an artifact of the proof? For the square integer grid the answer is that the $\log n$ *is* needed — the grid actually achieves $\sim n^3 \log n$. So the interesting refined question is whether the $\log n$ disappears once your points are *not* arranged in a rigid arithmetic pattern (a lattice). We want to formalize the lattice lower bound (log is necessary in general) and specify precisely the "non-lattice" conjecture (log may be removable otherwise).

### Why This Matters

The gap between the conjectured $n^{3+\varepsilon}$ (Erdős), the achieved $n^3 \log n$ (Guth–Katz), and the possible $n^3$ (no log) is one of the last quantitative mysteries in the distinct-distances circle of problems. Resolving it would pin down the exact extremal behavior of distance multiplicities, sharpen the dual bound on distinct distances ($t \gg n / \log n$ versus $t \gg n$), and clarify whether the $\log n$ is a real geometric phenomenon or a limitation of polynomial partitioning. The lattice lower bound also connects planar discrete geometry directly to classical analytic number theory (sums of two squares), making it an unusually clean bridge between fields.

## Known Results

### What's Already Proven

- Guth–Katz upper bound $\sum_i f(u_i)^2 \le C n^3 \log n$ — Guth & Katz, *On the Erdős distinct distances problem in the plane*, Annals of Mathematics 181 (2015). Axiomatized in the gallery as `guth_katz_theorem` in `Proofs/Erdos95Problem.lean` (`erdos-95`).
- Erdős's $n^{3+\varepsilon}$ conjecture, derived from Guth–Katz by absorbing $\log n$ into $n^\varepsilon$ — proved in the gallery as `erdos_conjecture_proved` (`erdos-95`, 0 sorries).
- Cauchy–Schwarz bridge $(n(n-1))^2 \le t \cdot \sum_i f(u_i)^2$ giving distinct-distances $t \gg n/\log n$ — proved in the gallery as `sq_sum_multiplicities_le` / `distinctDistances_lower_bound` (`erdos-95`, 0 axioms for the bridge).
- Ramanujan's identity $\sum_{m \le x} r_2(m)^2 \sim c\, x \log x$, where $r_2(m)$ counts representations of $m$ as a sum of two squares — classical analytic number theory. This is the source of the lattice's $\log n$ factor.
- Convex-position case $\sum_i f(u_i)^2 = O(n^3)$ (no log) — Altman (1963), Fishburn; axiomatized as `convex_polygon_case` (`erdos-95`).

### What's Still Open

- Whether $\sum_i f(u_i)^2 \le C n^3$ (no log) holds for all "non-lattice" configurations, and how to make "non-lattice" precise (e.g. bounded additive energy, or points in general algebraic position).
- Whether the $\log n$ in the *general* upper bound is truly unavoidable at the level of the constant, i.e. matching the lattice lower bound with a general upper bound of the same order for the worst case.

### Our Goal

Formalize the **lattice lower bound**: define the $\sqrt{n}\times\sqrt{n}$ integer lattice $L_n \subset \mathbb{R}^2$ as a `PointConfig`, and prove $\sum_i f(u_i)^2 \ge c\, n^3 \log n$ for it (for $n$ a perfect square, $n$ large). This establishes rigorously that the $\log n$ factor cannot be dropped from the general Guth–Katz bound. As a companion, state (without necessarily proving) the precise "non-lattice removability" conjecture as a Lean proposition parameterized by an additive-structure hypothesis, so a future researcher has a formal target.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-95 | Parent problem: defines `PointConfig`, `multiplicity`, `sumSquaredMultiplicities`, and axiomatizes the Guth–Katz upper bound this question refines | Polynomial method, Cauchy–Schwarz duality, Euclidean-plane formalization |
| erdos-105 | Companion distinct-distances / incidence-geometry problem sharing the Elekes–Sharir and incidence-bound machinery | Incidence geometry, discrete geometry |
| erdos-210 | Related discrete-geometry problem on distance/incidence configurations | Incidence geometry, extremal configurations |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Direct lattice computation via representation counts.**
   Work with $L_n = \{0,\dots,\sqrt{n}-1\}^2$. A squared distance $m = a^2 + b^2$ occurs (up to boundary effects) $\approx n \cdot r_2(m)$ times, so $f(\sqrt m) \gtrsim c\, n\, r_2(m)$ for $m \lesssim n$. Then $\sum_i f(u_i)^2 \gtrsim c^2 n^2 \sum_{m \le c'n} r_2(m)^2 \sim c'' n^2 \cdot n \log n = c'' n^3 \log n$ by Ramanujan's estimate.
   - Why it might work: The chain reduces a geometric claim to a single, classical number-theoretic asymptotic; all pieces are elementary once $\sum r_2(m)^2 \sim x \log x$ is available.
   - Risk: Mathlib currently lacks $\sum_{m\le x} r_2(m)^2 \sim c x \log x$; supplying it may require substantial analytic-number-theory scaffolding, or an axiom.

2. **Approach B — Lower bound via the number of distinct distances, avoiding fine $r_2$ asymptotics.**
   Combine the Cauchy–Schwarz bridge with a translation-invariance / lattice-symmetry counting: the lattice has $\sim n \cdot \pi$ (i.e. $\Theta(n)$) distinct distances but each frequent distance has multiplicity $\gg n/\sqrt{\log n}$ on average; a second-moment (variance) argument over lattice translations forces a $\log n$ surplus in $\sum f^2$.
   - Why it might work: Sidesteps sharp Ramanujan asymptotics by needing only lower bounds on high-multiplicity distances, which come from divisor-type counts that Mathlib can support more readily.
   - Risk: Getting the *exact* $\log n$ (not just a super-$n^3$ bound) still ultimately needs the second moment of $r_2$; weaker inputs may only yield $\gg n^3$ without the logarithm.

### Key Difficulties

- Formalizing $\sum_{m \le x} r_2(m)^2 \sim c x \log x$ (Ramanujan) — the crux; Mathlib has `Nat.sq_add_sq` / sum-of-two-squares theory but not this second-moment asymptotic.
- Boundary/edge effects: distances near a lattice point undercount by $O(\sqrt n)$-fringe terms; need clean lower bounds robust to the boundary.
- Choosing $n$ a perfect square and handling the $\sqrt n \times \sqrt n$ indexing cleanly in Lean.

### What Would a Proof Need?

- Key lemma 1: a lattice `PointConfig` `latticeConfig (k : ℕ) : PointConfig` for the $k \times k$ grid with `card = k^2`.
- Key lemma 2: `multiplicity (latticeConfig k) (Real.sqrt m) ≥ c * k^2 * r2(m)` for $m$ in a suitable range (translation lower bound).
- Key lemma 3 (analytic): `∑ m in range N, (r2 m)^2 ≥ c' * N * Real.log N` (Ramanujan lower bound), possibly introduced as a stated hypothesis/axiom if not in Mathlib.
- Assembly: chain the above to `sumSquaredMultiplicities (latticeConfig k) ≥ c'' * (k^2)^3 * Real.log (k^2)`.
- Technical requirements: `Finset` fibre counting (reuse `sum_multiplicities` pattern), `Real.log` monotonicity, sum-of-two-squares representation counts.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The geometric-to-number-theoretic reduction (multiplicities $\to$ $r_2$ counts) is clean and reuses gallery infrastructure (`multiplicity`, `sumSquaredMultiplicities`, fibre counting), which is encouraging.
- However, the essential analytic input $\sum_{m\le x} r_2(m)^2 \sim c\, x\log x$ is not in Mathlib and is genuinely nontrivial to formalize from scratch; obtaining the true $\log n$ (rather than merely $\gg n^3$) hinges on it.
- Similar "extremal lattice attains the bound" results are known to be hard to fully formalize because they mix combinatorics, geometry, and analytic number theory. A partial result ($\sum f^2 \gg n^3$, log stated as hypothesis) is realistically achievable; the full sharp $\log n$ is a stretch.
- Relevant Mathlib support exists for sums of two squares and real logs, lowering the geometric barrier even if the analytic one remains.

**Estimated Effort**:
- Exploration: several days (survey Mathlib $r_2$ / sum-of-two-squares API, prototype the lattice config)
- If tractable: 2–4 weeks for the $\gg n^3$ lower bound with the Ramanujan estimate taken as a hypothesis
- If hard: unknown (formalizing $\sum r_2^2 \sim x\log x$ could be a project in itself)

## References

### Papers
- L. Guth and N. H. Katz, *On the Erdős distinct distances problem in the plane*, Annals of Mathematics 181 (2015), 155–190 — proves $\sum f(u_i)^2 \ll n^3 \log n$ and $t \gg n/\log n$; the theorem whose log factor is in question.
- P. Erdős, *On sets of distances of n points*, American Mathematical Monthly 53 (1946), 248–250 — origin of the distinct-distances and multiplicity problems; conjectured $n^{3+\varepsilon}$.
- E. Altman, *On a problem of P. Erdős*, American Mathematical Monthly 70 (1963), 148–157 — convex-position case with $O(n^3)$ (no log), a model for the non-lattice conjecture.
- S. Ramanujan, *On the expression of a number in the form $ax^2+by^2+cz^2+du^2$* and related work on $r_2$; the asymptotic $\sum_{m\le x} r_2(m)^2 \sim c\, x\log x$ is standard analytic number theory (see also Grosswald, *Representations of Integers as Sums of Squares*, Springer 1985).
- J. Solymosi and C. D. Tóth, *Distinct distances in the plane*, Discrete & Computational Geometry 25 (2001), 629–634 — pre-Guth–Katz incidence bounds on the same quantities.

### Online Resources
- https://erdosproblems.com/95 — Erdős Problem #95 statement, status (solved, \$500), and references.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` — model of $\mathbb{R}^2$ as `EuclideanSpace ℝ (Fin 2)` for the lattice configuration.
- `Mathlib.NumberTheory.SumTwoSquares` / `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — representations of integers as sums of two squares, underlying $r_2(m)$.
- `Mathlib.Data.Real.Basic` and `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log` for the $\log n$ factor.
- `Mathlib.Data.Finset.Basic` and `Mathlib.Algebra.BigOperators` — fibre decomposition and `Finset.sum` for multiplicity counting (reuse the `sum_multiplicities` pattern from `erdos-95`).

## Metadata

```yaml
tags:
  - discrete-geometry
  - distinct-distances
  - incidence-geometry
  - polynomial-method
  - number-theory
related_proofs:
  - erdos-95
  - erdos-105
  - erdos-210
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
