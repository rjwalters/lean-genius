# Problem: Bohman–Keevash Lower Bound R(4,k) ≥ Ω(k^{5/2}/log²k) via the Triangle-Free Process

**Slug**: ramsey-r4k-oq-03
**Created**: 2026-07-09T15:22:58-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
R(4,k) \;\geq\; c \,\frac{k^{5/2}}{(\log k)^2}
\qquad \text{for some absolute constant } c > 0 \text{ and all sufficiently large } k,
$$

established by exhibiting a $K_4$-free graph $G$ on $n = \Theta\!\big(k^{5/2}/(\log k)^2\big)$ vertices whose independence number satisfies $\alpha(G) < k$. Equivalently, the triangle-free process on $\binom{n}{2}$ edges, run to completion, produces (with high probability) a triangle-free graph $G$ with
$$
\alpha(G) \;=\; O\!\big(\sqrt{n\,\log n}\big),
$$
from which the $R(4,k)$ bound follows by a standard blow-up / product construction turning a triangle-free graph into a $K_4$-free graph with controlled independence number.

### Plain Language

The Ramsey number $R(4,k)$ is the smallest $n$ such that every red/blue 2-coloring of the edges of the complete graph $K_n$ contains either a red $K_4$ or a blue $K_k$. To prove a *lower* bound $R(4,k) > n$ we must build a single coloring of $K_n$ with **no** red $K_4$ and **no** blue $K_k$; equivalently, a graph $G$ on $n$ vertices that is $K_4$-free (the red edges) and has independence number $\alpha(G) < k$ (no blue $K_k$).

Bohman and Keevash (2013) construct such graphs not by an explicit formula but by a *random greedy process*: start with the empty graph and repeatedly add a uniformly random edge subject to never creating a triangle (the "triangle-free process"), running until no more edges can be added. They show this yields, with high probability, a triangle-free graph on $n$ vertices whose largest independent set has size only $O(\sqrt{n \log n})$. Feeding this into a construction that converts triangle-freeness into $K_4$-freeness gives the record lower bound on $R(4,k)$.

The goal here is to formalize this argument — or a well-chosen tractable fragment of it — in Lean 4, most plausibly the *self-correcting* / martingale expectation estimates that drive the analysis of the process.

### Why This Matters

- **Records the best known lower bound.** Together with the Ajtai–Komlós–Szemerédi upper bound $R(4,k) = O(k^3/\log^2 k)$, the Bohman–Keevash bound $R(4,k) = \Omega(k^{5/2}/\log^2 k)$ pins the growth of $R(4,k)$ to the window $[k^{5/2}/\log^2 k,\; k^3/\log^2 k]$. Closing this gap is a central open problem in extremal combinatorics.
- **The triangle-free process is a flagship of the "algorithmic / self-correcting random process" method.** Bohman (2009) and independently Fiz Pontiveros–Griffiths–Morris (2020) and Bohman–Keevash used it to determine the order of magnitude of $R(3,k)$ up to a factor of $(1+o(1))$. Formalizing even the expectation heuristics would put a modern probabilistic-combinatorics technique into a proof assistant for the first time.
- **Bridges the probabilistic-method framework already in the gallery.** The parent entry (`ramsey-r4k`) contains a first-moment `expectedCliqueTerm` scaffold; this problem is the natural, deeper companion on the lower-bound side, moving from a static union bound to a dynamic random process.

## Known Results

### What's Already Proven

- **Parent gallery entry `ramsey-r4k`** — formalizes the Erdős–Szekeres upper bound $R(4,k) \le \binom{k+2}{3}$, the Pascal recursion $R(r,s) \le R(r-1,s)+R(r,s-1)$ (170-line `ramsey_recursion`), the cubic bound $R(4,k) \le (k+2)^3$, and a first-moment `expectedCliqueTerm` framework. Status `axiomatized` (numeric bounds via `native_decide`, `Lean.ofReduceBool`).
- **Erdős (1947), "Some remarks on the theory of graphs"** — the classical first-moment lower bound $R(s,s) > 2^{s/2}$; the paradigm we are extending to the dynamic setting.
- **Ajtai, Komlós, Szemerédi (1980)** — upper bound $R(4,k) = O(k^3/\log^2 k)$ via the deletion method (the matching upper side).
- **Bohman (2009), "The triangle-free process"** — proves the process survives for $\sim \tfrac{1}{2\sqrt2}\sqrt{n\log n}$ steps per vertex and gives $R(3,k) = \Omega(k^2/\log k)$; introduces the differential-equation-method analysis reused here.
- **Bohman, Keevash (2013), "The early evolution of the H-free process"** — the paper containing the $R(4,k) = \Omega(k^{5/2}/\log^2 k)$ lower bound (and general $R(s,k)$ bounds) via the $H$-free process.

### What's Still Open

- No formalization of the triangle-free process (or any self-correcting random graph process) exists in Lean/Mathlib.
- The exact asymptotics of $R(4,k)$ (closing the $k^{5/2}$ vs. $k^3$ gap) is open even on paper.
- Mathlib currently lacks the martingale concentration toolkit (Freedman/Azuma–Hoeffding for supermartingales with bounded differences) in the form these proofs use, and lacks a differential-equation-method (Wormald) library.

### Our Goal

Formalize a **tractable, self-contained fragment** of the lower-bound argument rather than the entire $\Omega(k^{5/2}/\log^2 k)$ theorem. Concretely, in decreasing order of ambition:

1. **(Reduction lemma, most tractable)** Formalize the deterministic reduction: *if there exists a triangle-free graph $G$ on $m$ vertices with $\alpha(G) < t$, then $R(4, f(t,m)) > g(t,m)$* for explicit $f,g$ coming from the standard "blow-up a triangle-free graph into a $K_4$-free graph" construction. This isolates the purely combinatorial step and reduces the Ramsey bound to a statement purely about triangle-free graphs with small independence number.
2. **(First-moment / expectation core)** Formalize the expected-value computations for the triangle-free process at a fixed time step: expected number of edges, of "open" (addable) pairs, and of copies of small configurations, matching the parent's `expectedCliqueTerm` style but for the dynamic process at a single step.
3. **(Full theorem, moonshot)** The complete high-probability bound $\alpha(G) = O(\sqrt{n\log n})$ with martingale concentration, yielding the Ramsey lower bound.

The realistic deliverable is (1) plus as much of (2) as concentration infrastructure allows.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramsey-r4k | Parent: fixes the definition of $R(4,k)$ / `RamseyProp`, proves the matching upper bound, and provides the first-moment `expectedCliqueTerm` scaffold this problem extends on the lower-bound side | Pascal recursion, Erdős–Szekeres bound, first-moment method, finset clique encoding |
| ramseys-theorem | Grandparent: existence/finiteness of $R(r,s)$; provides the ambient Ramsey framework | Pigeonhole, induction on $r+s$, monochromatic clique extraction |
| combinations-formula | Binomial-coefficient identities used throughout the expectation estimates ($\binom{n}{r}$, $\binom{r}{2}$) | Pascal's identity, induction on $n$ |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Deterministic reduction only (recommended first target).** Formalize the purely combinatorial implication "triangle-free graph with small $\alpha$ $\Rightarrow$ $K_4$-free coloring with small blue clique", encoded in the parent's `RamseyProp` / `Bool`-coloring language. Take the triangle-free graph's existence (with the $\alpha = O(\sqrt{n\log n})$ bound) as a stated hypothesis (an `axiom` or a hypothesis of the theorem), and derive the $R(4,k)$ lower bound from it.
   - Why it might work: this step is finite/combinatorial, uses only clique counting and neighborhood arguments already exercised in `ramsey_recursion` and `embed_from_finset`; no probability needed.
   - Risk: the "blow-up" construction that upgrades triangle-freeness to $K_4$-freeness must be stated correctly; getting the exact $f,g$ so that the asymptotic bound survives is fiddly.

2. **Approach B — Single-step expectation computation for the process.** Model the triangle-free process abstractly (a filtration of graphs $G_0 \subset G_1 \subset \dots$, each triangle-free) and prove the expected count of open pairs / edges at step $i$ matches the heuristic trajectory to first order.
   - Why it might work: mirrors the parent's static first-moment computation; expectations of counting random variables are linear and amenable to `Finset.sum` manipulation.
   - Risk: even defining the process (conditioning on triangle-freeness at each step) requires a clean probability-space model; Mathlib's `MeasureTheory`/`ProbabilityTheory` for discrete dynamic processes is usable but verbose, and the *self-correcting* estimates need martingale concentration that is not readily available.

### Key Difficulties

- **Modeling a conditioned random process.** The triangle-free process conditions each step on not creating a triangle; formalizing this stopping/rejection dynamics cleanly is the crux.
- **Concentration inequalities.** The analysis relies on Freedman/Azuma-type supermartingale bounds with bounded differences over $\Theta(n^{3/2}\sqrt{\log n})$ steps; Mathlib's martingale library may not yet expose the exact form needed.
- **Differential-equation method.** The trajectory tracking is usually done via Wormald's DE method; there is no such library, so any faithful formalization must replace it with explicit discrete supermartingale estimates.
- **Asymptotic bookkeeping.** Carrying $O(\cdot)$/$\Omega(\cdot)$ constants and $\log$ factors through to a clean $\Omega(k^{5/2}/\log^2 k)$ statement requires disciplined `Filter.Tendsto`/`Asymptotics.IsBigO` accounting.

### What Would a Proof Need?

- **Key lemma 1 (reduction):** `triangleFree G → G.indepNum < t → RamseyProp (blowupSize t G) 4 (k t) = False`-style statement, i.e. an explicit $K_4$-free, blue-$K_k$-free coloring built from $G$.
- **Key lemma 2 (independence bound, hypothesis or target):** existence of a triangle-free graph on $n$ vertices with $\alpha(G) \le C\sqrt{n\log n}$ (the Bohman/Kim/Bohman–Keevash output).
- **Key lemma 3 (expectation trajectory):** at step $i$ of the process, $\mathbb{E}[\#\text{open pairs}] \approx n^2 e^{-4t^2}$ (in the standard $t = i/n^{3/2}$ scaling), plus the analogous edge-count estimate.
- **Technical requirements:** a graph-process model (filtration of `SimpleGraph`s), `SimpleGraph.CliqueFree` / independence-number API, `Finset.sum` linearity-of-expectation lemmas, and — for the full theorem — supermartingale concentration.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The *full* Bohman–Keevash theorem is a research-level probabilistic argument (self-correcting process + concentration + DE method) and is a genuine moonshot to formalize end-to-end.
- However, **Approach A** (the deterministic reduction, with the triangle-free-graph existence taken as a stated hypothesis) is a genuinely tractable High-difficulty target: it reuses the parent's `RamseyProp`/`embed_from_finset` clique machinery and needs no probability.
- Comparable formalized results: the parent `ramsey-r4k` already formalizes the Pascal recursion and first-moment scaffold; Mathlib contains `SimpleGraph.CliqueFree`, Ramsey-number lemmas (`Combinatorics.SimpleGraph.Ramsey`), and a growing `ProbabilityTheory` martingale library, so the ingredients for the reduction and single-step expectation exist.
- Relevant Mathlib modules: `Mathlib.Combinatorics.SimpleGraph.Clique`, `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic`, `Mathlib.Combinatorics.SimpleGraph.Ramsey`, `Mathlib.Data.Nat.Choose.Basic`, `Mathlib.Probability.Martingale.Basic`, `Mathlib.Probability.Independence.Basic`.

**Estimated Effort**:
- Exploration: 3–5 days (scope the reduction lemma; audit Mathlib's triangle/independence/martingale API).
- If tractable (Approach A + single-step expectation): 3–6 weeks.
- If hard (full high-probability theorem): unknown / open-ended.

## References

### Papers
- T. Bohman and P. Keevash, "The early evolution of the H-free process", *Inventiones Mathematicae* 181 (2010/2013), 291–336 — proves $R(4,k) = \Omega(k^{5/2}/\log^2 k)$ (and general $R(s,k)$ bounds) via the $H$-free process.
- T. Bohman, "The triangle-free process", *Advances in Mathematics* 221 (2009), 1653–1677 — introduces the triangle-free process analysis and gives $R(3,k) = \Omega(k^2/\log k)$.
- G. Fiz Pontiveros, S. Griffiths, R. Morris, "The triangle-free process and the Ramsey number R(3,k)", *Memoirs of the AMS* 263 (2020) — sharp analysis of the same process.
- M. Ajtai, J. Komlós, E. Szemerédi, "A note on Ramsey numbers", *J. Combin. Theory Ser. A* 29 (1980), 354–360 — matching upper bound $R(4,k) = O(k^3/\log^2 k)$.
- P. Erdős, "Some remarks on the theory of graphs", *Bull. Amer. Math. Soc.* 53 (1947), 292–294 — the classical first-moment Ramsey lower bound.
- P. Erdős and G. Szekeres, "A combinatorial problem in geometry", *Compositio Math.* 2 (1935), 463–470 — the binomial upper bound and Pascal recursion (parent's upper side).

### Online Resources
- Radziszowski, "Small Ramsey Numbers", *Electronic Journal of Combinatorics* Dynamic Survey DS1 — canonical table of known $R(4,k)$ bounds and constructions.
- Morris, lecture notes on "The triangle-free process" (IMPA) — expository account of the differential-equation-method analysis.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Clique` — `CliqueFree`, clique/independent-set predicates for encoding $K_4$-freeness and $\alpha(G) < k$.
- `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic` — triangle-free graph API for the process.
- `Mathlib.Combinatorics.SimpleGraph.Ramsey` — Ramsey number definitions/bounds to connect with `RamseyProp`.
- `Mathlib.Probability.Martingale.Basic` / `Mathlib.Probability.Martingale.Convergence` — martingale/supermartingale scaffolding for the concentration step.
- `Mathlib.Data.Nat.Choose.Basic` — binomial coefficients for the expectation estimates.

## Metadata

```yaml
tags:
  - combinatorics
  - ramsey-theory
  - graph-theory
  - probabilistic-method
  - random-processes
  - lower-bounds
related_proofs:
  - ramsey-r4k
  - ramseys-theorem
  - combinations-formula
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:58-07:00
```
