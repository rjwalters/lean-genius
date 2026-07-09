# Problem: Closing the Logarithmic Gap in Beck's Circle Discrepancy Bound

**Slug**: erdos-989-oq-01
**Created**: 2026-07-09T15:23:00-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $A = \{z_1, z_2, \dots\} \subset \mathbb{R}^2$ be an infinite sequence of points and let
$f_A(r) = \sup_C \bigl| \#(A \cap C) - \pi r^2 \bigr|$ denote the circle discrepancy, where the
supremum ranges over all disks $C$ of radius $r$. Beck (1987) established

$$
c\,\sqrt{r} \;\le\; \inf_A f_A(r) \;\le\; C\,\sqrt{r \log r}
\qquad\text{for suitable constants } 0 < c \le C.
$$

The open question is whether the logarithmic factor is necessary. Concretely, we ask which of
the following holds for the extremal growth rate $g(r) := \inf_A f_A(r)$:

$$
\textbf{(Conjecture A: log is removable)}\quad \exists\, A,\ C > 0 : \ f_A(r) \le C\sqrt{r}\ \text{ for all large } r,
$$
$$
\textbf{(Conjecture B: log is forced)}\quad \exists\, c' > 0 : \ f_A(r) \ge c'\sqrt{r \log r}\ \text{ for all } A \text{ and all large } r.
$$

Deciding between (A) and (B) — i.e. pinning down $g(r)$ to $\Theta(\sqrt r)$ or $\Theta(\sqrt{r\log r})$
— has been open since 1987.

### Plain Language

Beck proved that if you scatter infinitely many points in the plane, then for circles of radius
$r$ the count of enclosed points must deviate from the "expected" area $\pi r^2$ by at least about
$\sqrt{r}$, and that a cleverly randomized arrangement keeps the deviation down to about
$\sqrt{r \log r}$. There is a small but stubborn gap: a factor of $\sqrt{\log r}$ separates the best
known lower bound from the best known upper bound. The question is: is the truth $\sqrt{r}$ (so the
log is just an artifact of Beck's union-bound proof), or is it genuinely $\sqrt{r \log r}$ (so no
point set can do better)? Our formalization target is not to resolve this gap — it is to state the
gap rigorously and prove the structural "squeeze" lemmas that any resolution must pass through.

### Why This Matters

This is the flagship open sub-question of a fully solved Erdős problem: Beck determined the growth
rate of circle discrepancy up to a single $\sqrt{\log r}$ factor, and closing it would give the
*exact* order of geometric discrepancy for the most natural curved test family. The analogous
$\log$-gap question drives a large part of modern discrepancy theory (boxes, half-planes, spheres),
so a resolution — in either direction — would be a landmark. Formalizing the precise statement, the
relationship between the two conjectures, and the reduction lemmas makes the open problem
machine-checkable and provides scaffolding for future proof attempts.

## Known Results

### What's Already Proven

- Beck's universal lower bound $f_A(r) \gg \sqrt{r}$ for all $A$ — Beck, "Irregularities of
  distribution I", *Acta Math.* **159** (1987), 1–49; formalized as the axiom `beck_lower_bound`
  in `Proofs/Erdos989Problem.lean` (gallery proof `erdos-989`).
- Beck's existence upper bound $\exists A,\ f_A(r) \ll \sqrt{r \log r}$ — same paper; formalized
  as the axiom `beck_upper_bound` and witnessed via `beckOptimalSequence` (Classical.choose).
- Unboundedness $f_A(r) \to \infty$ for every $A$ — derived theorem `discrepancy_unbounded` in the
  parent Lean file.
- Comparison landmarks: Roth's $\gg \sqrt{\log N}$ box discrepancy (1954), Schmidt's extension
  (1972), and Alexander's half-plane bound $\gg r^{1/4}$ (1990), showing circles ($\sqrt r$) are
  strictly harder than half-planes.

### What's Still Open

- Whether $g(r) = \inf_A f_A(r)$ has order $\sqrt r$ or $\sqrt{r \log r}$ (Conjectures A vs. B above).
- Whether Beck's $\sqrt{\log r}$ loss from the union bound over $O(r^2)$ circle centers is
  intrinsic or an artifact of the second-moment argument.
- Whether any *explicit* (non-randomized) sequence attains even $O(\sqrt{r \log r})$.

### Our Goal

Formalize the open problem precisely and prove the *structural* results that frame it, without
resolving the gap. Specifically: (1) define $g(r) = \inf_A f_A(r)$ (or an order-of-magnitude proxy)
inside the `Erdos989` namespace; (2) state Conjectures A and B as Lean propositions; (3) prove the
**squeeze lemma** that Beck's two bounds imply $c\sqrt r \le g(r) \le C\sqrt{r\log r}$; and (4) prove
the **dichotomy lemma** that (A) and (B) are mutually exclusive for large $r$ (since
$\sqrt{r\log r}/\sqrt r = \sqrt{\log r} \to \infty$), so at most one can hold. These are provable
from the existing axioms plus real-analysis facts (`Real.sqrt`, `Real.log` monotonicity/growth).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-989 | Parent problem: defines $f_A(r)$, `circleDiscrepancy`, and both Beck bounds as axioms | Fourier analysis, Bessel $J_1$ asymptotics, probabilistic method |
| erdos-988 | Companion spherical-cap discrepancy with the same $\sqrt{\text{boundary}}$ heuristic and analogous log gap | Schmidt spherical-cap theorem, harmonic analysis on $S^2$ |
| erdos-990 | Angular discrepancy of polynomial roots on the unit circle; shares the log-loss union-bound structure | Erdős–Turán inequality, exponential sums |
| fourier-series | Foundational Fourier theory underpinning Beck's lower bound via the disk indicator's transform | Fourier coefficients, Parseval's identity |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Framing/squeeze formalization (target)**: Define $g(r)$ as the infimal
   discrepancy and derive the two-sided bound directly from `beck_lower_bound` and
   `beck_upper_bound`, then prove the log-growth dichotomy from `Real.log` asymptotics.
   - Why it might work: purely a consequence of already-axiomatized bounds plus standard Mathlib
     real-analysis lemmas ($\sqrt{r\log r} = \sqrt r \cdot \sqrt{\log r}$ and
     $\sqrt{\log r} \to \infty$). No new mathematics required.
   - Risk: the infimum over all sequences $A$ may not be a well-defined real for every $r$
     (need a `sInf` over a nonempty, bounded-below set); careful handling of `Real.sInf` edge cases
     and eventual (large-$r$) quantifiers is required.

2. **Approach B — Attack the gap via a sharper union bound (research, not formalization target)**:
   Replace Beck's crude union bound over $O(r^2)$ centers with a chaining / Dudley-type entropy
   bound, aiming to shave the $\sqrt{\log r}$ and prove Conjecture A.
   - Why it might work: chaining routinely removes logarithmic losses in Gaussian/empirical-process
     discrepancy arguments; the circle-center family has controlled metric entropy.
   - Risk: this is a genuine open research problem — decades of effort have not settled it, so a
     full formalization of a resolution is out of scope. We flag it as the intended *downstream*
     use of the scaffolding.

### Key Difficulties

- Defining $g(r) = \inf_A f_A(r)$ rigorously in Lean: the class of point sequences is a function
  type, and the discrepancy is already an `iSup`; nesting an `sInf` over sequences needs a
  boundedness/nonemptiness witness (Beck's bounds supply both).
- The bounds are *eventual* (hold for all large $r$) with existential constants; matching quantifier
  order between the lower bound (∀ A, ∃ c) and upper bound (∃ A, ∃ C) when forming $\inf_A$.
- Proving $\sqrt{\log r} \to \infty$ and hence the strict separation of the two conjectures cleanly
  via `Real.log` and `Filter.Tendsto` at `atTop`.

### What Would a Proof Need?

- Key lemma 1 (`extremal_discrepancy_wellDefined`): for each $r > 1$, the set
  $\{ f_A(r) : A \text{ a point sequence} \}$ is nonempty and bounded below by $0$, so
  $g(r) := \inf_A f_A(r)$ exists in $\mathbb{R}$.
- Key lemma 2 (`beck_squeeze`): $\exists\, c, C > 0$ with
  $c\sqrt r \le g(r) \le C\sqrt{r\log r}$ eventually, derived from `beck_lower_bound` (lower) and
  `beck_upper_bound` witness `beckOptimalSequence` (upper).
- Key lemma 3 (`log_gap_dichotomy`): $\sqrt{r\log r}/\sqrt r = \sqrt{\log r} \to \infty$ as
  $r \to \infty$, hence Conjecture A and Conjecture B cannot both hold; at most one is true.
- Technical requirements: `Real.sqrt` monotonicity and multiplicativity, `Real.log` positivity and
  divergence at `atTop`, `Real.sInf`/`csInf_le`/`le_csInf`, `Filter.Tendsto ... atTop`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The framing lemmas (squeeze and dichotomy) follow from already-axiomatized Beck bounds plus
  standard Mathlib real analysis, so they are genuinely formalizable — this is the concrete,
  medium-effort target.
- Resolving the gap itself (Approach B) is a Moonshot open since 1987 and is explicitly *not* the
  formalization goal; the deliverable is a rigorous statement plus reduction lemmas.
- Comparable "define the extremal quantity + squeeze it between known bounds" tasks appear in the
  parent proof (`discrepancy_unbounded` already chains `Real.sqrt` monotonicity), giving a template.
- Mathlib provides all needed real-analysis infrastructure (`Real.sqrt`, `Real.log`,
  conditionally-complete-lattice `sInf`, `Filter.Tendsto`).

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 3–7 days (define $g(r)$, prove squeeze + dichotomy)
- If hard: unknown (only if one attempts to actually close the gap)

## References

### Papers
- József Beck, "Irregularities of distribution I", *Acta Mathematica* **159** (1987), 1–49 —
  original solution establishing $\sqrt r \le g(r) \le \sqrt{r\log r}$ and posing the log gap.
- Klaus F. Roth, "On irregularities of distribution", *Mathematika* **1** (1954), 73–79 —
  founding lower-bound result for box discrepancy.
- Wolfgang M. Schmidt, "Irregularities of distribution VII", *Acta Arithmetica* **21** (1972),
  45–50 — sharp box-discrepancy lower bounds in higher dimensions.
- J. Ralph Alexander, "Geometric methods in the study of irregularities of distribution",
  *Combinatorica* **10** (1990), 115–136 — half-plane discrepancy $\gg r^{1/4}$.
- József Beck and William W. L. Chen, *Irregularities of Distribution*, Cambridge Univ. Press,
  1987 — comprehensive monograph with the $\sqrt{\log}$-gap discussion.

### Online Resources
- https://erdosproblems.com/989 — Erdős problem #989 entry, status and references.
- https://en.wikipedia.org/wiki/Discrepancy_theory — overview of geometric discrepancy and open gaps.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.sqrt`, real powers for the $\sqrt r$ / $\sqrt{r\log r}$ bounds.
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log`, its positivity and divergence at `atTop`.
- `Mathlib.Order.ConditionallyCompleteLattice.Basic` — `sInf`/`csInf_le`/`le_csInf` for defining $g(r) = \inf_A f_A(r)$.
- `Mathlib.Order.Filter.AtTopBot` / `Mathlib.Analysis.SpecialFunctions.Log.Deriv` — `Filter.Tendsto ... atTop` for $\sqrt{\log r} \to \infty$.
- `Mathlib.Analysis.InnerProductSpace.PiL2` — `EuclideanSpace ℝ (Fin 2)` points, as used in the parent file.

## Metadata

```yaml
tags:
  - discrepancy-theory
  - geometric-discrepancy
  - fourier-analysis
  - combinatorics
  - erdos
related_proofs:
  - erdos-989
  - erdos-988
  - erdos-990
  - fourier-series
difficulty: medium
source: proof-suggestion
created: 2026-07-09T15:23:00-07:00
```
