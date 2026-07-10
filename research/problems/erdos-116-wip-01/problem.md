# Problem: Completing the Lean Formalization of Erdős #116 (Measure of Polynomial Sublevel Sets)

**Slug**: erdos-116-wip-01
**Created**: 2026-07-09T17:33:18-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall\, p \in \mathrm{UnitDiskPoly}_n,\qquad \frac{c}{\log n} \;\le\; \mu\bigl(\{\, z \in \mathbb{C} : |p(z)| < 1 \,\}\bigr) \;\le\; \pi,
$$

where $\mathrm{UnitDiskPoly}_n$ is the set of monic degree-$n$ polynomials $p(z) = \prod_{i=1}^{n}(z - z_i)$ with all roots $z_i$ in the closed unit disk $\overline{\mathbb{D}}$, $\mu$ is $2$-dimensional Lebesgue measure, and $c > 0$ is an absolute constant.

### Plain Language

We want to finish turning a partially-formalized Lean 4 proof about polynomial "small regions" into one that is machine-checked as far as possible. For a polynomial whose roots all lie inside the unit disk, look at the region where the polynomial has absolute value below $1$; the Krishnapur–Lundberg–Ramachandran theorem says this region always has area at least $c/\log n$, which resolved a 1958 question of Erdős, Herzog, and Piranian. The current gallery entry `erdos-116` states the main bounds as unproven assumptions and defines the objects but does not formally verify any nontrivial inequality. Our task is to discharge the pieces that are genuinely provable in Lean/Mathlib (the definitions, Pólya's upper bound $\pi$, and structural lemmas about the sublevel set) and to cleanly isolate the deep analytic core (the KLR lower bound) as a single stated assumption.

### Why This Matters

1. **Credibility of the gallery**: The `erdos-116` entry currently carries a `wip` badge because its central inequalities are assumed rather than proved; formalizing the tractable parts moves it toward an honest `verified` core with a clearly delimited assumption.
2. **Reusable complex-analysis scaffolding**: A clean Lean treatment of polynomial lemniscates and their Lebesgue measure produces definitions and lemmas (sublevel sets, root-product form, area monotonicity) that other gallery entries in complex analysis and measure theory can reuse.
3. **Sharp separation of open from closed**: Isolating exactly which inequality (the $c/\log n$ lower bound) is the hard KLR input clarifies for future researchers what remains genuinely open, namely the $1/\log n$ versus $1/\log\log n$ gap.

## Known Results

### What's Already Proven

- Pommerenke's polynomial lower bound $\mu(S_p) \ge c/n^4$ via logarithmic potential theory and transfinite diameter estimates — Pommerenke (1959–61).
- The optimal lower bound $\mu(S_p) \ge c/\log n$, resolving the Erdős–Herzog–Piranian conjecture — Krishnapur, Lundberg, Ramachandran (2021).
- The near-matching upper bound $\mu(S_p) \le C/\log\log n$ by explicit constructions — Krishnapur, Lundberg, Ramachandran (2021).
- Pólya's absolute upper bound $\mu(S_p) \le \pi$, with equality iff all roots coincide — Pólya (1928).

### What's Still Open

- The exact asymptotic minimum: whether $\min_p \mu(S_p)$ is $\Theta(1/\log n)$ or $\Theta(1/\log\log n)$ or something strictly between remains unresolved.
- Which root configurations are extremal for each degree $n$, and whether they relate to Fekete points or other classical configurations.
- Whether analogous bounds hold when roots are constrained to the unit circle $|z_i| = 1$ rather than the closed disk.

### Our Goal

Strengthen the Lean formalization `Proofs/Erdos116Problem.lean` so that (i) the `UnitDiskPoly` structure and the sublevel-set / sublevel-measure definitions are tightened and shown well-defined and measurable; (ii) Pólya's upper bound $\mu(S_p) \le \pi$ and basic monotonicity facts are formally proved from Mathlib rather than assumed; and (iii) the KLR lower bound $c/\log n$ is retained as a single named assumption with an explicit `assumptions` disclosure, so the entry's verified core is maximized and its remaining assumption is minimal and honest.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-116 | Direct parent entry; supplies the `UnitDiskPoly` structure, sublevel-set definitions, and the four bounds to be formalized | Root-product polynomials, Lebesgue measure on $\mathbb{C}$, potential theory |
| erdos-89 | Companion Erdős problem in the same complex/combinatorial-geometry cluster where sharp bounds are stated but the deep result stays axiomatized | Extremal estimates, geometric measure reasoning |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Formalize Pólya's $\pi$ upper bound and measurability first, treating KLR as a black-box assumption.
   - Why it might work: Pólya's bound follows from the isoperimetric/area properties of lemniscates and the fact that $S_p$ is contained in a disk of radius depending on the roots; measurability of $\{|p(z)|<1\}$ is immediate since $p$ is continuous, so the set is open.
   - Risk: The equality-case analysis (all roots coincident) may require careful handling of the polynomial's normal form and could exceed available Mathlib support for transfinite diameter.

2. **Approach B**: Refactor the definitions so the sublevel measure is expressed as an integral amenable to Mathlib's `MeasureTheory` API, then prove only the structural lemmas, leaving both KLR bounds as assumptions.
   - Why it might work: Reducing everything to a single measurable-set/integral formulation lets Mathlib discharge openness, measurability, and finiteness automatically, shrinking the surface that must be assumed.
   - Risk: Choosing the wrong encoding can make the KLR assumption awkward to state, or make the connection between the assumption and the main theorem statement non-obvious.

### Key Difficulties

- The KLR lower bound relies on probabilistic value-distribution estimates far beyond current Mathlib complex-analysis coverage, so it cannot be discharged and must be isolated cleanly.
- Reasoning about the 2D Lebesgue measure of a lemniscate requires connecting Mathlib's abstract measure theory to concrete complex-analytic geometry, which has limited existing lemma support.

### What Would a Proof Need?

- Key lemma 1: The sublevel set $\{z : |p(z)| < 1\}$ is open (hence measurable) and bounded for $p \in \mathrm{UnitDiskPoly}_n$.
- Key lemma 2: Pólya's inequality $\mu(S_p) \le \pi$ with the coincident-roots equality condition.
- Technical requirements: A robust `UnitDiskPoly` structure carrying roots and disk-membership proofs, plus a clean statement of the KLR lower bound as a single assumption disclosed in `meta.json`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The tractable sub-goals (measurability, boundedness, Pólya's $\pi$ bound) are achievable with Mathlib's measure theory, but the headline KLR lower bound is a deep 2021 research result with no path to full formalization.
- Similar gallery entries (e.g. erdos-89) succeed by formalizing definitions and easy bounds while axiomatizing the hard theorem; the same pattern applies here.
- Mathlib provides `MeasureTheory`, complex analysis basics, and `Real.log`, sufficient for the scaffolding but not for potential-theoretic estimates.

**Estimated Effort**:
- Exploration: 2–3 days to map Mathlib measure-theory support for lemniscates.
- If tractable: 1–2 weeks to formalize definitions, measurability, and Pólya's bound.
- If hard: the KLR lower bound remains an assumption indefinitely.

## References

### Papers
- Erdős, Herzog, Piranian, "Metric properties of polynomials", J. Analyse Math. (1958) — original conjecture on sublevel set measure.
- Krishnapur, Lundberg, Ramachandran, "Superlevel sets and nodal extrema of Laplace eigenfunctions" / related work on lemniscate area (2021) — establishes the $c/\log n$ lower bound.
- Pommerenke, "On metric properties of complex polynomials" (1959–61) — the $c/n^4$ bound.
- Pólya, "Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete" (1928) — the $\pi$ upper bound.

### Online Resources
- https://erdosproblems.com/116 — problem statement and status.

### Mathlib
- Mathlib.MeasureTheory.Measure.Lebesgue.Basic — 2D Lebesgue measure on $\mathbb{C} \cong \mathbb{R}^2$.
- Mathlib.Analysis.SpecialFunctions.Complex.Circle — complex modulus and circle machinery.
- Mathlib.Analysis.SpecialFunctions.Log.Basic — $\log n$ for the lower-bound statement.

## Metadata

```yaml
tags:
  - complex-analysis
  - measure-theory
  - polynomial-lemniscates
  - erdos-problems
  - potential-theory
  - formalization
related_proofs:
  - erdos-116
  - erdos-89
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:18-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
