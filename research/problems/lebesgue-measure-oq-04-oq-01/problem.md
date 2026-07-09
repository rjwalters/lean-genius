# Problem: Formalize the Cantor Function (Devil's Staircase)

**Slug**: lebesgue-measure-oq-04-oq-01
**Created**: 2026-07-09T16:43:21-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, F : [0,1] \to [0,1] \text{ continuous, monotone, surjective, with } F' = 0 \text{ Lebesgue-a.e., yet } F(1) - F(0) = 1.
$$

Concretely, define $F$ on $x = \sum_{n\ge 1} a_n 3^{-n}$ (ternary digits $a_n \in \{0,1,2\}$) by: if some digit equals $1$, truncate at the first such position and set that digit to $1$; otherwise halve each digit. Then $F(x) = \sum_{n} b_n 2^{-n}$ with $b_n = a_n / 2$ before truncation. The map $F$ is well-defined, continuous, non-decreasing, surjective onto $[0,1]$, constant on every open middle-third interval removed in the Cantor construction, and $F'(x) = 0$ for almost every $x \in [0,1]$.

### Plain Language

The Cantor function, nicknamed the "devil's staircase," is a continuous function that climbs from $0$ to $1$ across the interval $[0,1]$ while being flat almost everywhere. It is constant on each of the open intervals deleted when building the Cantor set (the middle thirds), so all of its rise happens on the Cantor set itself — a set of Lebesgue measure zero. The paradox is that a function can be continuous and increasing yet have zero derivative almost everywhere and still manage to increase by a full unit: the rise is "smuggled" through a null set. This is the canonical example of a singular continuous function, and it is currently absent from Mathlib.

### Why This Matters

The Cantor function is the standard counterexample separating monotone continuity from absolute continuity: it shows that the fundamental theorem of calculus $F(1) - F(0) = \int_0^1 F'\,dx$ can fail when $F$ is merely continuous and monotone rather than absolutely continuous, because here $\int_0^1 F'\,dx = 0 \neq 1$. It is the concrete witness of a nonzero singular measure (the Cantor–Lebesgue measure $dF$) supported on a null set, and it seeds the theory of singular distributions, self-affine functions, and multifractal analysis. Formalizing it completes the gallery's Cantor-set story: the parent proof establishes the set is an uncountable null set; this entry builds the function whose entire variation lives on that null set.

## Known Results

### What's Already Proven

- The ternary Cantor set is Lebesgue-null and uncountable — `lebesgue-measure-oq-04` (`cantorSet_null_and_uncountable`, this gallery), built on Mathlib's `cantorSet`.
- Mathlib's Cantor-set infrastructure: `Topology.Instances.CantorSet` provides `preCantorSet`, `cantorSet`, its closedness/compactness, the ternary description, and the bijection `cantorSetEquivNatToBool : cantorSet ≃ (ℕ → Bool)`.
- General measure/derivative tooling: `MeasureTheory.Measure.StieltjesFunction` (monotone right-continuous functions induce measures), and a.e.-differentiability of monotone functions (`Monotone.ae_differentiableAt` in `Mathlib.Analysis.Calculus.Monotone`).

### What's Still Open

- No construction of the Cantor function `F : ℝ → ℝ` (or on `[0,1]`) exists in Mathlib or this gallery.
- No formal proof that such an `F` is continuous, monotone, and surjective onto `[0,1]`.
- No formal proof that `F' = 0` Lebesgue-almost-everywhere, nor the associated singularity statement `∫₀¹ F' = 0 < 1 = F(1) - F(0)`.

### Our Goal

Construct `F` and prove its four defining properties (continuity, monotonicity, surjectivity onto `[0,1]`, and constancy on each removed middle-third interval), then establish `F' = 0` Lebesgue-a.e. A staged goal: first nail the construction plus continuity/monotonicity/surjectivity, then add the a.e.-derivative-zero result, which is the deepest piece.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lebesgue-measure-oq-04 | Parent: proves the Cantor set is an uncountable null set; the Cantor function's entire rise is carried on exactly this null set | Haar-measure homothety scaling, `(2/3)^n` induction bound, squeeze; `cantorSetEquivNatToBool` cardinality transfer |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Uniform limit of piecewise-linear staircases**: Define $F_n$ as the piecewise-linear function that is constant with value $k/2^n$ on the $k$-th removed interval at stage $n$ and interpolates linearly on the pre-Cantor stage $C_n$. Show $(F_n)$ is uniformly Cauchy (each refinement moves values by at most $2^{-n}$), so $F = \lim F_n$ is continuous by the uniform-limit theorem. Monotonicity and the constant-on-removed-intervals property pass to the limit.
   - Why it might work: leverages Mathlib's uniform-convergence continuity theorems and avoids delicate ternary bookkeeping; each $F_n$ is manifestly monotone.
   - Risk: proving the uniform Cauchy bound and that $F$ is genuinely constant on each open removed interval (not just at endpoints) needs careful stage-indexing.

2. **Approach B — Ternary/binary digit map with a Stieltjes measure**: Define $F$ directly via the ternary-to-binary digit rewrite, or equivalently push Mathlib's uniform Bernoulli measure on `ℕ → Bool` forward through `cantorSetEquivNatToBool` to get the Cantor–Lebesgue measure $\mu$, then set $F(x) = \mu([0,x])$. Right-continuity + monotonicity of a CDF gives continuity (no atoms) and monotonicity for free via `StieltjesFunction`; $F' = 0$ a.e. follows because $\mu \perp$ Lebesgue (μ is supported on the null Cantor set).
   - Why it might work: reuses the parent proof's bijection and null-set result; `StieltjesFunction` machinery hands over monotonicity and the induced measure directly; singularity gives $F'=0$ a.e. from Lebesgue's differentiation/decomposition theorems.
   - Risk: the measure-pushforward and mutual-singularity plumbing may hit Mathlib gaps; connecting `StieltjesFunction.measure` derivative to the classical a.e. derivative of $F$ requires the Radon–Nikodym / Lebesgue-differentiation bridge.

### Key Difficulties

- Establishing $F' = 0$ Lebesgue-a.e.: this is the singular part and requires either Lebesgue's differentiation of monotone functions plus the fact that the "increase" is concentrated on a null set, or the Radon–Nikodym singular-part machinery.
- Well-definedness of the digit map at the countably many ternary-ambiguous points (numbers with two ternary expansions), and matching the two constructions at the endpoints of removed intervals.
- Surjectivity onto $[0,1]$: showing every binary expansion in $[0,1]$ is hit, which follows from continuity + $F(0)=0$, $F(1)=1$ + intermediate value, but must be assembled formally.

### What Would a Proof Need?

- Key lemma 1: a well-defined `F : ℝ → ℝ` (constructed as a uniform limit or via a Stieltjes/pushforward measure) with `F 0 = 0`, `F 1 = 1`.
- Key lemma 2: `Continuous F`, `Monotone F`, and constancy of `F` on each open removed middle-third interval `Ioo (removed endpoints)`.
- Key lemma 3: surjectivity `F '' Icc 0 1 = Icc 0 1` (via IVT `intermediate_value_Icc`).
- Key lemma 4 (deepest): `∀ᵐ x ∂volume, HasDerivAt F 0 x`, i.e. `F' = 0` a.e., yielding the singularity `∫₀¹ F' = 0 ≠ F 1 - F 0`.
- Technical requirements: `Monotone.ae_differentiableAt`, `MeasureTheory.Measure.StieltjesFunction`, uniform-convergence continuity, and the parent's `volume_cantorSet = 0`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The construction (continuity, monotonicity, surjectivity, constancy on removed intervals) is standard and matches Mathlib's available uniform-limit and IVT tooling — likely reachable.
- The a.e.-derivative-zero statement is harder and may require assembling Lebesgue-differentiation and singular-measure results; this is where a Mathlib gap could turn the full result into a longer effort.
- The parent proof `lebesgue-measure-oq-04` already provides the null-set fact and the `cantorSetEquivNatToBool` bijection that Approach B reuses, lowering the barrier.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 1–3 weeks (construction + continuity/monotone/surjective; a.e.-derivative as a follow-on)
- If hard: unknown (if the singular-derivative bridge is missing from Mathlib)

## References

### Papers
- Cantor, G., "Über unendliche, lineare Punktmannigfaltigkeiten V", 1883 — introduces the ternary set underlying the function's flat regions.
- Lebesgue, H., "Leçons sur l'intégration et la recherche des fonctions primitives", 1904 — the measure theory in which the Cantor function is the canonical singular function.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Instances/CantorSet.html — Mathlib's Cantor-set definitions and the `cantorSetEquivNatToBool` bijection.

### Mathlib
- `Mathlib.Topology.Instances.CantorSet` — `preCantorSet`, `cantorSet`, and the bijection with `ℕ → Bool` used to index the staircase.
- `Mathlib.MeasureTheory.Measure.StieltjesFunction` — monotone right-continuous functions and their induced (Cantor–Lebesgue) measures.
- `Mathlib.Analysis.Calculus.Monotone` — `Monotone.ae_differentiableAt`, a.e. differentiability of monotone functions, toward `F' = 0` a.e.
- `Mathlib.Topology.UniformSpace.UniformConvergence` — uniform-limit continuity for the piecewise-linear approximation approach.

## Metadata

```yaml
tags:
  - measure-theory
  - cantor-set
  - lebesgue-measure
  - null-set
  - uncountable
  - cardinality
  - research
related_proofs:
  - lebesgue-measure-oq-04
difficulty: medium
source: lebesgue-measure-oq-04
created: 2026-07-09T16:43:21-07:00
```
