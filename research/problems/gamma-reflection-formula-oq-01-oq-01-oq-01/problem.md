# Problem: Symmetric Beta Value B(s,1−s) = π / sin(πs)

**Slug**: gamma-reflection-formula-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall s\in(0,1):\quad B(s,1-s)=\frac{\Gamma(s)\,\Gamma(1-s)}{\Gamma(1)}=\Gamma(s)\,\Gamma(1-s)=\frac{\pi}{\sin(\pi s)}.
$$

### Plain Language

The Beta function satisfies B(x,y) = Γ(x)Γ(y)/Γ(x+y). Specializing to y = 1−x gives B(s,1−s) = Γ(s)Γ(1−s)/Γ(1) = Γ(s)Γ(1−s). Euler's reflection formula then evaluates this product as π/sin(πs). The goal is to combine Mathlib's Beta–Gamma relation with the reflection formula (already in the gallery / Mathlib) to obtain the closed form B(s,1−s) = π/sin(πs) for 0 < s < 1 as a named theorem.

### Why This Matters

- B(s,1−s)=π/sin(πs) is the normalizing constant of the arcsine / Beta(s,1−s) distribution and appears throughout analytic number theory and probability.
- It is the cleanest non-trivial special value of the Beta function and a natural showcase of how the Beta–Gamma bridge + reflection compose.
- Mathlib has Complex.Gamma_mul_Gamma_one_sub (reflection) and the Beta–Gamma relation, so this is an assembly of existing results rather than new analysis.

## Known Results

### What's Already Proven

- Parent gamma-reflection-formula-oq-01-oq-01 (verified, 0-axiom): Euler's reflection Γ(s)Γ(1−s)=π/sin(πs).
- Mathlib: Complex.Gamma_mul_Gamma_one_sub / Real.Gamma_mul_Gamma_one_sub (reflection formula).
- Mathlib: the Beta function and its relation to Gamma (Mathlib.Analysis.SpecialFunctions.Gamma.Beta), Real.Gamma_one = 1.

### What's Still Open

- Q1: State and prove betaIntegral / Beta value B(s,1−s) = Γ(s)Γ(1−s) by the Beta–Gamma relation at x=s, y=1−s (using Γ(1)=1).
- Q2: Compose with the reflection formula to conclude B(s,1−s)=π/sin(πs) for 0<s<1 (real form), and the complex analogue off the poles.
- Q3 (stretch): specialize at s=1/2 to recover B(1/2,1/2)=π and the central-Beta / Wallis connection.

### Our Goal

Prove B(s,1−s)=π/sin(πs) for s∈(0,1) by composing Mathlib's Beta–Gamma relation with Euler's reflection formula, as a verified/0-axiom named theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| gamma-reflection-formula-oq-01-oq-01 | parent open question | source of this extension |
| gamma-reflection-formula | ancestor in the same family | shared definitions and lemmas |
| gamma-reflection-formula-oq-01 | ancestor in the same family | shared definitions and lemmas |

## Initial Thoughts

### Potential Approaches

1. **Real Beta–Gamma + reflection**: Use Real.Gamma_mul_Gamma_one_sub and the Beta–Gamma identity B(x,y)=Γ(x)Γ(y)/Γ(x+y) with x+y=1, Γ(1)=1.
   - Risk: Confirming the exact Mathlib name and hypotheses (positivity 0<s<1) for the real Beta–Gamma relation; Mathlib's Beta is primarily developed in the complex/integral setting.
2. **Complex Beta then restrict**: Work with Complex.betaIntegral and Complex.Gamma_mul_Gamma_one_sub, then descend to reals via casting on (0,1).
   - Risk: Managing the domain/pole conditions and the real-vs-complex cast.

### Key Difficulties

- Locating Mathlib's exact Beta–Gamma lemma name and its hypotheses at v4.26.
- Domain bookkeeping: reflection has poles at integers; restrict to 0<s<1.

### What Would a Proof Need?

- Beta–Gamma relation B(x,y)=Γ(x)Γ(y)/Γ(x+y).
- Euler reflection Γ(s)Γ(1−s)=π/sin(πs).
- Γ(1)=1 and sin(πs)≠0 on (0,1).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Both load-bearing facts (Beta–Gamma, reflection) already exist; the contribution is a short composition.
- Sibling gamma-reflection entries are verified/0-axiom, confirming the analytic infrastructure is usable.
- Risk concentrated in API name discovery, not mathematical depth.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- E. Artin, The Gamma Function (1931/1964) — Beta–Gamma relation and reflection.
- Whittaker & Watson, A Course of Modern Analysis (1927) §12 — Beta and Gamma.

### Online Resources
- https://en.wikipedia.org/wiki/Beta_function
- https://en.wikipedia.org/wiki/Reflection_formula

### Mathlib
- Mathlib.Analysis.SpecialFunctions.Gamma.Beta — betaIntegral, Beta–Gamma relation
- Mathlib.Analysis.SpecialFunctions.Gamma.Basic — Complex/Real.Gamma_mul_Gamma_one_sub
- Mathlib.Analysis.SpecialFunctions.Trigonometric — sin(πs) nonvanishing on (0,1)

## Metadata

```yaml
tags:
  - seeker-selected
  - analysis
  - special-functions
  - gamma-function
  - beta-function
  - reflection-formula
  - arcsine-distribution
related_proofs:
  - gamma-reflection-formula
  - gamma-reflection-formula-oq-01
  - gamma-reflection-formula-oq-01-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-06-24
```
