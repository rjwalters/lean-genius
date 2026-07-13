# Problem: When exactly does the Hasse principle fail for higher-degree forms?

## Statement

### Plain Language

The Hasse-Minkowski theorem (formalized in `Hilbert11_QuadraticForms.lean` and refined in
`Hilbert11OQ01.lean`) shows that the Hasse principle (local-global principle) holds for
quadratic forms over ℚ: a quadratic form represents zero rationally iff it does so over ℝ
and over every ℚₚ.

For higher-degree forms (cubic and beyond) the principle FAILS in general. The Selmer
curve `3x³ + 4y³ + 5z³ = 0` (Selmer 1951) is the classical counterexample: it has
solutions over ℝ and every ℚₚ but no nontrivial rational solutions.

The OPEN question asks for an exact characterization of when the Hasse principle fails.

### Formal Statement

For a smooth proper geometrically rationally connected variety `X` over `ℚ`:

$$
X(\mathbb{Q}) \neq \emptyset \iff X(\mathbb{A}_\mathbb{Q})^{\mathrm{Br}(X)} \neq \emptyset
$$

i.e. the Brauer-Manin obstruction is the only obstruction to the Hasse principle.

This is the **Colliot-Thélène conjecture**. It is known for several families
(quadratic forms, conic bundles over ℙ¹, del Pezzo surfaces of degree ≥ 5, some
Châtelet surfaces) but open in general — including for cubic surfaces (del Pezzo
of degree 3) and K3 surfaces.

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - seeker-selected
  - number-theory
  - hasse-principle
  - cubic-forms
  - brauer-manin
```

**Significance**: 7/10 — A central question in arithmetic geometry, governing the
local-global behavior of varieties.

**Tractability**: 4/10 — The full conjecture is far beyond current Lean infrastructure.
Concrete sub-results (e.g., real solubility of the Selmer cubic) are tractable.

## Why This Matters

1. **Foundational arithmetic geometry** — The Hasse principle is the prototypical
   local-global principle. Understanding when it fails drives the theory of
   obstructions, descent, and Brauer-Manin / étale obstructions.
2. **Application to Diophantine equations** — A characterization tells us which
   polynomial systems can be solved by purely local computations.
3. **Interaction with class field theory and étale cohomology** — Modern proofs use
   class field theory, étale cohomology, Galois cohomology, and the arithmetic of
   torsors.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `hilbert-11` | Parent: Hasse-Minkowski for quadratic forms (the principle holds) |
| `hilbert-11-oq-01` | Sister: tensor-product formalization of local conditions |
| `quadratic-reciprocity` | Foundational: governs binary quadratic forms over ℚₚ |
| `lagrange-four-squares` | Special case: the form x²+y²+z²+w² represents all naturals |
