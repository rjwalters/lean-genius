# Problem: Complete Nonderogatory to Cyclic Vector: The General Case (All Fields)

**Slug**: cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01
**Created**: 2026-04-25
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall K \text{ field},\ \forall n \geq 1,\ \forall M \in M_n(K):\ \mu_M = \chi_M \Rightarrow \exists v \in K^n,\ \{v, Mv, \ldots, M^{n-1}v\}\ \text{spans}\ K^n
$$

```lean
theorem nonderogatory_has_cyclic_vector_any_field
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K)
    (hnd : IsNonderogatory M) :
    ∃ v : Fin n → K, IsCyclicVector M v
```

### Plain Language

A matrix M is **nonderogatory** if its minimal polynomial equals its characteristic polynomial. A vector v is **cyclic** for M if iterating M on v (i.e., v, Mv, M²v, …) spans the whole space.

The theorem: every nonderogatory matrix has a cyclic vector, over **any** field — including finite fields.

Previous formalizations proved this for infinite fields (union avoidance) and for |K| > n. This problem closes the general case using a module-theoretic argument that avoids all cardinality conditions.

### Why This Matters

1. Completes the cyclic vector trilogy in the gallery (infinite → |K| > n → all fields)
2. Demonstrates that the result is algebraic (module theory over PID K[X]), not combinatorial
3. Isolates a concrete Mathlib gap: PID module structure theorem for K[X]-modules
4. Natural Mathlib contribution target: the missing lemma `exists_cyclic_vector_module`

## Known Results

### What's Already Proven

- `CayleyHamiltonMinpolyOQ05OQ01` — nonderogatory ↔ cyclic vector for infinite fields
- `CayleyHamiltonMinpolyOQ05OQ01OQ01` — weakened to |K| > n
- All 22 supporting lemmas in `CayleyHamiltonMinpolyOQ05OQ01OQ04.lean` are sorry-free:
  - `aeval_conj`: conjugation commutes with polynomial evaluation
  - `IsCyclicVector` and `IsNonderogatory` preserved under matrix similarity
  - `krylov_independent_iff_cyclic`: Krylov span ↔ cyclic vector

### What's Still Open

- Main theorem `nonderogatory_has_cyclic_vector_any_field` — 1 sorry in WIP file
- `exists_cyclic_vector_module`: if M nonderogatory then ∃ v generating K^n as K[X]-module

### Our Goal

Fill the single sorry in `CayleyHamiltonMinpolyOQ05OQ01OQ04.lean` (268 lines, 22 theorems)
by proving `exists_cyclic_vector_module`, either via Mathlib's PID module structure or directly.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cayley-hamilton` | Base theorem (charpoly annihilates M) | Polynomial evaluation |
| `cayley-hamilton-minpoly` | Minimal polynomial reduction | Annihilator ideals |
| `cayley-hamilton-minpoly-oq-05` | Nonderogatory ↔ cyclic (original) | Union avoidance |
| `cayley-hamilton-minpoly-oq-05-oq-01` | Proof for infinite fields | Polynomial counting |
| `cayley-hamilton-minpoly-oq-05-oq-01-oq-04` | Parent WIP file | Module theory over K[X] |

## Initial Thoughts

### Potential Approaches

1. **Module structure theorem** (preferred): K^n with M-action is f.g. over PID K[X]; nonderogatory forces rank-1 (single cyclic summand); generator is the cyclic vector.
   - Why it might work: The module K[X]/(minpoly M) has rank 1, so its generator v satisfies ann(v) = (minpoly M), making v cyclic.
   - Risk: Mathlib's PID module structure results may not apply to this K[X]-module setup.

2. **Rational canonical form**: Nonderogatory → single companion matrix block → e₁ is cyclic.
   - Why it might work: Concrete, avoids module theory abstraction.
   - Risk: Rational canonical form may not be formalized in Mathlib for arbitrary fields.

3. **Direct annihilator argument**: For nonderogatory M, show ∃ v with ann(v) = (minpoly M) using dimension counting over K.
   - Why it might work: Reduces to linear algebra, avoids module theory.
   - Risk: May still need module theory in disguise.

### Key Difficulties

- PID structure theorem for K[X]-modules not directly available in Mathlib
- Rational canonical form not fully formalized in Mathlib (as of early 2026)
- Translating between Matrix algebra and module-theoretic language in Lean 4

### What Would a Proof Need?

- Key lemma: `exists_cyclic_vector_module` — module generator is a cyclic vector
- Mathlib search: `Module.Cyclic`, `Submodule.span_singleton_eq_top`, `Ideal.Quotient.mk_surjective`
- Technical: `Polynomial.aeval_apply` and `Module.smul` compatibility

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- 22 supporting lemmas already proved; only 1 sorry remains
- Proof strategy clearly laid out in the WIP file header comments
- Primary obstacle: finding/building the right Mathlib lemma for cyclic K[X]-modules

**Estimated Effort**:
- Exploration: 1-2 days (Mathlib search for PID structure / rational canonical form)
- If approach 1 works: 1-3 days of Lean formalization
- If approach 2 works: 3-5 days (companion matrix results may need proving)

## References

### Papers
- Hoffman & Kunze, *Linear Algebra*, Ch. 7 — Rational canonical form, cyclic decomposition

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly` — characteristic polynomial machinery
- `Mathlib.RingTheory.PrincipalIdealDomain` — PID module structure
- `Mathlib.LinearAlgebra.FreeModule.Basic` — free module rank results

## Metadata

```yaml
tags:
  - linear-algebra
  - abstract-algebra
  - minimal-polynomial
  - cyclic-vector
  - finite-fields
  - module-theory
  - wip
  - seeker-selected
related_proofs:
  - cayley-hamilton
  - cayley-hamilton-minpoly
  - cayley-hamilton-minpoly-oq-05
  - cayley-hamilton-minpoly-oq-05-oq-01
  - cayley-hamilton-minpoly-oq-05-oq-01-oq-04
difficulty: medium
source: gallery-gap
created: 2026-04-25
```
