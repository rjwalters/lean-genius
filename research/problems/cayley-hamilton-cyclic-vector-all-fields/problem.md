# Problem: Cyclic Vector Existence for Nonderogatory Matrices — RCF Approach

**Slug**: cayley-hamilton-cyclic-vector-all-fields
**Created**: 2026-04-25
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For any field } K \text{ and nonderogatory } M \in M_n(K),\ \exists\, v \in K^n \text{ cyclic for } M.
$$

```lean
theorem nonderogatory_has_cyclic_vector
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v : Fin n → K, IsCyclicVector M v

def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly
```

### Plain Language

A matrix M is **nonderogatory** when its minimal polynomial equals its characteristic
polynomial (both degree n). A **cyclic vector** v gives a basis {v, Mv, ..., M^{n-1}v}.

The theorem: every nonderogatory matrix has a cyclic vector, over ANY field.

### Why This Matters

This completes the cyclic vector story in the gallery:
- Cyclic → nonderog: **proven** (OQ-05-OQ-01, 0 sorries)
- Nonderog → cyclic over infinite fields: **proven** (OQ-05-OQ-01)
- Nonderog → cyclic with |K| > n: **proven** (OQ-05-OQ-01-OQ-01)
- Nonderog → cyclic over ALL fields: **this problem**

Over F_2 with n=3, union avoidance fails (F_2^3 has 8 vectors but ≤7 subspaces
to avoid). A structurally different proof is needed.

## Context: The Existing WIP

`CayleyHamiltonMinpolyOQ05OQ01OQ04.lean` tries the module-theory route:
K^n as K[X]-module, cyclic decomposition via PID structure theorem.
**Blocker**: PID structure theorem not in Mathlib 4.x.

## Our Approach: RCF Similarity

Key lemma to prove:

> M nonderogatory ↔ M is similar to its companion matrix C(charpoly(M)).

**Why this closes the proof** (all three steps are already proven):
1. `companionMatrix_orbit`: `C(p)^k · e₀ = eₖ` for k < deg(p) → e₀ is cyclic for C(p)
2. `aeval_conj`: conjugation commutes with polynomial evaluation
3. Conjugation preserves cyclic vectors (consequence of `aeval_conj`)

So M ~ C(charpoly(M)) implies P⁻¹e₀ is cyclic for M.

## Known Results

### Already Proven (in this gallery)

- `cyclic_implies_nonderogatory` — `CayleyHamiltonMinpolyOQ05OQ01.lean`
- `cyclic_iff_ann_eq_minpoly` — annihilator characterization
- `companionMatrix_minpoly` — `minpoly(C(p)) = p`
- `companionMatrix_charpoly` — `charpoly(C(p)) = p`
- `companionMatrix_orbit` — e₀ is cyclic for C(p) (from `CayleyHamiltonReductionOQ02OQ01.lean`)
- `aeval_conj` — conjugation commutes with `aeval`

### What's Still Open

1. `nonderogatory_similar_companion`: M nonderog → M ~ C(charpoly(M)) over any K
2. Whether a Smith-NF-free proof exists for single companion block

## Proof Strategies

### Route A: Search Mathlib First

Does Mathlib have `Matrix.IsCompanion`, `Matrix.similar_companion_of_nonderogatory`,
or `Matrix.RationalCanonicalForm`? Search:
```lean
#check Matrix.IsCompanion
-- Mathlib.LinearAlgebra.Matrix.Charpoly.*, Mathlib.RingTheory.MatrixAlgebra
```

### Route B: Axiomatize with 1 Sorry (Recommended)

Create `CayleyHamiltonCyclicVectorAllFields.lean`:
- Axiom: `nonderogatory_similar_companion` (the similarity theorem)
- Prove: `nonderogatory_has_cyclic_vector` from orbit lemma + conjugation
- Submit the axiom to Aristotle

This gives a clean proof with 1 focused sorry, clearly isolating the gap.

### Route C: Direct Krylov (Hard)

Show det[v | Mv | ... | M^{n-1}v] ≠ 0 for some v when M is nonderogatory.
Requires showing the determinant polynomial doesn't vanish identically — needs
same structural argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cayley-hamilton-minpoly-oq-05-oq-01` | Proves cyclic→nonderog; ∞-field case | Union avoidance, minpoly degree |
| `cayley-hamilton-minpoly-oq-05-oq-01-oq-01` | Weakens to \|K\| > n | Cardinality |
| `cayley-hamilton-minpoly-oq-05-oq-01-oq-04` | PID module approach (1 sorry) | K[X]-module theory |
| `cayley-hamilton-reduction-oq-02-oq-01` | Companion matrix: orbit, minpoly, charpoly | Orbit lemma |
| `cayley-hamilton-minpoly-oq-04` | Nonderog characterization | cyclic_iff_ann_eq_minpoly |

## Tractability Assessment

**Difficulty**: Medium (Mathlib has it) to Hard (full Smith NF proof)

- If Mathlib has the similarity theorem: 2-5 days
- Route B (1 sorry): 1-2 days
- Full proof from scratch: 3-6 weeks

**Recommended first step**: Search Mathlib. Then Route B if not found.

## References

### Papers
- Horn & Johnson, "Matrix Analysis" §3.3 — rational canonical form
- Hoffman & Kunze, "Linear Algebra" §7.2 — cyclic decomposition

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`

## Metadata

```yaml
tags:
  - linear-algebra
  - cayley-hamilton
  - cyclic-vector
  - rational-canonical-form
  - all-fields
  - minimal-polynomial
related_proofs:
  - cayley-hamilton-minpoly-oq-05-oq-01
  - cayley-hamilton-minpoly-oq-05-oq-01-oq-04
  - cayley-hamilton-reduction-oq-02-oq-01
difficulty: medium-hard
source: gallery-gap
created: 2026-04-25
```
