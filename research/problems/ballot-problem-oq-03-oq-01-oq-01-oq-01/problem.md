# Problem: LGV Lemma → Jacobi-Trudi Identity (Schur Polynomials as Determinants)

**Slug**: ballot-problem-oq-03-oq-01-oq-01-oq-01
**Created**: 2026-04-23T12:58:12+02:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Apply the LGV lemma (formalized in `ballot-problem-oq-03-oq-01`) to prove the Jacobi-Trudi identity:

$$s_\lambda(x_1, \ldots, x_n) = \det\left[h_{\lambda_i - i + j}(x_1, \ldots, x_n)\right]_{1 \le i,j \le k}$$

where $s_\lambda$ is the Schur polynomial and $h_k$ is the complete homogeneous symmetric
polynomial of degree $k$.

```lean
-- Target formalization:
theorem jacobi_trudi_identity (λ : YoungDiagram) (n : ℕ) (x : Fin n → ℝ) :
    schurPolynomial λ n x =
    Matrix.det (fun i j => completeHomogeneous (λ.rowLengths i - i + j) n x) := by
  sorry
```

### Plain Language

The Jacobi-Trudi identity expresses Schur polynomials (basis for the ring of symmetric
functions, encoding irreducible representations of GL(n)) as determinants of complete
homogeneous symmetric polynomials. The LGV lemma provides a combinatorial proof via
non-intersecting lattice paths.

### Why This Matters

- **Gallery connection**: `ballot-problem-oq-03-oq-01` formalizes the LGV lemma. The
  Jacobi-Trudi proof uses this as a black box.
- **Mathlib gap**: Schur polynomials exist in Mathlib (`MvPolynomial.schurPolynomial`),
  but the Jacobi-Trudi identity likely lacks a formalized proof.
- **Algebraic combinatorics**: Foundational result connecting representation theory,
  symmetric functions, and combinatorics.

## Known Results

### What's Already Proven

- LGV lemma: `ballot-problem-oq-03-oq-01` — non-intersecting lattice path determinant formula
- Complete homogeneous symmetric polynomials: `Mathlib.RingTheory.MvPolynomial.Symmetric`
- Schur polynomials: `MvPolynomial.schurPolynomial` (recent Mathlib)

### What's Still Open

- The Jacobi-Trudi identity itself using the LGV infrastructure

### Our Goal

Prove the Jacobi-Trudi identity by connecting the LGV lattice path framework to Schur
polynomial theory.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ballot-problem-oq-03-oq-01 | LGV lemma (direct dependency) | Lattice paths, determinants |
| ballot-problem-oq-03-oq-01-oq-02 | LGV → Catalan/path applications | Path bijections |

## Initial Thoughts

### Potential Approaches

1. **Via Non-Intersecting Lattice Paths**
   - Define path systems for the Jacobi-Trudi determinant
   - Show NI-paths biject to SSYT of shape λ
   - Apply LGV from parent proof
   - Connect SSYT weight sum to Schur polynomial definition
   - Why it might work: Standard textbook proof path, LGV infrastructure exists
   - Risk: SSYT formalization may not exist in Mathlib

2. **Direct Algebraic Proof via Transfer Matrix**
   - Use LGV algebraic formulation on the transfer matrix directly
   - Risk: More abstract, harder to formalize

### Key Difficulties

- SSYT (semi-standard Young tableaux) may need to be defined from scratch
- Bridging Young diagram types between gallery and Mathlib

### What Would a Proof Need?

- Key lemma 1: SSYT biject to NI lattice paths (combinatorial bijection)
- Key lemma 2: Schur polynomial = weight sum over SSYT
- Technical: Young diagram / partition type, `Matrix.det` API

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- LGV infrastructure exists in gallery
- Mathlib has symmetric polynomial framework
- Main work: SSYT formalization + bijection proof

**Estimated Effort**:
- Exploration: 1-2 days (check Mathlib for SSYT, understand path bijection)
- If tractable: 1-2 weeks

## References

### Papers
- Lindström (1973), Gessel-Viennot (1985): original LGV papers
- Stanley, EC2, Chapter 7: Jacobi-Trudi and symmetric functions

### Mathlib
- `Mathlib.RingTheory.MvPolynomial.Symmetric` — symmetric polynomial infrastructure
- `MvPolynomial.schurPolynomial` — Schur polynomial definition

## Metadata

```yaml
tags:
  - algebraic-combinatorics
  - symmetric-polynomials
  - lgv-lemma
  - schur-polynomials
  - determinants
related_proofs:
  - ballot-problem-oq-03-oq-01
  - ballot-problem-oq-03-oq-01-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-23T12:58:12+02:00
```

**Significance**: 8/10
**Tractability**: 6/10
