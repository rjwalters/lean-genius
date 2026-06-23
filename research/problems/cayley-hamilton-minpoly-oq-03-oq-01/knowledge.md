# Knowledge Base: Krylov Method for the Generalized (Vector) Minimal Polynomial

## Problem Summary

**Question**: Can the Krylov method be formalized for the generalized minimal polynomial
(the minimal polynomial of a specific vector v under M, rather than of M itself)?

**Background**: OQ-03 formalizes the Krylov method for the minimal polynomial μ_M of
matrix M. OQ-03-OQ-01 asks to generalize to μ_{M,v} — the minimum-degree annihilating
polynomial for a specific starting vector.

**Status**: PARTIAL (1 sorry remaining — existence/minimality via PID theory)

---

## Session 2026-04-14 (Session 1) — Initial Formalization

**Mode**: FRESH (EMPTY knowledge tier)
**Outcome**: progress — 8 theorems proved, 1 sorry remaining

### What I Did

Created `CayleyHamiltonMinpolyOQ03OQ01.lean` as a standalone file (imports Mathlib,
not OQ-03 directly). Proved the key structural results for the vector annihilator:

**`vecAnnSet` (definition)**: The set {p | p(M)·v = 0} — the annihilator of v under M.

**Ideal axioms (3 theorems)**:
- `vecAnnSet_zero_mem`: 0 ∈ I_v
- `vecAnnSet_add_mem`: I_v closed under addition
- `vecAnnSet_mul_mem`: I_v closed under polynomial multiplication (it's an IDEAL)

**`minpoly_mem_vecAnnSet`**: μ_M ∈ I_v — the minimal polynomial of M annihilates v.
Proof: `minpoly.aeval K M` gives μ_M(M) = 0 as a matrix, so μ_M(M)·v = 0·v = 0.

**`vecAnnSet_ne_bot`**: ∃ p ≠ 0, p ∈ I_v. Witness: μ_M.

**`vec_ann_poly_of_deg_le_dim`**: ∃ p ≠ 0, natDegree p ≤ n, p(M)·v = 0.
Proof: μ_M is the witness; its degree ≤ n from Cayley-Hamilton (μ_M | charpoly, 
deg(charpoly) = n).

**`krylov_zero_combo_at_minpoly`**: Σᵢ μ_M.coeff i • M^i·v = 0.
Proof: from `aeval_mulVec_eq_krylov_sum` + `minpoly_mem_vecAnnSet`.

Also proved `aeval_mulVec_eq_krylov_sum` locally (standalone copy from OQ-03).

### Key Lean Techniques

- `minpoly.aeval K M` gives `aeval M (minpoly K M) = 0` (direct Mathlib lemma)
- `Matrix.zero_mulVec` converts `0·v = 0`
- `minpoly.ne_zero` + `Algebra.IsIntegral.isIntegral M` for minpoly ≠ 0
- `Polynomial.natDegree_le_natDegree` + `minpoly.dvd K M (aeval_self_charpoly M)` for degree bound
- `Matrix.natDegree_charpoly` gives natDegree(charpoly M) = n

### Key Mathematical Insights

1. **Annihilator is an ideal**: I_v is closed under polynomial multiplication because
   p(M)·v = 0 implies (q·p)(M)·v = q(M)·(p(M)·v) = q(M)·0 = 0. This crucial fact means
   I_v is a nonzero ideal in K[X] (a PID), guaranteeing a unique monic generator.

2. **μ_M ∈ I_v always**: This establishes that the vector minimal polynomial always
   divides the matrix minimal polynomial. The Krylov sequence for any v terminates
   in ≤ deg(μ_M) ≤ n steps.

3. **Degree bound from Cayley-Hamilton**: deg(μ_{M,v}) ≤ deg(μ_M) ≤ n. The first
   inequality uses minimality of μ_{M,v} (it divides μ_M). The second uses
   μ_M | charpoly_M and deg(charpoly_M) = n.

### Remaining Sorry (1)

- `vec_minpoly_exists`: Full existence theorem — monic generator of minimal degree in I_v,
  with divisibility and minimality properties. Requires K[X] PID ideal generation via
  Mathlib's `IsPrincipalIdealRing` or `Submodule.IsPrincipal`. Estimated ~100 lines.

### Files Created

- `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ01.lean` (~200 lines, 8 theorems, 1 sorry)
- `proofs/Proofs.lean` (import added)
- `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-01/meta.json` (gallery entry)
- `research/problems/cayley-hamilton-minpoly-oq-03-oq-01/knowledge.md` (this file)

### Next Steps

- Prove `vec_minpoly_exists` using `IsPrincipalIdealRing.generator` from Mathlib:
  construct the ideal `I_v` formally as `Ideal K[X]`, use `generator` to get the
  monic polynomial, prove minimality and divisibility from ideal membership.
- Submit to Aristotle if the PID extraction proves too technical.
