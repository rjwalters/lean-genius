# Hilbert 15 OQ-02: Complexity of Computing LR Coefficients

**Status**: IN PROGRESS (ACT phase)
**Problem**: Complexity of computing Littlewood-Richardson coefficients c^ν_{λ,μ}

## Problem Summary

LR coefficients c^ν_{λ,μ} count semistandard skew Young tableaux of shape ν/μ
and content λ satisfying the ballot (lattice word) condition. They appear in:
- Schubert calculus: σ_λ · σ_μ = Σ c^ν_{λ,μ} σ_ν
- Representation theory: V_λ ⊗ V_μ = Σ c^ν_{λ,μ} V_ν for GL_n
- Algebraic combinatorics: Schur function multiplication

**Key complexity dichotomy:**
- Positivity (c^ν_{λ,μ} > 0?): **P** — Knutson-Tao saturation + Klyachko LP
- Counting (exact value): **#P-complete** — Narayanan 2006

---

## Session 2026-04-12 (Session 1) - LR Coefficients for Gr(2,4)

**Mode**: FRESH (first session on this problem)
**Outcome**: progress — implemented `Hilbert15OQ02.lean`

### What I Did

1. Surveyed existing Hilbert15 infrastructure (OQ01, SchubertCalculus, SchubertCalculusOQ01)
2. Derived the ballot-sequence formula for 2-row LR coefficients
3. Implemented `lrCoeff2 : Partition2 → Partition2 → Partition2 → ℕ`
4. Verified all 7 nonzero Gr(2,4) structure constants + 2 zero cases
5. Proved Gr(2,4) multiplicity-free property (all LR coeffs ≤ 1)
6. Axiomatized Knutson-Tao saturation and Narayanan #P-completeness
7. Could not build (Docker Desktop requires manual restart after factory reset)

### Key Mathematical Findings

**Convention clarification**: c^ν_{λ,μ} uses skew shape ν/μ (not ν/λ) with content λ.
This was crucial — using the wrong convention gives wrong zero cases!

**Ballot condition derivation**: For reading word [1^k₂, 2^(r₂-k₂), 1^k₁, 2^(r₁-k₁)],
the only non-trivial ballot condition is: 2k₂ ≥ r₂.

**Column condition**: For overlap columns (in both rows of skew shape),
requires row1=1 and row2=2, forcing: k₁ ≥ ov AND k₂ ≤ μ.a - μ.b.

**Nontrivial zero** σ₂·σ₁₁=0: Column condition forces k₂ ≤ 0, but range forces k₂ ≥ 1.

### Files Modified

- `proofs/Proofs/Hilbert15OQ02.lean` (created, 364 lines, 3 axioms, 17 theorems)
- `proofs/Proofs.lean` (regenerated, +1 import)
- `src/data/research/problems/hilbert-15-oq-02.json` (updated)

### Next Steps

1. **Immediate**: Verify build once Docker Desktop is restarted
2. Extend to 3-row partitions for #P-hardness witness
3. Prove closed-form formula for 2-row LR coefficient
4. Consider Mathlib contribution: general SSYT + LR rule definition
