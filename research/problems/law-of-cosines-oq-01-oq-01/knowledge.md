# law-of-cosines-oq-01-oq-01: Dual Spherical Law of Cosines

**Status**: COMPLETE
**Problem**: Prove cos(C) = -cos(A)cos(B) + sin(A)sin(B)cos(c) for spherical triangles.

## Session 2026-05-06 (Session 1) — Complete

**Mode**: FRESH (recovered pre-existing proof file from main repo)
**Outcome**: completed

### What I Did

- Found `LawOfCosinesOQ01OQ01.lean` untracked in main repo (248 lines, 0 sorries, 0 axioms)
- Created gallery entry: `src/data/proofs/law-of-cosines-oq-01-oq-01/` (meta.json, annotations.json, index.ts)
- Updated `src/data/proofs/listings.json` with new entry
- Updated research JSON knowledge fields
- Submitted PR

### Key Findings

- **Proof structure**: The dual law reduces to the ring identity (r-pq)(1-r²) = Δ·r - (p-qr)(q-pr)
  where Δ = 1-p²-q²-r²+2pqr is the Gram determinant
- **Gram factors**: gram_factor_A/B/C prove each squared-sine product minus squared-cosine-numerator = Δ
  (ensures arccos inputs lie in [-1,1])
- **Two-layer proof**: algebraic form via field_simp+nlinarith, geometric form via cos_arccos/sin_arccos
- **Key Mathlib**: `Real.sin_arccos` gives sin(arccos(x)) = √(1-x²), completing the geometric form

### Files Modified

- `proofs/Proofs/LawOfCosinesOQ01OQ01.lean` (248 lines, new file)
- `src/data/proofs/law-of-cosines-oq-01-oq-01/meta.json` (new)
- `src/data/proofs/law-of-cosines-oq-01-oq-01/annotations.json` (new)
- `src/data/proofs/law-of-cosines-oq-01-oq-01/index.ts` (new)
- `src/data/proofs/listings.json` (entry added)
- `src/data/research/problems/law-of-cosines-oq-01-oq-01.json` (knowledge updated)

### Next Steps

- Consider follow-up: polar triangle derivation (oq-01)
- Consider follow-up: law of sines as corollary (oq-02)
