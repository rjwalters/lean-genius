# cevas-theorem-oq-01-oq-03 — Routh's Theorem for General Parameters

**Problem**: Complete Routh's theorem formula for general cevian parameters (not just 1/3).

**Status**: COMPLETED — 14 theorems, 0 sorries, 0 axioms, PR #15173

---

## Session 2026-05-03 (Session 1) — researcher-10

**Mode**: FRESH
**Outcome**: completed — 14 theorems proved, gallery entry created, PR #15173 filed

### What I Did

- Claimed problem from pool (EMPTY knowledge, tractability 5)
- Computed explicit intersection formulas for P=AD∩BE, Q=BE∩CF, R=CF∩AD
  - P = ((1-d)(1-e)/w₁, d(1-e)/w₁), w₁ = 1-e+de
  - Q = (ef/w₂, (1-e)(1-f)/w₂), w₂ = 1-f+ef
  - R = (f(1-d)/w₃, fd/w₃), w₃ = 1-d+fd
- Proved all 6 cevian membership lemmas (field_simp + ring)
- Proved main theorem: signedArea(P,Q,R) = routhRatio(d,e,f) × signedArea(A,B,C)
  - After field_simp [hw1, hw2, hw3], reduces to degree-6 polynomial identity proved by ring
- Proved corollaries: explicit area form, 1/7 case, concurrent degeneration (area=0), nonnegativity
- Created gallery entry: meta.json, annotations.json, index.ts
- Created PR #15173

### Key Findings

- **Intersection formulas**: The key is solving 2D linear systems. For P=AD∩BE: set
  t(1-d, d) = (1,0) + s(-1, 1-e), get t = (1-e)/(1-e+de) = (1-e)/w₁.
- **Polynomial identity**: After field_simp clears all rational denominators, the area
  formula reduces to a polynomial identity that `ring` verifies automatically.
- **Denominator positivity**: w₁,w₂,w₃ > 0 for d,e,f ∈ (0,1) — proved by nlinarith.
- **Zero condition**: routhRatio = 0 ↔ Ceva condition (def = (1-d)(1-e)(1-f)).
- **Example**: d=e=f=1/3 gives 1/7; d=1/2, e=1/3, f=1/4 gives 1/10.

### Files Modified

- `proofs/Proofs/CevasTheoremOQ01OQ03.lean` (created, ~200 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/cevas-theorem-oq-01-oq-03/meta.json`
- `src/data/proofs/cevas-theorem-oq-01-oq-03/annotations.json`
- `src/data/proofs/cevas-theorem-oq-01-oq-03/index.ts`
- `src/data/research/problems/cevas-theorem-oq-01-oq-03.json` (pool updated)

### Next Steps

(None — proof is complete)
