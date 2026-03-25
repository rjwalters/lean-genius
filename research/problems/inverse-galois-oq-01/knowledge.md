# Inverse Galois Problem: Non-Solvable Frontier (OQ-01)

**Problem**: Does every finite group appear as a Galois group over Q?

**Status**: IN-PROGRESS (structural analysis complete, more group realizations needed)

## Summary

The Inverse Galois Problem (IGP) asks whether every finite group is isomorphic to the Galois group of some Galois extension of Q. This is one of the most important open problems in algebra.

**Key insight**: The problem divides into solvable and non-solvable realms:
- Solvable groups: All realizable by Shafarevich's theorem (axiomatized)
- Non-solvable groups: Require explicit polynomial constructions (A5, S5 done)

## Session 2026-03-24 (Session 1) - Solvability Frontier

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Created `InverseGaloisOQ01.lean` (448 lines, 31 theorems, 0 axioms)
- Proved the complete solvability characterization: Sn is solvable iff n <= 4
- Proved A5 is simple (from Mathlib), not solvable, and perfect ([A5,A5] = A5)
- Proved Galois correspondence degree formulas: [K:K^H] = |H| and [K^H:F] = [G:H]
- Proved Cayley's embedding theorem
- Stated the full Inverse Galois Conjecture formally
- Created gallery entry with metadata

### Key Findings
- The solvability divide at n=5 is the fundamental boundary
- A5 perfection is the core obstruction: the derived series stalls at A5
- The sign homomorphism gives the exact sequence 1 -> An -> Sn -> C2 -> 1
- Galois correspondence provides automatic quotient realizability
- Every quotient of a realized group is realized (via fixed fields)

### Mathlib Gaps
- No `MulAction.toPermHom_injective` (proved manually)
- `IsSimpleGroup` API uses `eq_bot_or_eq_top_of_normal` not `eq_bot_or_eq_top`

### Files Modified
- `proofs/Proofs/InverseGaloisOQ01.lean` (new, 448 lines)
- `src/data/proofs/inverse-galois-oq-01/` (new gallery entry)
- `src/data/research/problems/inverse-galois-oq-01.json` (updated knowledge)

### Next Steps
- Realize PSL(2,7) as Galois group over Q (order 168, second-smallest simple group)
- Realize A6 (order 360) via explicit polynomial
- Prove quotient realizability formally using Mathlib compositum machinery
- Connect S5 realization to the census (import AbelRuffiniOQ04OQ01)
