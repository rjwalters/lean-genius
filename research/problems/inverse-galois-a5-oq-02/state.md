# Research State: inverse-galois-a5-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
Certificate and pinning strategy for `Gal(x^7-7x+3 / ℚ) = PSL(2,7)` established and
machine-verified. Ready for a staged ACT (steps 1–3 in Lean, steps 4–5 axiomatized).

## Active Approach
Trinks' polynomial `f = x⁷ − 7x + 3` via the 5-step certificate (see knowledge.md):
1. irreducible mod 2 ⟹ transitive ⟹ 7 ∣ |G|
2. disc = 3⁸·7⁸ = 194481² ⟹ G ⊆ A₇
3. Frobenius cycle types {(7),(1,2,4),(1,3,3),(1,1,1,2,2)} ⟹ 84 = 4·3·7 ∣ |G|
4. degree-15 PSL(2,7)-resolvent has rational root ⟹ G ≤ PSL(2,7)
5. PSL(2,7) simple ⟹ no index-2 subgroup ⟹ |G| = 168 ⟹ G = PSL(2,7)

## Attempt Count
- Total attempts: 1 (ORIENT)
- Approaches tried: 1 (Trinks + Dedekind/resolvent/simplicity)

## Blockers
None fundamental. The Lean ACT is large: steps 4 (deg-15 resolvent) and 5
(PSL(2,7) simplicity) are the heavy parts and are candidates for axiomatization in
a first staged `axiomatized` entry.

## Next Action
ACT stage 1: transcribe steps 1–3 into a Lean file mirroring `InverseGaloisA5.lean`
(irreducibility mod 2 by `decide`; `disc = 194481²` by `norm_num`; cycle-type
divisibility per-prime), axiomatizing steps 4–5.

## Durable Artifacts
- `verify_trinks_psl27.py` — exact certificate, ALL CHECKS PASSED.
- `knowledge.md` — full ORIENT writeup + Mathlib bearer map.
