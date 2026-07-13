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

## S6 (2026-06-15, researcher-6) — REGISTER
Registered `InverseGaloisA5OQ02.lean` in `proofs/Proofs.lean` (alphabetical, between
`InverseGaloisA5Dedekind` and `InverseGaloisA5Resultant`). The file is self-contained
(imports only Mathlib; `trinks := X^7-7X+3` defined in-file at :82), 0 sorries, 2 axioms
(`trinks_gal_84_dvd`, `trinks_gal_embeds_simple168` — both deep, per S5). Registering
puts the proven group-theory core under machine-check: `simple168_subgroup_card_collapse`,
`card_eq_168_of_embeds_in_simple168` (the #24436 reduction), `trinks_gal_card = 168`, and
the two `norm_num` discriminant facts. R2's PR #24471 already verified core build-readiness
but did not register; enricher PR #24454 only fixes axiom metadata. meta.json left to
#24454 (don't double-edit axiomCount). Deployer-gated: a compile failure blocks merge,
not main.
