# Current State

**Phase**: BLOCKED
**Since**: 2026-06-28
**Iteration**: 1

## Current Focus

Eliminate `three_dvd_gal_card : 3 ∣ Fintype.card q.Gal` in InverseGaloisA5.lean
via Dedekind's theorem at p = 7.

## Active Approach

None viable in-session. The 3 ∣ |Gal| fact requires either Dedekind's theorem
(mod-7 factorization → 3-cycle) or Dummit's resolvent correspondence; both are
absent from Mathlib and there is no computational/axiom-free shortcut.

## Blockers

Dedekind's theorem (factorization type mod p = cycle type of Frobenius in Gal)
is absent from Mathlib 4.26.0; no Frobenius-as-Galois-permutation primitive.
Estimated 800–1500 lines of foundational number theory to build. See
`knowledge.md` for the concrete Mathlib bridge plan (KummerDedekind +
RamificationInertia/Galois + galActionHom + cycleType).

## Next Action

Park until Mathlib gains Dedekind's theorem, or commit a dedicated multi-session
bridge effort.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (assess-and-document)
