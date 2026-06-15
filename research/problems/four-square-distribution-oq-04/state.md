# Research State: four-square-distribution-oq-04

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
Generalization of the four-square type-decomposition to r_{2k}(n) under the
hyperoctahedral group B_{2k} = S_{2k} ⋉ (Z/2)^{2k} CONFIRMED: orbit size
2^{#nonzero}·(2k)!/∏m_i!, stabilizer 2^z·z!·∏(nonzero m_j!), and
r_{2k}(n) = Σ_shapes orbit. Verified exactly for 2k ∈ {2,4,6,8}; Mathlib
orbit–stabilizer bearer pinned.

## Active Approach
Build-free ORIENT (Docker + Aristotle both down this session). Durable exact
verifier `verify_hyperoctahedral_2k.py` (all checks pass).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Lean ACT is Docker-gated (no build this session).
- B_{2k} (signed permutations) has no Mathlib name — must be assembled from
  `Equiv.Perm (Fin 2k)` + sign flips.

## Next Action
ACT (next Docker session): for fixed m = 2k ∈ {4,6,8}, define the B_m MulAction on
`{f : Fin m → ℤ // Σ f² = n}`, compute the stabilizer order (zero/nonzero split),
and apply `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` for the
orbit-size formula. The real obstruction is the orbit PARTITION
(r_{2k} = Σ orbit), not the orbit-size formula.
