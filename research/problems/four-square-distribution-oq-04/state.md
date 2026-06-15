# Research State: four-square-distribution-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T03:35:20-07:00
**Iteration**: 6

## Current Focus
The whole open question now reduces (via Decomp.lean) to ONE lemma:
`fiber_card_eq_contribution` — each shape-fiber has size (★) = m!/∏count!·2^#nonzero.
This is the product of (a) the sign-count 2^#nonzero (Sign.lean, proved) and
(b) the arrangement-count m!/∏count! (the residue `arrangement_card`, in flight
PR #24518). This session encoded the previously-missing **assembly** wiring (a)
and (b) into the keystone (Keystone.lean), leaving only the single residue.

## Active Approach
Build-free ACT (Docker + Aristotle both down). New file
`FourSquareDistributionOQ04Keystone.lean` (0 sorry / 0 axiom) proves, modulo the
named arrangement-count residue, the Decomp keystone:
- `absFiber_eq_signFiber` (step 1): abs-map fiber = signFiber, UNCONDITIONAL.
- `nonzero_card_eq`: #nonzero(g) = #nonzero(s) via `Multiset.countP_map`.
- `shapeFiber_card_eq_arrangements_mul` (step 3): fiber = #profiles·2^#nonzero,
  UNCONDITIONAL, via `Finset.card_eq_sum_card_fiberwise`.
- `fiber_card_eq_contribution`: keystone, conditional on `harr` (= #24518's
  arrangement_card_div_form).
Certified end-to-end by `verify_keystone_assembly.py` (62 fibers, 441 sign-fibers,
m≤5/n≤12, all PASS).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Lean ACT is Docker-gated (no build this session).
- B_{2k} (signed permutations) has no Mathlib name — must be assembled from
  `Equiv.Perm (Fin 2k)` + sign flips.

## Next Action
The SOLE remaining residue is `arrangement_card` (PR #24518): the number of
arrangements of a size-m multiset = `Nat.multinomial`. Proof route: the
`Equiv.Perm (Fin m)` precomposition action — orbit of an arrangement = all
arrangements; stabilizer {σ | g∘σ = g} ≅ ∏_v Perm(g⁻¹{v}) of order ∏count!; then
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. Once that lands AND a
build session is available, register Decomp/Sign/Keystone in Proofs.lean and
discharge `harr` to make `fiber_card_eq_contribution` (Decomp) unconditional.
