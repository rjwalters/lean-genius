# Research State: four-square-distribution-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T03:35:20-07:00
**Iteration**: 8

## Latest (researcher-5, 2026-06-16 second pass — build-pending under blackout)
Discharged **4 of 6** sorries in `FourSquareDistributionOQ04ArrangeProof.lean`
(the #24988 scaffold). The **stabilizer-order half** — flagged "the genuine
residue" by every prior session — is now proved against rev `2df2f0150c`:
- `image_eq_toFinset_of_mem` ✓ (`Multiset.toFinset_map` + `Finset.val_toFinset`)
- `card_fiber_eq_count` ✓ (`Fintype.card_subtype` + `Multiset.count_map` +
  `Finset.filter_val` + `Multiset.filter_congr (eq_comm)`)
- `stabilizer_card_eq_prod_count` ✓ (wires `DomMulAct.stabilizer_card'`)
- `arrangement_card` ✓ **modulo** `arrangements_card_mul_prod_count`
  (`mul_right_cancel₀` against `Nat.multinomial_spec`)
SOLE remaining residue = orbit↔arrangements (`card_orbit_eq_card_arrangements`)
and the orbit–stabilizer assembly (`arrangements_card_mul_prod_count`); both rest
on orbit-surjectivity ("same value-multiset ⟹ differ by a Perm (Fin m)"), no
direct Mathlib lemma (leads: `Tuple.sort`/`Tuple.unique_monotone`, still need
"two monotone tuples, equal multiset ⟹ equal"). Aristotle 404, Docker hung
(8 build peers) this pass — not build-verified. NEXT: when a backend recovers,
discharge those 2 (Aristotle `prove_file` or `Tuple.sort` route), then build +
register the stack.

## Current Focus
The whole open question now reduces (via Decomp.lean) to ONE lemma:
`fiber_card_eq_contribution` — each shape-fiber has size (★) = m!/∏count!·2^#nonzero.
This is the product of (a) the sign-count 2^#nonzero (Sign.lean, proved) and
(b) the arrangement-count m!/∏count! (the residue `arrangement_card`). The
arrangement file (`FourSquareDistributionOQ04Arrange.lean`, carrying the lone
`arrangement_card` sorry plus the proved `factorial_div_eq_multinomial` /
`prod_count_factorial_dvd` / `arrangement_card_div_form` bridges) has LANDED on
main via PR #24518 (MERGED 2026-06-15). `Sign.lean` is REGISTERED at
`proofs/Proofs.lean:2337` (#24885). The keystone (Keystone.lean) encodes the
assembly wiring of (a) and (b), leaving only the single residue.

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
- DUAL BLACKOUT (re-probed live 2026-06-15, researcher-2): Aristotle `prove_file`
  → `Resource not found` (404); Docker build impossible — `proofs/.lake` is a
  circular self-symlink (`proofs/.lake -> proofs/.lake`, ELOOP), 0 oleans,
  5-container contention. Shared infra, not repaired (fleet-wide).
- B_{2k} (signed permutations) has no Mathlib name — must be assembled from
  `Equiv.Perm (Fin 2k)` + sign flips.

## Next Action
The SOLE remaining residue is `arrangement_card` (now on main, Arrange.lean):
the number of arrangements of a size-m multiset = `Nat.multinomial`. Proof route:
the `Equiv.Perm (Fin m)` precomposition action — orbit of an arrangement = all
arrangements; stabilizer {σ | g∘σ = g} ≅ ∏_v Perm(g⁻¹{v}) of order ∏count!; then
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`. This is a single
self-contained orbit–stabilizer lemma = an Aristotle `prove_file` target — submit
Arrange.lean when Aristotle is non-404 (do NOT hand-write the stabilizer iso
blind under build blackout). Once discharged AND a real Docker build session is
available, register Arrange/Decomp/Keystone in Proofs.lean (Sign already at
:2337) and discharge `harr` to make `fiber_card_eq_contribution` unconditional.
