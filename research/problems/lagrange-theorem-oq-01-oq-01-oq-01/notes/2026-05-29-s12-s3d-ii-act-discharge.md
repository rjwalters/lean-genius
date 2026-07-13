# S12 ACT — S3d-ii shipped: OQ existence direction discharged (sorry-free)

**Author**: researcher-1
**Date**: 2026-05-29T07:50Z
**Phase**: ACT → COMPLETED (iter 11 → 12)

## Summary

The open question (exhibit a non-cyclic group of order `pq` whenever primes
`p ∣ q - 1`) is now **discharged for the general case**, sorry-free and
Docker-verified. Approach A had handled `p = 2` (dihedral); Approach B now
handles all `p ∣ q - 1` via the semidirect product.

The 2-week ACT gate (host disk + Docker daemon, see S10/S11 PREP) had cleared by
this session: `df -h /System/Volumes/Data` = **67 Gi avail** (gate threshold 50
Gi), Docker **v29.4.1** healthy.

## What shipped (proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean)

S3d-ii section (~120 LOC) appended after S3d-i:

- `approachBGroup hp hp_dvd` (abbrev) = `Multiplicative (ZMod q) ⋊[actionHom hp hp_dvd] Multiplicative (ZMod p)`
- `actionHom_ofAdd_one` — `actionHom (ofAdd 1) = (exists_mulAut_mult_of_order_p ..).choose` (= ψ)
- `exists_actionHom_not_fixed` — non-triviality, **NO SORRY** (the S10-PREP R3 high-risk item)
- `approachBGroup_card` — `Nat.card = p * q`
- `approachBGroup_not_isCyclic`
- `exists_noncyclic_of_pq_when_p_dvd_q_sub_one` — main theorem
- order-21 sanity `example`

Final Docker build: `✔ [7743/7743]`, 0 errors, 0 warnings, 0 sorries, 0 axioms.
File now 440 LOC, 11 theorems, 3 definitions.

## Two key lessons (vs the S10 PREP forecast)

1. **The R3 sorry was avoidable.** The S10 PREP forecast a `sorry` on the
   non-triviality witness. It is fully provable: `actionHom (ofAdd 1)` reduces to
   the order-`p` automorphism `ψ` via
   `AddMonoidHom.coe_toMultiplicativeLeft` → `toAdd_ofAdd` → `ZMod.lift_coe`
   (at integer `1`) → `zmultiplesHom_apply` → `one_zsmul` → `toMul_ofMul`. Since
   `orderOf ψ = p ≥ 2`, `ψ ≠ 1`, so it moves some element.
   - Gotcha: `toAdd_ofAdd` / `toMul_ofMul` are **root-level** lemmas (no
     `Multiplicative.` / `Additive.` prefix) and are `rfl`.

2. **Non-cyclic must use `IsCyclic.commutative`, not `mul_comm`.**
   `IsCyclic.commutative : Std.Commutative (· * ·)` — its `.comm` is stated over
   the canonical `(· * ·)` = `SemidirectProduct.instMul`, so it matches the
   `SemidirectProduct.mul_left` / `left_inl` / `right_inr` simp lemmas. Going via
   `IsCyclic.commGroup` + `mul_comm` FAILS (a `CommMagma.toMul` vs `instMul`
   instance-path mismatch the unifier won't bridge).

## Decoupling from the Sylow blocker

ApproachB.lean referenced **no** Approach-A identifier (verified by a standalone
`import Mathlib`-only compile of the full S3a..S3d-ii body). The
`import Proofs.LagrangeTheoremOQ01OQ01OQ01` was dead weight that transitively
pulled in the **broken** `Proofs.SylowTheoremOQ01` (8 v4.26.0 errors). Removing
it makes ApproachB.lean Mathlib-only and **buildable** — clearing the
`(build pending — Sylow parent blocker)` qualifier this work had carried since
S3a.

## Remaining work

- New OQ slugs: iff version, uniqueness.
- Mechanic/doctor (NOT research): repair `Proofs/SylowTheoremOQ01.lean` v4.26.0
  drift — still blocks the PRIMARY Approach-A file and the Lagrange umbrella, but
  no longer ApproachB.
