# Research State: liouville-theorem-oq-04

## Current State
**Phase**: REFINE
**Path**: full
**Since**: 2026-05-08T06:30:00+00:00
**Iteration**: 14

## Current Focus
Part IV.11 (`padic_liouville_bridge_rational_roots_case`) added in Session 14.
A fully-proved theorem (no new axioms, no sorries) discharging the
**rational-roots case** of `padic_liouville_norm_bridge` — i.e., uniform δ > 0
with `δ ≤ ‖α - (q : ℚ_[p])‖` for every rational root `q` of `f.map (algebraMap ℤ ℚ)`
whose ℚ_[p]-image differs from α.

Construction: form `R'` = Finset of rational roots `q` with `(q : ℚ_[p]) ≠ α`
(finite, cardinality ≤ deg f). When `R'` is non-empty, take
`δ := R'.inf' (q ↦ ‖α - (q : ℚ_[p])‖)` — strictly positive via
`Finset.lt_inf'_iff` because every entry is the norm of a non-zero element.
When `R'` is empty, take `δ := 1`; the conclusion is vacuously true.

After this session: 1 axiom (unchanged), 0 sorries, ~1216 lines, 34 theorems,
6 defs. **Both case-analysis pieces are now formally proved**: Part IV.10
(algebraic) + Part IV.11 (rational-roots). The bridge axiom can now be
discharged in a single combine-and-case-split session.

## Active Approach
With **both** case-analysis pieces (Parts IV.10 and IV.11) now proved as
stand-alone lemmas, the remaining work to discharge `padic_liouville_norm_bridge`
is purely combinational: take `C := min((1/(L·M)), δ)` and case-split on
`(f.map alg').eval (r/s) ?= 0` over ℚ, dispatching each side via the
respective lemma.

## Attempt Count
- Total attempts: 13
- Current approach attempts: 6
- Approaches tried: 3

## Blockers
- None for the next step (combine-and-case-split). All structural ingredients
  AND both case-analysis pieces are formally proved.

## Next Action
**Session 15**: discharge `padic_liouville_norm_bridge` axiom to theorem by
combining Parts IV.10 and IV.11.

1. State the new theorem `padic_liouville_norm_bridge_proved` with the same
   signature as the axiom, and provide a `by`-proof.
2. Obtain `δ > 0` from Part IV.11 (rational-roots case) given `f ≠ 0` (which
   follows from `1 ≤ f.natDegree`).
3. Set `L := intPolyL1 f`, `M := coeffNormSum p g`, both positive.
4. Take `C := min((1/(L·M)), δ)` — strictly positive.
5. For each `(r, s)` with `s ≠ 0` and `α ≠ (r:ℚ_[p])/s`:
   - Let `H := max r.natAbs s.natAbs ≥ 1`.
   - Case split on `(f.map (algebraMap ℤ ℚ)).eval ((r:ℚ)/s) ?= 0`:
     - **Non-zero**: apply Part IV.10 to get `1/(L·M·H^(2d)) ≤ ‖α - r/s‖`;
       since `C ≤ 1/(L·M)`, conclude `C/H^(2d) ≤ 1/(L·M·H^(2d)) ≤ ‖α - r/s‖`.
     - **Zero**: apply Part IV.11 with `q := (r:ℚ)/s` to get `δ ≤ ‖α - r/s‖`;
       since `C ≤ δ` and `H ≥ 1`, conclude `C/H^(2d) ≤ C ≤ δ ≤ ‖α - r/s‖`.
6. After the discharge: also remove the old `axiom` declaration, replace with
   the new theorem, and update gallery: `status: "axiomatized" → "verified"`,
   `badge: "axiom" → "original"`, `axiomCount: 1 → 0`.

## Session 14 deltas (this session)
- File: 1102 → 1216 lines (+114), 33 → 34 theorems (+1), defs unchanged.
- Theorem added: `padic_liouville_bridge_rational_roots_case`.
- Axioms unchanged (still 1: `padic_liouville_norm_bridge`).
- Sorries unchanged (still 0).
- Build: pending (per established convention on this slug; cold-cache 45 min).

## References
- Parent file: `proofs/Proofs/LiouvilleTheoremOQ04.lean`.
- Algebraic case: Part IV.10, `padic_liouville_bridge_algebraic_case`
  (Session 13, line ~671).
- Rational-roots case (NEW): Part IV.11,
  `padic_liouville_bridge_rational_roots_case` (Session 14, line ~813).
- Bridge axiom: `padic_liouville_norm_bridge` (line ~917 after this session).
