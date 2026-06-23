# Research State: inverse-galois-d4-oq-01

## Current State
**Phase**: DONE
**Path**: fast
**Since**: 2026-06-16
**Iteration**: 4

> **STATE-SYNC (researcher-8, 2026-06-16).** This file was frozen at the
> Iteration-1 ORIENT stub ("None yet / 0 attempts") while three later
> sessions (recorded in `knowledge.md`) drove the problem to completion and
> merged the work to `main`. The header above now reflects reality. Read
> `knowledge.md` for the full record.
>
> **JSON-SYNC (researcher-2, 2026-06-18).** The structured record
> `src/data/research/problems/inverse-galois-d4-oq-01.json` was still frozen at
> the stale `status: available` / `phase: ORIENT` "build-pending" snapshot
> (where this `state.md` was already `DONE`), so the problem kept surfacing as
> available work. Reconciled the JSON to `status: completed` / `phase: COMPLETED`
> to match #24876 and the `verified` gallery entry. No Lean change.

## Summary of Completed Work
Both the internal and external ℤ/4 ⋊ ℤ/2 decompositions of the D₄ Galois
action are formalized, machine-checked (Docker-GREEN), registered, and merged.

- **Internal decomposition** — `proofs/Proofs/InverseGaloisD4OQ01.lean`
  (13 theorems, 0 sorry / 0 axiom). Normal order-4 rotation subgroup ≅ ℤ/4,
  order-2 reflection complement ≅ ℤ/2, inversion twist
  (`reflection_conj_rotation'`), `⊔ = ⊤`, `⊓ = ⊥`, packaged in
  `d4_internal_semidirect`. Verified Session 2.
- **External packaging** — `proofs/Proofs/InverseGaloisD4OQ01External.lean`
  (171 lines, 0 sorry / 0 axiom). Honest `MulEquiv`
  `SemidirectProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) φ
  ≃* DihedralGroup 4` with `φ` the inversion action, via
  `SemidirectProduct.lift` (`d4Equiv`). A genuine Mathlib gap (no
  `DihedralGroup n`-as-semidirect-product result upstream). Docker-GREEN
  (7746 jobs), registered at `Proofs.lean:2520`. Verified Session 3 /
  **PR #24876, MERGED 2026-06-16**.

Gallery `meta.json`: `status: verified`, `badge: original`, `axiomCount: 0`.

## Active Approach
None — OQ-01 (the explicit ℤ/4 ⋊ ℤ/2 structure question) is resolved.

## Attempt Count
- Total attempts: resolved across Sessions 1–3 (see `knowledge.md`)
- Approaches tried: internal decomposition + external `SemidirectProduct` MulEquiv

## Blockers
None — work complete and merged. (Aristotle `prove` was 404 throughout;
Docker build route sufficed.)

## Next Action
None for OQ-01. The remaining direction is the **separate, harder OQ-03
bridge**: a concrete `Gal(X⁴−2/ℚ) ≃* DihedralGroup 4`, which requires
"D₄ = unique transitive order-8 subgroup of S₄" and is tracked as its own
problem (explicit anti-goal here — do not fold it into OQ-01).
