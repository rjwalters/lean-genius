# Research State: erdos-117-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T17:33:20-07:00
**Iteration**: 3

## Status (researcher-1, 2026-07-22) — MONOTONICITY of the covering number h(n)

New file `Erdos117WIP01Mono.lean` (1 def, 3 thm, 0 ax, 0 sorry, docker-VERIFIED, 8578 jobs;
`#print axioms = [propext, Classical.choice, Quot.sound]`). Adds the elementary structural
monotonicity of `h(n) = abelianCoverNumber n` in `n`, building on `Erdos117WIP01.lean`'s
base values (`h(0)=0`, `h(1)=1`) and closure theory.

- `CoversWithAbelian k n` — names the membership condition of `abelianCoverNumber`'s defining
  set (`k` abelian subgroups cover every finite group with the `n`-commuting property).
- `abelianCoverNumber_eq_sInf` — `h(n) = sInf {k | CoversWithAbelian k n}` (`rfl`).
- `coversWithAbelian_of_le` — the crux: for `n ≤ m`, an `m`-cover is an `n`-cover (the
  `n`-property *implies* the `m`-property via the parent's `hasNCommutingProperty_mono`).
- `abelianCoverNumber_mono` — `n ≤ m` + a finite `m`-cover exists (`∃ k, CoversWithAbelian k m`)
  ⟹ `h(n) ≤ h(m)`. The nonemptiness hypothesis is honest: unconditional monotonicity fails
  under the `Nat.sInf ∅ = 0` convention when `h(m)` is ill-defined (Pyber's upper bound /
  well-definedness is unformalized). Via `Nat.sInf_mem` + `Nat.sInf_le` on the set inclusion.

**★GOTCHA (universe)**: `abelianCoverNumber` and `CoversWithAbelian` are universe-polymorphic
in the group universe (bodies quantify `∀ (G : Type*)`); the value depends on `u`. Every
occurrence must be pinned to a single explicit `universe u` with `.{u}` annotations, else
Lean assigns independent universes → `abelianCoverNumber.{u_1}` vs `.{u_3}` /
`@h G` application-type mismatches. Also: `/- -/` (not `/-- -/`) before a `universe` command.

**STILL OPEN / out of scope**: Pyber's exponential bounds `c₁ⁿ < h(n) < c₂ⁿ` and the OPEN
exact growth base stay unformalized; `h(n)` well-definedness for general `n` = the Pyber upper
bound (nonemptiness of the `sInf` argument), NOT elementary.

## Current Focus
Elementary axiom-free scaffolding of the def-only parent stub (base values, closure, and now
monotonicity of `h`). Deep Pyber bounds remain out of reach.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.
