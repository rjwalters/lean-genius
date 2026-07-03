# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: DEVELOP
**Path**: full — **extension-only (Path B) chosen; fork RESOLVED 2026-07-03 (r4)**
**Since**: 2026-07-02
**Iteration**: 6

## Current Focus
Formalize the **cons-preserved cycle-balance invariant** that discharges `escape_exists`
without `BuiltFrom`, then assemble the extension-only scheduler. The termination↔stability
fork is decided: cons steps suffice, so `mLookup_stable` applies directly and no finite-injury
stabilization is needed.

## Active Approach
Stage-wise finite back-and-forth (Rogers §7.4), **extend-only**. Even/odd atomic moves DONE and
VERIFIED 0-axiom (`domain_step_exists` cons; dual range cons). The read-off is monotone because
nothing is ever removed. The remaining work is the balance invariant + scheduler assembly.

## Fork resolution (2026-07-03, researcher-4) — see knowledge.md r4 entry + cycle_balance_scaffold.lean
`escape_exists` does NOT need `BuiltFrom`. It follows from the **cons-preserved** invariant
`Balanced L :≡ ∀ g∘f-cycle C, (C ∩ mDom L).card = (f(C) ∩ mRan L).card`:
- **Balanced ⟹ escape** (BuiltFrom-free): infinite orbit ⇒ pigeonhole; cycle `C` with fresh
  anchor ⇒ `(f(C)∩mRan).card = (C∩mDom).card ≤ |C|-1 < |C|` ⇒ a fresh f-image exists.
- **Balanced is cons-preserved** (both domain and range steps add one fresh dom + one fresh ran
  point on the affected cycle; injectivity of `g∘f` gives no ρ-tails so other cycles are inert).
This is why r14's `OrbitGEdged` failed (it fixed the *witnessing pair* as a g-edge; the anchor
cons supplies an f-edge-like pair) but the *count* is preserved. Path B is viable; no finite injury.

## Attempt Count
- Approaches tried: 1 (stage-wise back-and-forth). Fork within it resolved; 1 dead sub-approach
  (`OrbitGEdged`) refuted, replaced by `Balanced`.

## Blockers
No strategic blocker remains — the path is decided. Remaining risk is purely the Lean **encoding
of "cycle" and its cardinality** (`Balanced`, scaffold step 3): likely a `Finset`-of-orbit cut by
`Nat.find` of the period, or a cycle-free reformulation. **Build environment is NOT hostile** —
researcher-16 established a reliable verify path (2026-07-03): the file is self-contained on
Mathlib, so compile the worktree copy with `LEAN_PATH` → the main repo's prebuilt oleans and
`elan run leanprover/lean4:v4.26.0 lean` (no Docker, no `lake build`). Recorded in knowledge.md.

## Next Action (supersedes all prior; scaffold at cycle_balance_scaffold.lean)
1. ~~Formalize `escape_of_infinite_orbit` FIRST~~ **DONE 2026-07-03 (researcher-16), VERIFIED
   0-axiom.** Section 4i-bis now has `OnCycle`, `fwdOrbit_injective_of_not_onCycle`, and
   `escape_of_infinite_orbit` (the `¬OnCycle` arm of the escape dichotomy, drop-in matching the
   scaffold signature). `myhill_isomorphism` sorry still open — infrastructure, not closure.
2. **NEXT (critical path):** Pick the Lean encoding of `Balanced`; prove `balanced_cons_domain` /
   `balanced_cons_range` and `balanced_nil` (Claim B).
3. Prove `escape_of_balanced` (Claim A, cycle case); merge into `escape_exists'` by `OnCycle`
   dichotomy.
4. Build the extension-only scheduler on `domain_step_exists` + dual range cons; read off `e`
   with `mLookup` + `mLookup_stable` (values immutable); prove `.Computable`; discharge the
   `myhill_isomorphism` sorry. **Do NOT re-open the fork — Path B is decided.**
5. Then coverage (`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`).
