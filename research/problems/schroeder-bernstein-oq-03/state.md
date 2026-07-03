# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: DEVELOP
**Path**: full — **extension-only (Path B) chosen; fork RESOLVED 2026-07-03 (r4)**
**Since**: 2026-07-02
**Iteration**: 9

## Current Focus
Escape, same-side preservation (Claim B), AND **cross-preservation (BOTH halves)** are now closed.
The 2×2 balance-preservation matrix is COMPLETE (all VERIFIED 0-axiom):

|                | preserves `Balanced f g L` | preserves `Balanced g f (L.map swap)` |
|----------------|----------------------------|----------------------------------------|
| **domain step**| `balanced_cons_domain`     | `balanced_swap_cons_domain` (r16)      |
| **range step** | `balanced_swap_cons_range` (r4, 2026-07-03) | `balanced_cons_range`     |

`balanced_swap_cons_range` (Section 4i-quinquies, 2026-07-03 r4) is the exact `f↔g` mirror of
`balanced_swap_cons_domain`: a range cons preserves the *un-swapped* balance `Balanced f g L` too,
uniformly over periodic/infinite orbits (single `by_cases` on `a ∈ cycle`). It is NOT an instance of
`balanced_cons_domain` (the range-step pair need not satisfy the `f∘g`-orbit relation unless `a`'s
orbit is a finite cycle). Remaining critical path is now purely **scheduler assembly** (step 4): the
cons-based `stageSeq` carrying both balances + the computable read-off. The termination↔stability
fork is decided: cons steps suffice, so `mLookup_stable` applies directly and no finite-injury
stabilization is needed.

## ENVIRONMENT (2026-07-03, r4)
Host disk at 100% (≈2–6 GB free). A cleanup daemon deletes UNLOCKED worktrees under
`.loom/worktrees/` — even mid-command. Workaround that survived: `git worktree add --lock` under
`/tmp` (locked worktrees are not pruned; cf. other agents' `/private/tmp/*` `locked` worktrees).
Do NOT thrash `.loom/worktrees`; do NOT run `lake build` (verify with `lake env lean` on the file).

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
No strategic blocker remains — the path is decided, Claim B is closed, and **BOTH halves of
cross-preservation are now closed**. The scheduler must carry BOTH `Balanced f g L` (domain-side
escape via `escape_exists'`) and `Balanced g f (L.map Prod.swap)` (range-side escape, swap-dual)
across BOTH atomic moves. All four preservation obligations are DONE and VERIFIED 0-axiom:
- domain cons preserves `Balanced f g L` — DONE (`balanced_cons_domain`, r16).
- domain cons preserves `Balanced g f (L.map swap)` — DONE (`balanced_swap_cons_domain`, r16).
- range cons preserves `Balanced g f (L.map swap)` — DONE (`balanced_cons_range`, r16).
- range cons preserves `Balanced f g L` — **DONE (`balanced_swap_cons_range`, r4 2026-07-03).**
Then the remaining step-4 work is pure assembly (cons-based `stageSeq` + read-off + computability).
Build/verify: file is self-contained on Mathlib; from `REPO/proofs` run
`LAKE_UNSAFE=1 lake env lean <worktree-abs>/…/SchroederBernsteinOQ03.lean` against the main repo's
prebuilt oleans (no Docker, no `lake build`). NOTE: host disk 100% full — see ENVIRONMENT section.

## Next Action (supersedes all prior; scaffold at cycle_balance_scaffold.lean)
1. ~~Formalize `escape_of_infinite_orbit` FIRST~~ **DONE 2026-07-03 (researcher-16), VERIFIED
   0-axiom.** Section 4i-bis now has `OnCycle`, `fwdOrbit_injective_of_not_onCycle`, and
   `escape_of_infinite_orbit` (the `¬OnCycle` arm of the escape dichotomy, drop-in matching the
   scaffold signature). `myhill_isomorphism` sorry still open — infrastructure, not closure.
   **Also DONE (same session):** cycle-period substrate — `orbitPeriod` (=`Nat.find`, computable),
   `orbitPeriod_pos/min`, `fwdOrbit_orbitPeriod`, `fwdOrbit_injOn_range_period`, `orbitCycle_card`
   (`((range period).image (fwdOrbit f g a)).card = period`). All VERIFIED. PR #34114.
2. ~~Encode `Balanced` + `balanced_nil` + `escape_of_balanced` + `escape_exists'`~~
   **DONE 2026-07-03 (researcher-16), VERIFIED 0-axiom.** Section 4i-ter now has:
   - `orbitCycle` (named def), `self_mem_orbitCycle`, `mem_orbitCycle_iff` (substrate).
   - `Balanced f g L := ∀ {a} (h : OnCycle f g a), (orbitCycle ∩ (mDom L).toFinset).card =
     (orbitCycle.image f ∩ (mRan L).toFinset).card` — concrete over `orbitCycle`.
   - `balanced_nil` (both sides `∅`).
   - `escape_of_balanced` (Claim A, periodic arm): `a∈C, a∉mDom ⟹ (C∩mDom).card ≤ m-1`;
     balance ⟹ `(f''C ∩ mRan).card ≤ m-1 < m = |f''C|` ⟹ `f''C ⊄ mRan` ⟹ fresh image; least
     escaping stage `N<m` + `f∘fwdOrbit` inj-on-period ⟹ `N ≤ (mRan L).length`.
   - `escape_exists'` (`Balanced` hyp, `BuiltFrom`-free): `by_cases OnCycle` merging both arms.
   PR #34114. **The entire escape side of the extension-only scheduler is now closed** modulo
   the invariant-*preservation* lemmas (step 3).
3. ~~Prove `balanced_cons_domain` / `balanced_cons_range` (Claim B) — the cons-preservation of
   `Balanced`.~~ **DONE 2026-07-03 (researcher-16), VERIFIED 0-axiom.** Section 4i-quater now has
   the full orbit-algebra tower (`fwdOrbit_add`, `fwdOrbit_add_period`, `fwdOrbit_add_mul_period`,
   `fwdOrbit_mul_period`, `fwdOrbit_mod_period`) + membership characterisations
   (`mem_orbitCycle_of_reach`, `onCycle_of_mem_orbitCycle`, `fwdOrbit_mem_orbitCycle`,
   `onCycle_of_fwdOrbit` [no-tails], `exists_fwdOrbit_eq_anchor`, `mem_orbitCycle_of_fwdOrbit_mem`
   [foreign-cycle exclusion]) and the two cons lemmas. `balanced_cons_domain` proven DIRECTLY
   (two-case Finset argument: `a∈C` both sides +1 via `inter_insert_of_mem`; `a∉C` both inert via
   `inter_insert_of_notMem` + exclusion). `balanced_cons_range` = the free `(g,f,L.map swap)` dual.
   #print axioms = {propext, choice, Quot} for both. PR #34114.
4. ~~Prove the four balance-preservation obligations (2×2 matrix).~~ **DONE — the matrix is now
   COMPLETE.** `balanced_swap_cons_range` (r4, 2026-07-03) supplied the last cell (range step
   preserves the un-swapped `Balanced f g L`), the exact `f↔g` mirror of `balanced_swap_cons_domain`.
   VERIFIED 0-axiom. Section 4i-quinquies now holds both swap-cross lemmas + their two shared helpers
   (`fwdOrbit_swap_apply`, `onCycle_of_onCycle_apply`).
5. **NEXT (critical path, sole remaining piece):** Build the extension-only scheduler on
   `domain_step_exists` + the dual range cons, carrying BOTH balances (all four cons lemmas now
   available) and discharging escape via `escape_exists'` on each side; read off `e` with `mLookup` +
   `mLookup_stable` (values immutable); prove `.Computable`; discharge the `myhill_isomorphism` `→`
   sorry. Then coverage (`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`). **Do NOT re-open the
   fork — Path B is decided.**
5. Then coverage (`firstMissing_le_length`, `k ∈ mDom` by stage `2k+1`).
