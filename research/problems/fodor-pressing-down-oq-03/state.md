# State — fodor-pressing-down-oq-03

## Phase: S1 OBSERVE COMPLETE — feasibility map shipped; S2 design is paste-ready, build-gated

> **Iteration**: 1 (fresh EMPTY problem, claimed by researcher-11).
> **Last Updated**: 2026-07-02 (researcher-11).
> **Deliverable this cycle**: `problem.md` + `knowledge.md` (this dir).
> **No Lean committed** — verification environment cold (see below).

## What was done (researcher-11, 2026-07-02)

Produced a documentation/feasibility map separating the OQ into its two
logically-opposite halves and pinning the tractable target:

- **Positive ZFC fragment (formalizable now):** club reflection
  (`clubReflects`), trace-of-a-club-is-club (`isClubBelow_trace`), and the
  honest ω₁ non-reflection fact (`no_uncof_reflection_omega1`). All 0-axiom,
  reuse `Proofs.Club.Basic` unchanged. Designed in `knowledge.md §3, §6`.
- **Obstruction fragment (frontier):** full stationary reflection is
  **independent of ZFC** (must NOT be shipped as a verified theorem); □_κ
  needs a new order-type/coherence module; "□ ⇒ non-reflecting stationary"
  is reachable only in hypothesis-taking form. `knowledge.md §3.4, §5, §6`.

The key correctness guardrail recorded: **do not claim a positive
reflection theorem "0-axiom verified"** — that would be false in ZFC.
The verifiable content is the *base case* + the *ω₁ obstruction*.

## Why no build this cycle

- No Mathlib `.olean` cache in this worktree's `proofs/.lake` (checked
  `Mathlib.olean`, `SetTheory/Ordinal/Topology.olean` — absent). Main repo
  `proofs/.lake` also has no Mathlib build.
- Disk at 99% (~11 GiB free); a from-source Mathlib compile is infeasible
  and the worktree was already reaped once mid-session.
- Compiling from source would take hours; `docker-build.sh` also needs the
  cache. Per project precedent, S1 OBSERVE ships as docs + paste-ready S2.

## Concrete unblock for S2 (build route discovered)

A `find / -name Mathlib.olean` this cycle located **warm Mathlib caches in
sibling worktrees**, e.g.:

- `/Users/rwalters/GitHub/lean-genius-wt/r9-erdos695/proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
- `/Users/rwalters/lg-wt-carmichael/proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
- `/private/tmp/r16-cheby0201oq02/proofs/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`

**Recommended next-cycle ACT** (when a warm-cache worktree is available and
not being reaped):
1. From a worktree carrying this branch, symlink/point the Mathlib package
   build into `proofs/.lake/packages/mathlib` (match toolchain in
   `proofs/lean-toolchain`; caches on other *research* branches may sit at a
   different Mathlib pin — verify no drift, esp. `Complex.abs`→`‖·‖`,
   `div_lt_div_iff`→`…₀` renames noted elsewhere in the project).
2. Build the dependency `Proofs.Club.Basic` olean once:
   `lake env lean proofs/Proofs/Club/Basic.lean -o /tmp/ClubBasic.olean`
   (heavy Mathlib import → prefer `docker-build.sh Proofs.Club.Basic`).
3. Author `proofs/Proofs/Reflection/Basic.lean` per `knowledge.md §6` S2
   list (`Reflects`, `Trace`, `clubReflects`, `isClubBelow_trace`,
   `Reflects.mono`, `no_uncof_reflection_omega1`), `import Proofs.Club.Basic`.
4. Verify 0-axiom via `#print axioms clubReflects` (expect only
   `propext`/`Classical.choice`/`Quot.sound` — those do NOT count).
5. Add gallery entry `src/data/proofs/fodor-pressing-down-oq-03/` (verified,
   badge `original`, status `verified`, 0 axioms) — model meta on the
   parent `fodor-pressing-down` and sibling `fodor-pressing-down-oq-02`.

## Risk notes / gotchas

- The `clubReflects` closedness field transports `IsClosedBelow … o` down to
  `… α` (α ≤ o) — closedness is local; confirm `isClosedBelow_iff`'s
  acc-point quantifier restricts cleanly (should be immediate).
- `isClubBelow_trace` unbounded field: reuse the ω-iteration ("zipper")
  pattern already proven in `diagInter_isUnboundedBelow`
  (`Club/Basic.lean:138+` region / `FodorPressingDown.lean`).
- `no_uncof_reflection_omega1` needs a `cf(α) ≤ |α| ≤ ℵ₀` bound for
  `α < ω₁` — `Ordinal.cof_le_card` / `Cardinal.lt_aleph1_iff_countable`-style
  lemmas; verify exact Mathlib names at the pin.
- **Do NOT** attempt to prove full `Refl(κ)` or construct a □-sequence — the
  former is not a ZFC theorem, the latter is a Jensen-`L` multi-month build.

## Status flags for the pool/JSON gates

This is a completed S1 OBSERVE, not a terminal BLOCK: the slug is *not*
exhausted — S2 is a well-scoped, tractable, 0-axiom verified-proof target,
gated only on a warm Mathlib cache. Suggested registry status after this PR:
`in-progress`, phase `S1-complete` (re-servable when a build env is warm).
