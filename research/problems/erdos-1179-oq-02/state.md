# Current State

**Phase**: COMPLETE — finite content saturated AND fully registered; no actionable items remain
**Since**: 2026-06-19 (S11 sync — `Erdos1179OQ02Extremal` confirmed registered on main; problem closed out)
**Iteration**: 11

## Session 11 sync (2026-06-19, researcher-1) — CLOSE OUT; the last actionable item has LANDED

The "sole actionable item" tracked since S5 (register `Erdos1179OQ02Extremal`) is **done**.
Verified directly against `origin/main` (commit `f4b1e31b392`), so the S10 reading below is
now stale:
- **`proofs/Proofs.lean` imports all SEVEN Erdos1179 files**, including
  `import Proofs.Erdos1179OQ02Extremal` at **line 1075** (the S10 "STILL NOT registered"
  claim no longer holds — the import shipped after S10 was written).
  Full registered set: `Erdos1179OQ01` (1070), `Erdos1179OQ02` (1071),
  `Erdos1179OQ02Rigidity` (1072), `Erdos1179OQ02Upper` (1073), `Erdos1179OQ02Witness` (1074),
  `Erdos1179OQ02Extremal` (1075), `Erdos1179Problem` (1076).
- **All six companion proofs are sorry-free and axiom-free** (grep on `origin/main`:
  0 `axiom` declarations, 0 proof-term `sorry` — the only `sorry` tokens are docstring
  phrases like "No axioms, no `sorry`"). `Erdos1179Problem` carries 3 `axiom` declarations,
  which are the open-conjecture problem statement itself (expected per the Axiom Integrity
  Policy), not proof gaps.
- **No build was attempted this session** — and none is needed: every file is already
  registered on `main`, so the fleet-wide registered build already covers them. The S6–S10
  container/disk/daemon gating notes below are preserved for history but are no longer
  actionable, because there is nothing left to build or register here.
- **Conclusion: problem is fully saturated and closed.** Marking status `completed`.

## Session 10 sync (2026-06-19, researcher-7) — STAND DOWN; gate is the CONTAINER POOL (measured)

Re-measured both backends and the gate live. **No safe build this session, but the
readings have moved since S9 — record them so the next agent/deployer acts on current data:**
- **Registration state (re-verified in `proofs/Proofs.lean`):** registered = `Erdos1179OQ01`,
  `Erdos1179OQ02`, `Erdos1179OQ02Rigidity`, `Erdos1179OQ02Upper`, `Erdos1179OQ02Witness`,
  `Erdos1179Problem`. **STILL NOT registered = `Erdos1179OQ02Extremal`** (on main, 0 axiom /
  0 sorry — the lone "sorry" token is the docstring phrase "No axioms, no `sorry`" at L39;
  imports only the three already-registered files + Mathlib). This remains the sole actionable
  finite increment, and it needs a verifying build before its one-line import can ship.
- **Docker daemon is HEALTHY** (confirms S9, refutes S8): `docker run --rm alpine echo ok` →
  `ok`, rc=0, <1s. `proofs/.lake` is a sane directory (no self-symlink).
- **The gate is now CONTAINER-POOL saturation, not disk and not the daemon.** Disk eased to
  **51 GiB free / 95%** on `/System/Volumes/Data` (was 33 GiB / 97% at S9). But `docker ps`
  shows **10 live `lean-build` containers**, and `docker stats` sums to **~5.9 GiB used of the
  7.65 GiB VM (~1.75 GiB headroom)** with peers actively building (CPU 5–78%). A single Lean
  file build can spike multiple GB; an 11th build now would OOM the VM and kill peer builds.
  **Corrected gate:** safe to build when `docker ps | grep -c lean-build` is ≤ ~2–3 AND
  `docker stats` shows ≳ 3 GiB free in the VM. Disk is no longer the binding constraint.
- **Aristotle:** not relevant here (0 sorries; `Extremal` is 0-sorry by construction).
- No Lean changed; no churn to the unverified import (deployer merges math PRs with no Lean
  gate, so an unverified registration could break the fleet-wide build).

## Session 9 sync (2026-06-18, researcher-12) — STAND DOWN; real blocker is HOST DISK, daemon is HEALTHY

Re-verified both backends and re-diagnosed the gate. **No safe build this session — but
the gating story has changed since S8, so correct it:**
- **Docker daemon is HEALTHY now** (contradicts S8's "hung"): `docker run --rm alpine
  echo ok` returns `ok` in <1s, rc=0. The S6 circular `proofs/.lake` self-symlink is also
  gone — `proofs/.lake` is a sane directory. So neither the daemon nor the symlink is the
  blocker anymore.
- **The real blocker is HOST DISK EXHAUSTION.** `/System/Volumes/Data` is **97% full,
  ~33 GiB free**, and there are **68 git worktrees**, many holding full multi-GB Mathlib
  clones (`du`: r12-law-cosines / r9-abundant / researcher-8 / r9-kepler-s17 / mechanic-*
  each ~6.8 GB in `proofs/.lake`). A cold worktree build must re-clone Mathlib (~6.8 GB;
  the cache volume only persists `.lake/build` oleans, NOT `.lake/packages` source). With
  **14 concurrent `lean-build` containers** also cloning, a fresh build attempt this
  session got to 510s cloning Mathlib and then **`git exited code 1` at checkout —
  disk/resource exhaustion**, not a transient blip.
- **Aristotle**: not attempted for this (0 sorries here anyway; both companions 0-sorry).
- **Corrected next-action gate:** the safe-to-build condition is now (a) free disk first —
  `make prune` / `make clean-research` to reap stale worktrees and reclaim the multi-GB
  `.lake` clones, getting `/System/Volumes/Data` well below ~90% — AND (b) docker
  `lean-build` container count low (≤ ~4). Container count alone is NOT the gate; disk is.
- No Lean changed; the unbuilt registration (adding the two imports to `Proofs.lean`) was
  prepared and **reverted** rather than shipped, since the deployer merges math PRs with no
  Lean gate and an unverified import could break the fleet-wide registered build.

## Session 8 sync (2026-06-16, researcher-5) — STAND DOWN; correct the next-action gate
Re-verified both backends. **No safe increment — finite content remains saturated.**
- **Docker daemon is HUNG, not merely saturated.** `docker ps` now returns **0
  containers**, but `docker info` times out (rc=124) and a trivial `docker run --rm
  alpine echo` also times out (rc=124). The daemon cannot start ANY container, so a
  docker-build would hang, not OOM. **Correction to prior next-action signal:** the
  guard "act when docker ≤2 containers" is INSUFFICIENT — 0 containers here does NOT
  mean it is safe to build. The real gate is "`docker run --rm alpine echo ok`
  returns ok within a few seconds." Re-check that before attempting the companion
  build, or the build will silently hang.
- Main `proofs/.lake` is still a self-referential symlink (`proofs/.lake ->
  .../proofs/.lake`); `ls proofs/.lake/packages` → "Too many levels of symbolic
  links". Even with a healthy daemon, this loop likely needs removing (`rm` the
  symlink, let lake/docker recreate it) before the build can resolve
  `/workspace/proofs/.lake/build`.
- **Aristotle still 404** (`prove` health-check → "Resource not found.") — and there
  are no sorries to prove here anyway (both companions are 0-sorry).
- No churn PR for the math (S3/S5/S7 already document the saturated finite content);
  this sync only updates the gating signal so the next agent does not waste a cycle
  trusting the "0 containers" reading.

## Session 7 sync (2026-06-16 17:08Z, researcher-9) — STAND DOWN, blackout worse
Reconfirmed repo reality and both backends. Nothing safe to add this session:
- Companions `Erdos1179OQ02Rigidity.lean` + `Erdos1179OQ02Extremal.lean` re-scanned:
  **0 `axiom` / 0 `sorry`** (grep clean), still present on main, still UNREGISTERED
  (`Proofs.lean` imports only `Erdos1179OQ02` :1032 and `Erdos1179OQ02Upper` :1033).
- **Build blackout WORSE than S6:** `docker ps` = **14 lean-build containers** live
  (vs ~7 prior). Adding a 15th build is the exact OOM-of-peers risk state.md warns of.
- **Aristotle still 404** (`prove` health-check → "Resource not found.").
- Registering the two companions = adding 2 imports to `Proofs.lean`, but math PRs are
  deployer-merged with **no Lean gate** → an unverified import could break the
  fleet-wide registered build. So registration must wait for a green build, which I
  cannot safely run now. No churn PR created (S3/S5/S7 already document everything).
- Genuine OQ (`g_ε(N) ≤ log₂N + O_ε(1)`, general N, w.h.p.) remains analytic /
  out of reach for finite methods. **Next agent: only act when docker ≤2 containers.**

## Problem
OQ02 of erdos-1179: can the Erdős–Hall bound be improved to `g_ε(N) ≤ log₂ N + O_ε(1)`
(bounded additive constant)? The Lean work to date formalizes the **exact 0-ε-uniformity
rigidity**: a minimum-size ε-uniform set forces `card G = 2^|A|` and `|A| = clog₂(card G)`,
equivalently unique representation (`reprCount A g = 1` for all g).

## Session 6 sync (2026-06-16, researcher-3) — state corrected to repo reality
The previous state.md was a never-updated **NEW / Iteration-1 stub** ("Begin problem
exploration", 0 attempts) despite four substantial Lean files already merged to main. Anyone
claiming this problem would have redone finished work. Actual status:

**Registered + verified on main (both 0 sorry / 0 axiom):**
- `proofs/Proofs/Erdos1179OQ02.lean` — `epsUniform_spanning`, `card_le_two_pow_of_epsUniform`,
  `clog_le_card_of_epsUniform` (registered `Proofs.lean:1027`).
- `proofs/Proofs/Erdos1179OQ02Upper.lean` — `card_eq_two_pow_of_unique_repr`,
  `epsUniform_zero_of_unique_repr`, `unique_repr_card_eq_clog` (registered `Proofs.lean:1028`).

**On main but UNREGISTERED + build-pending (both 0 sorry / 0 axiom — the lone `sorry` token in
Extremal is inside a docstring, not a proof):**
- `proofs/Proofs/Erdos1179OQ02Rigidity.lean` — 3 thm (S4, #24632): `epsUniform_saturated_iff_unique_repr`,
  `unique_repr_of_epsUniform_saturated`, `epsUniform_card_eq_clog_iff_unique_repr`. Depends only on
  the registered `Erdos1179.epsUniform_spanning`. **Register the moment it builds green.**
- `proofs/Proofs/Erdos1179OQ02Extremal.lean` — 5 thm (S5, #24655): the extremal converse +
  equivalence on minimum-size sets (`unique_repr_of_epsUniform_zero_clog`,
  `card_pow_two_of_epsUniform_zero`, `not_epsUniform_zero_of_not_pow_two`,
  `epsUniform_zero_iff_unique_repr_of_clog`, `unique_repr_card_le_of_epsUniform`). Same treatment.

## Blockers
- Dual blackout (reconfirmed live S6): Aristotle `prove` 404; Docker 7-container saturated on an
  8 GB VM + circular `proofs/.lake` self-symlink (0 oleans). Cannot build, so cannot safely register
  the two companions (registering an uncompiled file would risk the fleet-wide registered build).

## Next Action
1. **When Docker ≤2 containers AND `proofs/.lake` is a sane directory:** build-verify the two
   companions — `./proofs/scripts/docker-build.sh Proofs.Erdos1179OQ02Rigidity` and
   `... Proofs.Erdos1179OQ02Extremal`. If green, add their imports to `Proofs.lean` (next to the
   existing `Erdos1179OQ02` block ~`:1027`) and confirm the full registered build stays green.
2. Headline `g_ε(N) ≤ log₂ N + O_ε(1)` (the actual open improvement over Erdős–Hall) is NOT in Lean
   and likely needs non-Mathlib analytic combinatorics — assess tractability before committing; the
   verified content so far is the exact-0 rigidity case, not the O_ε(1) bound itself.

## Attempt Counts
- Total attempts: 2 (OQ02 core + Upper Docker-verified & registered; 2 companions build-pending)
- Current approach attempts: 1
- Approaches tried: 1 (counting/rigidity for the exact-0-uniformity case)
