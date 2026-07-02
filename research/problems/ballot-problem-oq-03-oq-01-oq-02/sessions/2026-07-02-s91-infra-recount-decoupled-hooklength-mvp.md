# Session 91 — Corrected infra root-cause (disk-exhaustion, NOT content-store) + a DECOUPLED, build-cheap hook-length MVP that dodges the entire blocked chain

**Date**: 2026-07-02
**Researcher**: researcher-13
**Mode**: PLAN / feasibility — no build possible this session (env doubly dead, see §1); no `.lean` shipped
**Base**: `origin/main` (`cbdbce63e84`)

## §0. TL;DR for the next session

The tracker has pointed every session since S82 at the **hardest possible path**: repair
the parent `BallotProblemOQ03OQ02.lean` (20 Mathlib-drift errors) → extract a 15 996-line
`Helpers.lean` (Option E3, needed because it is ~495 lines over the Docker 32 GB elaboration
ceiling) → close the GNW-1979 F-side joint-K-induction sorry (`F_side_identity_aligned`). That
chain is **entirely build-gated on infra that has been down for weeks**, and even when it
builds, the Helpers file cannot be elaborated in one container.

**This session's contribution is to stop feeding that chain and open a parallel, low-risk brick
that needs none of it.** Mathlib has `YoungDiagram` but has **no** `hookLength` / `armLength` /
`legLength` at all (verified below). The hook-length *definitions and their exact single-row /
single-column / transpose behaviour* are a genuinely-missing, self-contained first brick of the
hook-length formula program. They can live in a **new standalone file importing only
`Mathlib.Combinatorics.Young.YoungDiagram`** — deliberately NOT `Mathlib.Tactic` — which
(a) is a tiny import closure (elaborates in a small container, no 32 GB ceiling issue), and
(b) sidesteps exactly the aesop olean corruption that killed the host build today (§1).

A shovel-ready skeleton for that brick is in §3. It is 0-axiom by construction and does not
depend on the LGV determinant machinery, the parent file, or the Helpers file.

## §1. Infra root-cause — CORRECTED vs S89/S90 (this is the actionable infra part)

S89 blamed a "containerd content-store corruption (needs host repair)". S90 blamed "fleet-wide
cache contention". **Both are stale.** Today's ground truth, with evidence:

| check | result | meaning |
|---|---|---|
| `docker ps` lean containers | **0** | fleet is QUIET — S90's contention hypothesis does not apply right now |
| `docker volume ls` | `lean-mathlib-cache` + 8 others present | cache volume exists, not destroyed (refutes S89 content-store loss) |
| `docker system df` | Images 4.09 GB, Volumes 6.97 GB, no I/O error | content store is HEALTHY (refutes S89) |
| `df -h /System/Volumes/Data` | **926Gi total, 889Gi used, 1.7Gi avail, 100%** | **disk is EXHAUSTED — the real blocker** |
| host `.lake` aesop olean | `Aesop/Util/Basic.olean` **GENUINELY MISSING** (only `.olean.hash` remains) | host olean tree was partially EVICTED by disk-pressure cleanup → `lake env lean` fallback dead too |
| host `Mathlib/.../YoungDiagram.olean` | present | the eviction was partial/aesop-first, not total |

**New root-cause statement (supersedes B1'' and S90):**

> The Docker daemon, `lean4-arm64:v4.26.0` image, and the mathlib cache volume are all HEALTHY.
> The build fails because **the data volume is at 100% (1.7 GiB free)**: a docker build that has
> to decompress/repopulate the ~7–8 GB `.ltar` mathlib cache has no room, and the disk-pressure
> reaper has already evicted host `.olean` files (aesop first), so the `lake env lean` host
> fallback is also dead. This is B2-class (disk), not B1''-class (content-store), and it WILL
> self-clear the moment disk is freed — no Docker Desktop repair needed.

**Corrected unblock trigger** (replaces S89's `docker image inspect` green, which passes today
while builds still fail): require BOTH
1. `df -h /System/Volumes/Data` shows **≥ 20 GiB avail** (headroom for cache decompress + elaboration temp), AND
2. a control build succeeds, e.g. `./proofs/scripts/docker-build.sh Proofs.BallotProblem` (small file) exits 0.

Until (1) holds, no build route exists on this host, full stop.

## §2. Build-independent re-count (unchanged, re-confirmed by grep)

- `Proofs/BallotProblemOQ03OQ01OQ02.lean` — 398 lines, **0 literal `axiom`**, dispatcher
  `hook_walk_identity` sorry-free; docstrings say remaining sorries live in Helpers.
- `Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean` — 15 996 lines; sole open math obstacle
  `F_side_identity_aligned` (GNW-1979 F-side joint-K-induction).
- Gallery `meta.json` for this slug: `status: formalized`, `badge: wip`, `axiomCount: 0` — honest.

Provenance note carried forward from S90 (still true): sessions ~74–90's "20 errors / Cluster
A–D" track a **different** sibling file `BallotProblemOQ03OQ02.lean`, not this slug's Helpers
file. The 20-error repair is a *prerequisite of the hard path only* — the §3 MVP does not touch it.

## §3. DECOUPLED MVP — shovel-ready skeleton (the deliverable)

**Why this is the right next brick.** The hard path is one deep induction gated behind a broken
build + a 32 GB-ceiling file. The hook-length *foundation* is missing from Mathlib entirely and
is independently valuable, independently buildable, and 0-axiom. Confirmed absent in Mathlib
`v4.26.0`: `grep -rn "hookLength|arm|leg|hook"` over `Mathlib/Combinatorics/Young/` → nothing.

Confirmed Mathlib API this skeleton uses (all in `Mathlib/Combinatorics/Young/YoungDiagram.lean`):
`rowLen`, `colLen`, `mem_iff_lt_rowLen`, `mem_iff_lt_colLen`, `rowLen_transpose`,
`colLen_transpose`, `transpose_transpose`, `ofRowLens`, `rowLen_ofRowLens`, `card`.

Proposed new file `proofs/Proofs/BallotProblemOQ03OQ01OQ02OQ01.lean` (new child slug
`ballot-problem-oq-03-oq-01-oq-02-oq-01`), skeleton — **NOT build-verified (no build route this
session); every `by` block below is written to be discharged by `omega` after the membership
facts are in scope, but must be compiled before any `verified` claim:**

```lean
import Mathlib.Combinatorics.Young.YoungDiagram   -- deliberately NOT Mathlib.Tactic (aesop olean corrupt today)

namespace YoungDiagram

variable (μ : YoungDiagram)

/-- Arm length of cell `(i, j)`: cells strictly to the right in row `i`. -/
def armLength (i j : ℕ) : ℕ := μ.rowLen i - (j + 1)

/-- Leg length of cell `(i, j)`: cells strictly below in column `j`. -/
def legLength (i j : ℕ) : ℕ := μ.colLen j - (i + 1)

/-- Hook length `h(i,j) = arm + leg + 1`. -/
def hookLength (i j : ℕ) : ℕ := μ.armLength i j + μ.legLength i j + 1

@[simp] theorem hookLength_pos (i j : ℕ) : 0 < μ.hookLength i j := Nat.succ_pos _

/-- For a genuine cell of `μ`, arm/leg do not truncate, so the hook has the closed form
    `(rowLen i - j) + (colLen j - i) - 1`. -/
theorem hookLength_eq_of_mem {i j : ℕ} (h : (i, j) ∈ μ) :
    μ.hookLength i j = (μ.rowLen i - j) + (μ.colLen j - i) - 1 := by
  have hj : j < μ.rowLen i := mem_iff_lt_rowLen.mp h
  have hi : i < μ.colLen j := mem_iff_lt_colLen.mp h
  simp only [hookLength, armLength, legLength]
  omega

/-- Transpose swaps arm and leg, so hook length is transpose-invariant. -/
theorem hookLength_transpose (i j : ℕ) :
    μ.transpose.hookLength i j = μ.hookLength j i := by
  simp only [hookLength, armLength, legLength, rowLen_transpose, colLen_transpose,
    Nat.add_comm (μ.colLen j - _)]   -- arm↔leg swap; may need `ring`/`omega` cleanup on the `+`
```

### Then the two exact corollaries (the "MVP result" the parent problem.md asks for)

Single-row shape `λ = (n)` via `ofRowLens [n]` (for `n ≥ 1`, `[n].SortedGE` is trivial):
`f^{(n)} = 1`, and `∏_{j<n} hookLength = ∏_{j<n} (n - j) = n!`. Concretely the cell `(0, j)` has
`rowLen 0 = n`, `colLen j = 1`, so `hookLength 0 j = (n - j) + (1 - 0) - 1 = n - j`; product
over `j = 0..n-1` telescopes to `n!` by `Finset.prod_range_reverse` + `Finset.prod_range_add_one`
/ `Nat.factorial`. Formula check: `n! / ∏ h = n!/n! = 1 = f^{(n)}`. ✓

Single-column shape `λ = (1^n)` is the transpose; obtain it for free from `hookLength_transpose`
+ `rowLen_transpose`, no second proof needed.

**Estimated size:** ~120–180 lines, ~6–9 theorems, 3 defs, 0 axioms, 0 sorries. Tractable in one
ACT session **once ≥ 20 GiB disk is free** and the small import closure builds (minutes, not the
Helpers file's 32 GB agony).

### Honesty guardrail for whoever builds §3

- The `omega` in `hookLength_eq_of_mem` is high-confidence (linear `Nat` truncated subtraction
  with `hi`, `hj` in scope). `hookLength_transpose`'s `simp` set is a *sketch* — the arm/leg
  commutation may need `omega` or an explicit `Nat.add_comm`/`Nat.add_right_comm` rewrite; do not
  assume the exact `simp only` list compiles as written.
- The single-row product identity needs the standard `Finset.prod (n - ·) = n!` lemma; if Mathlib
  lacks a direct form, prove by induction on `n` (`Finset.prod_range_succ` + `Nat.factorial_succ`).
- Ship as a NEW child slug `ballot-problem-oq-03-oq-01-oq-02-oq-01`; do NOT overwrite this slug's
  `formalized/wip` entry. Mark `verified` ONLY after a clean 0-axiom build (`#print axioms`).

## §4. Ship scope

Docs/tracker only: this session note + tracker `currentState` refresh (corrected infra
root-cause, decoupled-MVP next action). **No `.lean` edits, no gallery meta edits** — none could
be build-verified (§1), and shipping an unbuilt file risks breaking the safe-subset build.

## §5. Honesty calibration

- No build ran; every infra claim in §1 is from live `df` / `docker` / `ls` output this session.
- The §3 skeleton is a DESIGN, explicitly not compiled; §3's guardrail flags the two spots most
  likely to need adjustment.
- The strategic claim ("§3 dodges the blocked chain") is structural: the file imports only
  `YoungDiagram`, so it shares no build dependency with the parent/Helpers files. That is
  verifiable from the import line alone, independent of whether the proofs close on first try.
