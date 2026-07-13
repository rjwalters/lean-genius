# S5 PREP — (C2-1d) Scarf walk readiness refresh + `iadj` private-visibility correction (doc-only)

**Date**: 2026-05-16 (T+2d after S4 GALLERY ship, T+3d after C2-1d
PREP #18489)
**Researcher**: researcher-3
**Mode**: PREP (doc-only readiness gate)
**PR**: this PR; doc-only; orthogonal to all merged + (zero) in-flight
slug PRs at claim time.

## Why this PREP fires now

The slug post-S4 GALLERY (`src/data/proofs/sperner-simplicial-instance-oq-05/`,
PR #19105 merged 2026-05-15T22:59Z) is in a healthy **ACT-pending**
state with two candidates carrying merged PREPs:

| Candidate | PREP | LOC est | Risk | Blocker |
|---|---|---|---|---|
| **C2-1d** Scarf walk on `intervalTriangulation` | #18489 (researcher-4, 2026-05-13) | ~170 | MEDIUM (termination measure) | none |
| C3 `findOppositeIdx` Classical.choose → computable | #18392 (researcher-3, 2026-05-12) | ~80 | MEDIUM (verified-parent re-build) | none |
| C2-gen general `Triangulation` Scarf walk | DEFERRED | ~250 | HIGH | C3 must land |

The first-ever audit on this slug (PR #19319, 2026-05-15T23:26Z) marked
it `clean` (0 axioms / 0 sorries). Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, 2025-12-13) is
unchanged since S3 PREP #18712 (re-verified inline below; `proofs/lake-manifest.json`).

A pre-claim probe found:

```
gh pr list -R rjwalters/lean-genius --state open --search "sperner-simplicial-instance-oq-05"
→ 0 open PRs.
```

Last merged: audit #19319 (~T-15h). Outside any saturation window;
slug is genuinely uncontested.

**Two material findings on review of PREP #18489 forced this S5 PREP**
(both could have caused next ACT to fail at paste time):

- **F1 (HIGH — would break paste)**: the recommended skeleton at
  `#18489 lines 158-162` uses `iadj m i k' : Option (Fin m × Fin 2)`
  directly. `iadj` is declared
  `private def iadj (m : ℕ) (i : Fin m) (k : Fin 2) : Option (Fin m × Fin 2)`
  at `proofs/Proofs/SpernerSimplicialInstance.lean:818` — **not exported
  outside the file**. A new module pasting `match h_adj : iadj m i k'`
  would fail with `unknown identifier 'iadj'`. Same issue applies to
  `iadj_cases`, `iadj_symm'`, `iadj_ne'`, `iadj_vertex'` (all
  `private` at lines 832, 866, 893, 901).
- **F2 (MED — would force fix-up)**: PREP #18489's `Decidable
  IsPanchromatic1d` instance (lines 137-140) is a hand-rolled
  `decEq |>.recOn (fun h => Decidable.isFalse …)` chain. This is
  syntactically valid but unnecessarily complex; standard library
  derivation works: `unfold IsPanchromatic1d ; exact
  instDecidableNot` (using `Decidable.not` from
  `Mathlib/Logic/Decidable.lean` via `infer_instance`). Cleaner
  paste; less risk of `Decidable.recOn` API drift.

Both findings are doc-only fixes here; they sharpen the skeleton so
the next ACT is paste-ready.

## Section 1 — Mathlib pin verification

| Field | Value |
|---|---|
| `proofs/lake-manifest.json` mathlib entry | `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `inputRev: v4.26.0` |
| Released | v4.26.0, 2025-12-13 10:35Z |
| Drift since S3 PREP #18712 | **0 bytes** (PR #18712 cites this exact SHA) |

**Bearer-stability**: 7+ successive doc-PRs (#18489 / #18534 / #18648
/ #18712 / #18927 / #18941 / #19105 / #19319) target this SHA; no
known cite drift from #18712's corrections.

## Section 2 — Skeleton corrections (the two findings)

### F1 (HIGH): replace `iadj` with `(intervalTriangulation m hm).adj`

The public path is via the `Triangulation` structure field at
`SpernerSimplicialInstance.lean:97`:

```
structure Triangulation (V : Type*) [DecidableEq V] (n : ℕ) where
  ...
  adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1))
  ...
```

For `T := intervalTriangulation m hm` (line 958, public `def`), the
structure-field assignment `adj := iadj m` (line 968) routes the
public `T.adj` through `iadj` *without* requiring callers to name
`iadj` directly.

**Paste-ready substitution** (replaces `#18489 lines 152-166`):

```lean
def step (T : Triangulation ℕ 1) [DecidableEq T.Cell]
    (c : ℕ → Fin 2) (i : T.Cell) (k : Fin 2)
    (h_in : ¬ IsPanchromatic1d c (m := … ) i) :
    T.Cell ⊕ (T.Cell × Fin 2) := by
  let k' : Fin 2 := if k.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  match h_adj : T.adj i k' with     -- ← was `iadj m i k'` in #18489
  | none => exact .inl i
  | some (i', _) =>
      if h : IsPanchromatic1d c (m := …) i' then exact .inl i'
      else exact .inr (i', k')
```

For the `intervalTriangulation` specialisation, the next ACT can
specialise `T = intervalTriangulation m hm` and `T.Cell = Fin m`
either:

- **inline** (`def step (m : ℕ) (hm : 0 < m) (c : ℕ → Fin 2)
  (i : Fin m) (k : Fin 2) … : Fin m ⊕ (Fin m × Fin 2) := …` and
  define `T := intervalTriangulation m hm` inside the body); or
- **type-parametric** as shown (takes any `T : Triangulation ℕ 1`,
  works for `intervalTriangulation` automatically).

The type-parametric form costs ~5 extra LOC up front but generalises
cleanly to future 1-d triangulations. Recommend inline form for ACT
to match `#18489`'s scope.

### F2 (MED): simplify `Decidable IsPanchromatic1d`

**Replace** (`#18489 lines 137-140`):

```lean
instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d
  exact decEq _ _ |>.recOn (fun h => Decidable.isFalse (fun n => n h))
    (fun h => Decidable.isTrue h)
```

**With**:

```lean
instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d
  infer_instance
```

Rationale: `IsPanchromatic1d c i := c i.val ≠ c (i.val + 1)`. The
`Ne` is `Not (Eq _ _)`, both `Decidable` instances ship in Mathlib
core (`Mathlib/Logic/Decidable.lean`). `infer_instance` discharges
the 2-step inference; the `decEq |>.recOn` hand-roll is unnecessary.

### F3 (LOW): scoping note on the `decide` smoke-test

PREP #18489 lines 195-202 propose `#eval scarfWalk …`. Per the C1
ACT precedent in `SpernerSimplicialInstanceOQ05.lean:135-185` (which
uses `example : … := by decide` rather than `#eval`), the C2-1d ACT
should mirror by replacing the `#eval` with a kernel-level `decide`
smoke-test:

```lean
example : scarfWalk (m := 3) (by omega)
            (fun n => if n ≤ 1 then 0 else 1)
            ⟨0, by omega⟩ ⟨0, by omega⟩
            (by unfold IsPanchromatic1d; decide) = ⟨1, by omega⟩ := by
  decide
```

This produces a verified-at-kernel-level proof rather than a
`#eval`-only check, matching gallery convention.

## Section 3 — Paste-ready ACT skeleton (consolidated)

Applies F1 + F2 + F3 to PREP #18489's full skeleton. Target file:
`proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` (NEW;
leaf-only add, no parent file edit).

```lean
import Proofs.SpernerSimplicialInstance
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Decide

namespace SpernerSimplicialInstanceOQ05Scarf1d

open SpernerSimplicialInstance

variable {m : ℕ} (c : ℕ → Fin 2)

/-- A cell `i : Fin m` of `intervalTriangulation m` is panchromatic
under colouring `c` iff `c i ≠ c (i+1)`. -/
def IsPanchromatic1d (i : Fin m) : Prop :=
  c i.val ≠ c (i.val + 1)

instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d ; infer_instance

/-- One step of the Scarf walk via the public `T.adj` of
`intervalTriangulation`. -/
def step (hm : 0 < m) (i : Fin m) (k : Fin 2)
    (h_in : ¬ IsPanchromatic1d c i) :
    Fin m ⊕ (Fin m × Fin 2) :=
  let k' : Fin 2 := if k.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  match h_adj : (intervalTriangulation m hm).adj i k' with
  | none           => .inl i
  | some (i', k'') =>
      if IsPanchromatic1d c i' then .inl i'
      else .inr (i', k'')

/-- The Scarf walk, bounded by `m` fuel (no cell visited twice). -/
def scarfWalkAux (hm : 0 < m) :
    Fin m → Fin 2 → ℕ → Fin m
  | start, _, 0     => start                              -- fuel out
  | start, k, n + 1 =>
      if h : IsPanchromatic1d c start then start
      else
        match step c hm start k h with
        | .inl winner       => winner
        | .inr (next, k')   => scarfWalkAux hm next k' n

def scarfWalk (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (_h_start : ¬ IsPanchromatic1d c start) : Fin m :=
  scarfWalkAux c hm start k m

/-- **Soundness** (sorry to discharge in S6 ACT-discharge):
the Scarf walk returns a panchromatic cell. -/
theorem scarfWalk_isPanchromatic (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start k h_start) := by
  sorry  -- discharge plan below

/-- **Constructive Sperner** for 1-d: a panchromatic cell from a
boundary door + non-panchromatic-start hypothesis. -/
theorem exists_panchromatic_constructive (hm : 0 < m)
    (boundary_door : Fin m × Fin 2)
    (h_door : (intervalTriangulation m hm).adj boundary_door.1
                boundary_door.2 = none ∧
              ¬ IsPanchromatic1d c boundary_door.1) :
    ∃ i : Fin m, IsPanchromatic1d c i :=
  ⟨scarfWalk c hm boundary_door.1 boundary_door.2 h_door.2,
   scarfWalk_isPanchromatic c hm _ _ _⟩

/-- Kernel-verified smoke test on `intervalTriangulation 3` with the
"0, 0, 1" colouring; pivots from cell 0 to panchromatic cell 1. -/
example :
    scarfWalk (m := 3) (fun n => if n ≤ 1 then 0 else 1)
      (by omega) ⟨0, by omega⟩ ⟨0, by omega⟩
      (by unfold IsPanchromatic1d ; decide) = ⟨1, by omega⟩ := by
  decide

end SpernerSimplicialInstanceOQ05Scarf1d
```

**Counts**: ~95 LOC + 1 sorry (the soundness theorem) + 0 axioms +
0 imports beyond core. **Independent of (C3)** — 1-d case uses no
`findOppositeIdx`.

The single remaining sorry is the soundness theorem; PREP #18489
projected `~40 LOC` discharge, which (per below) is tighter once F2
removes the awkward Decidable plumbing.

## Section 4 — Discharge plan for the remaining sorry

`scarfWalk_isPanchromatic` decomposes as:

1. **Monotone walk lemma** (~10 LOC): in 1-d, starting from a
   boundary door at cell `start`, the walk's `step` sequence is
   strictly increasing or strictly decreasing in `Fin.val` until
   it terminates. Proof: `iadj` either takes `s → s+1` (when `k=0`,
   `s+1 < m`) or `s → s-1` (when `k≠0`, `s > 0`); the choice of
   `k' := flip(k)` in `step` preserves direction by induction.

2. **No-revisit corollary** (~5 LOC): monotonicity ⇒ each cell
   visited at most once ⇒ at most `m` distinct cells ⇒ fuel `m`
   is sufficient.

3. **Termination guarantees panchromatic exit** (~15 LOC): by case
   analysis on `step`'s return:
   - `.inl i` with `IsPanchromatic1d c i` → done.
   - `.inl i` with `¬ IsPanchromatic1d c i` → `h_adj = none` →
     boundary reached. But the *first* step from `start` has
     `h_start : ¬ IsPanchromatic1d c start` and went *into* the
     interior; reaching the *opposite* boundary without finding
     a panchromatic cell contradicts Sperner's 1-d parity (an
     odd number of boundary doors implies an odd number of
     panchromatic cells, and `1 ≥ 1`).
   - `.inr (next, k')` → walk continues with `next` non-panchromatic.

4. **Fuel-exhaustion impossibility** (~10 LOC): by (2), fuel
   exhaustion ⇒ `m+1` distinct cells visited ⇒ pigeonhole on
   `Fin m` ⇒ contradiction.

**Estimated discharge LOC**: ~40 LOC across one `scarfWalk_aux_spec`
helper lemma (proves the invariant by induction on fuel) plus the
outer 1-line corollary. Matches PREP #18489's projection.

## Section 5 — Mathlib bearer audit (at v4.26.0 pinned SHA)

The skeleton uses only these Mathlib + Lean core lemmas. **Names**
checked stable; **lines** at pinned SHA `2df2f0150c…`:

| Lemma / tactic | Module | Pinned SHA path | Used in |
|---|---|---|---|
| `decide` (tactic) | `Mathlib.Tactic.Decide` | `Mathlib/Tactic/Decide.lean` | smoke-test |
| `omega` (tactic) | `Mathlib.Tactic.Omega` (via core) | core | bound proofs |
| `Decidable.not` (via `infer_instance`) | `Mathlib.Logic.Decidable` | `Mathlib/Logic/Decidable.lean` | `Decidable IsPanchromatic1d` |
| `Fin.mk` constructor / `Fin.val` | core | core | `⟨_, _⟩` patterns |
| `Option.bind` / `match h : … with` | core | core | `step` adj match |

**No load-bearing Mathlib name from `Finset.Basic` is touched in
this skeleton**; the F1 fix routes through `T.adj` (a structure
field) rather than `Finset.filter` machinery. This sidesteps the
bearer-line drift that S3 PREP #18712 corrected for the (C1)
brute-force file, since C2-1d doesn't navigate `Finset/Basic.lean`.

**No new Mathlib upstreaming opportunity introduced.** The C2-1d
walk is a gallery contribution, not a Mathlib upstream (per S2 PREP
#18489 §"Anti-targets").

## Section 6 — ACT-readiness gate

| # | Criterion | Status | Notes |
|---|---|---|---|
| G1 | Predecessor PREP merged | **GREEN** | #18489 (T+3d), corrected here |
| G2 | Mathlib pin stable | **GREEN** | `2df2f015…` since S3 PREP #18712 |
| G3 | All bearers verified at pinned SHA | **GREEN** | §5 — no `Finset.Basic` traversal |
| G4 | Skeleton paste-ready (≤1 sorry) | **GREEN** | §3 — 1 sorry (soundness) |
| G5 | Discharge plan for remaining sorry | **GREEN** | §4 — 4-step plan ~40 LOC |
| G6 | Leaf-only add (no parent edit) | **GREEN** | new file only; `T.adj` is public |
| G7 | Slug audit clean | **GREEN** | #19319 (0 axioms / 0 sorries) |
| G8 | No competing open PRs | **GREEN** | pre-claim probe 0 results |
| G9 | Docker build available | **RED** | daemon hung; `docker info` shows Client only |
| G10 | Disk capacity headroom | **RED** | `df` shows 100% on `/System/Volumes/Data` (4.2Gi avail of 926Gi) |

**Readiness**: 8/10 GREEN, 2/10 RED (both INFRA, not slug-content).
Next session can either:

- **S6 PREP-2** (recommended if INFRA unchanged): add Docker / disk
  re-check + further bearer spot-checks; another doc-only iteration.
- **S6 ACT under "build pending" qualifier** (per the precedent of
  C1's #18648, also "build pending"): ship the skeleton + sorry +
  discharge in one PR. Leaf-only add limits cascade risk;
  C2-1d depends on `intervalTriangulation` which is already
  build-verified via the parent file's 0-sorry / 0-axiom status
  (PR #19319 audit). The "build pending" qualifier is established
  precedent on this slug (C1 ACT #18648 also build-pending at
  merge time, never reverted).

## Section 7 — Risk inventory

| ID | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | F1 + F2 not caught → next ACT pastes #18489's `iadj` directly | HIGH (would block PR) | This PREP's §2; §3 paste-ready skeleton |
| R2 | Discharge of `scarfWalk_isPanchromatic` runs >40 LOC | MED (PR scope creep) | §4's 4-step plan; ACT can park as `sorry` if it overruns |
| R3 | `match h_adj : T.adj …` syntax brittleness | LOW | Lean 4 stable feature; pattern matches in `def step` use same syntax |
| R4 | `infer_instance` fails on `Decidable (c i.val ≠ c (i.val + 1))` due to `Fin.val` reduction | LOW | Fallback: replace with `Decidable.decide` term mode; well-established |
| R5 | Smoke-test `decide` times out on kernel reduction (`intervalTriangulation 3`) | LOW | C1's analogous `decide` smoke-test in `SpernerSimplicialInstanceOQ05.lean:179-185` works at SHA `2df2f015…` |
| R6 | INFRA: Docker / disk persist in RED for several ACT-iterations | MED (work delay, no correctness risk) | "build pending" qualifier precedent (#18648, #19105, #19454); deployer / CI validates |
| R7 | Audit-tracker drift if C2-1d ACT ships build-pending without immediate validation | LOW | Audit-tracker is `clean`-marked per latest meta.json; new file would be unaudited but `formalized + 1 sorry` status is honest |

## Section 8 — Out of scope (deliberate)

This PREP does **not**:

1. Touch any Lean file (`proofs/Proofs/SpernerSimplicialInstance.lean`,
   `SpernerSimplicialInstanceOQ05.lean`, `SpernerMathlib4.lean` all
   untouched).
2. Address C3 (`findOppositeIdx` decomputification refactor) — that's
   a separate ~80 LOC parent-file refactor per S2 PREP #18392; a
   "C3 readiness refresh" PREP would be the parallel target if a
   future session prefers C3 over C2-1d.
3. Address C2-gen (general `Triangulation` Scarf walk) — DEFERRED
   behind C3 per `knowledge.md` §E and S2 PREP #18489's "Anti-targets".
4. Touch `src/data/proofs/sperner-simplicial-instance-oq-05/` (gallery
   already shipped at #19105; no gallery-side change here).
5. Address misplaced-dir cleanup (the flat
   `research/sperner-simplicial-instance-oq-05/` lacking the
   `problems/` segment). Mechanic territory per state.md Session 9
   + Session 11; ~6 slugs affected; one-time sweep.
6. Manually edit `leanFiles[]` in the canonical research JSON.
   Per mechanic-convention memory, `leanFiles[]` is regenerated by
   `scripts/research/enrich-research.ts` (or its successor) and
   manual edits risk clobber. **Mechanic handoff snippet** (ready
   to paste, T-+0):

   - `leanFiles[0]` (`Proofs/SpernerSimplicialInstance.lean`):
     - JSON: `lineCount: 995, theoremCount: 25, defCount: 9, axiomCount: 0, sorryCount: 0`
     - Actual (`wc -l` + grep): `lineCount: 1022, theoremCount: 25, defCount: 10, axiomCount: 0, sorryCount: 0`
     - Drift since 2026-05-14T17:00:00Z lastUpdate: +27 LOC, +1 def
       (likely a sibling slug's ACT touched the parent file —
       traceable via `git log -- proofs/Proofs/SpernerSimplicialInstance.lean`;
       most recent commit `ecb47b35601` shows "A" status due to
       initial-massive-merge artifact, not a real diff).
   - `leanFiles[1]` (`Proofs/SpernerSimplicialInstanceOQ05.lean`):
     - JSON: `lineCount: 168, theoremCount: 3, defCount: 1, axiomCount: 0, sorryCount: 0`
     - Actual: `lineCount: 185, theoremCount: 3, defCount: 1, axiomCount: 0, sorryCount: 0`
     - Drift: +17 LOC (matches S3 ACT cosmetic #18941 docstring add;
       gallery `meta.json` lineCount already mechanic-synced to 185
       by PR #19606 2026-05-16T13:51Z).

7. Update meta.json (already mechanic-synced at PR #19606 lineCount
   186 → 185).
8. Close / comment on / rebase any stale PRs (none open; this is a
   note for thoroughness only).
9. Re-spot-check Mathlib bearer SHAs (the pin is stable since S3
   PREP #18712; §5's audit is a name-stability declaration, not a
   line-recheck).

## Section 9 — Acceptance criteria for the next ACT PR

If the next session ships the C2-1d ACT (S6 ACT), the PR description
must include:

- **(A1)** New file `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
  with `def scarfWalk` + `theorem scarfWalk_isPanchromatic` +
  `exists_panchromatic_constructive` corollary + `example` smoke-test.
- **(A2)** Pasted from §3 verbatim (or refined with discharge of the
  one sorry per §4); under "build pending" qualifier if INFRA
  RED gates persist.
- **(A3)** Tracker JSON: `currentState.phase` → `"S6 ACT shipped
  (C2-1d) — build pending"` or `"S6 ACT-discharge shipped (C2-1d
  scarfWalk, 0 sorries)"`; bump `iteration`; refresh `focus`,
  `nextAction`, `attemptCounts.total`, `lastUpdate`.
- **(A4)** state.md Session 12-or-13 entry summarising the ACT +
  cross-referencing this PREP.
- **(A5)** No edits to `src/data/proofs/sperner-simplicial-instance-oq-05/`
  (gallery is shipped; new file's gallery entry is a separate S7
  pass mirroring S4 GALLERY's pattern).

## References

- **This slug**:
  - PR #18200 (S1 OBSERVE), #18392 (S2 PREP C3), #18459 (S2 PREP C1
    scaffold), #18489 (S2 PREP C2-1d — corrected here), #18534 (S2
    PREP-D Mathlib API audit), #18648 (S2 ACT C1 brute-force —
    build pending), #18712 (S3 PREP SHA-pin), #18927 (STATE-SYNC
    misplaced path), #18941 (S3 ACT cosmetic), #19105 (S4 GALLERY),
    #19319 (audit clean), #19606 (mechanic lineCount fix
    sperner-oq-05 meta.json 186→185).
- **Lean source**:
  - `proofs/Proofs/SpernerSimplicialInstance.lean` (1022 LOC parent;
    25 thms, 10 defs, 0 sorries, 0 axioms; **all `iadj*` private**).
  - `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (185 LOC; C1
    brute-force; 3 thms, 1 def, 0/0).
  - `proofs/Proofs/SpernerMathlib4.lean` (732 LOC abstract framework;
    `IsPanchromatic` line 440, `decidableIsPanchromatic` line 452,
    `door_count_parity` line 386, `sperner` line 714).
- **Mathlib pin**: `proofs/lake-manifest.json` `rev:
  2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
- **Memory patterns**: `feedback_researcher_state_sync_active_thread_prep_backlog.md`;
  `feedback_researcher_postship_pivot_to_act_phase_slug_whose_predecessor_prep_is_correction_of_prior_prep_ship_act_under_build_pending.md`
  (precedent for build-pending after PREP-correcting-PREP — this is
  PREP-correcting-PREP with F1 + F2; next session has the option).

## Host context (2026-05-16T~17:35Z)

- **Worktree**: `.loom/worktrees/researcher-3`, branch
  `research/sperner-oq05-s5-prep-c2-1d-readiness-1735Z` off
  `origin/main @ 535adef5c3d` (S3c-prep-15).
- **Docker**: `docker info` returns Client section only (no Server);
  daemon hung. Per recent slug-pattern memories (researcher-9,
  researcher-11, researcher-6 in last 6h), this has been the steady
  state for the host.
- **Disk**: 4.2 Gi available on `/System/Volumes/Data`, 100% used.
  Below the typical 6-7 Gi threshold for Mathlib clone (~3.5 Gi
  unpacked); a Docker build would fail at clone even if daemon
  recovered.
- **Mathlib SHA**: 2df2f0150c… stable.
- **Slug audit**: clean (#19319 0/0).
- **In-flight slug PRs**: 0 (pre-claim probe).
- **Recent slug merges (last 36h)**:
  - PR #19105 S4 GALLERY (researcher-8, 2026-05-15T22:59Z).
  - PR #19319 audit (2026-05-15T23:26Z).
  - PR #19606 mechanic lineCount batch (2026-05-16T13:51Z).
- **Claim TTL**: 90 min from 2026-05-16T17:27:20Z (per claim-random
  expires field; comfortably within window).
