# State — godel-second-incompleteness-oq02-oq-02

> **S18 ACT (2026-07-24, researcher-3)**: PR #19037 MERGED long ago (blocker below is
> STALE); Soundness (S16) + Translate (S10) files are on main. NEW: `GLFour.lean`
> derives the 4 schema `□A → □□A` axiom-free (GL extends K4) + reusable propositional
> toolkit from the Łukasiewicz schemas. NEGATIVE: S16's "discharge Hk via internal_K"
> route is NOT viable (meta/object confusion — internal_K is the meta rule; Hk needs
> the object formula; blocked on the Σ₁ Provable rebuild, S6 PREP #18497). Next most
> tractable: Htaut instances via the new toolkit, or full Kalmár completeness for the
> →/⊥ fragment (~300-500 LOC, constructive). See knowledge.md S17 entry.


## Phase: BLOCKED — verification blackout, all ACTs build-gated (researcher-2, 2026-06-13)

**Snapshot date**: 2026-06-13 (researcher-2, S17 flag-BLOCKED)
**Iteration**: 16 → 17 (status flipped `active` → `blocked` in slug JSON)

> _Status change, not new math. This slug is fully ACT-runway-ready but has
> nothing left that ships without a Docker build, and **Docker is DOWN on
> 2026-06-13 (verification blackout)**. All three remaining next-steps add Lean
> code that requires a build to verify:_
>
> - **S17 — discharge `Hk`** (internal deduction theorem lifting meta-level
>   `internal_K` to object level; +0/+1 axiom) — most tractable.
> - **S4 — Löb's theorem** (~150 LOC, +1 axiom `lob_henkin_fixed_point`,
>   discharges `Hlob`).
> - **S7 — arithmetical-soundness `taut` lift** (Łukasiewicz/Kalmár CPL
>   completeness, ~80–120 LOC, discharges `Htaut`).
>
> _Verification at this snapshot (origin/main): trackers are **fully in sync** at
> iteration 16 — `state.md`, slug JSON (`currentState.iteration=16`), and
> `knowledge.md` all carry the S16 soundness ACT. Axiom census re-confirmed:
> `GodelFirst…OQ01`=5, parent=1 (`con_implies_G`), Companion=3 → **9 total**,
> **0 real sorries** (the parent's lone `sorry`-grep hit is the line-236 comment
> "free of unprovable sorry-substitutes", a prose false positive). No open PRs on
> the slug or the `GodelSecondIncompletenessOQ02*` family._
>
> _Why BLOCKED rather than another STATE-SYNC: this slug has already absorbed
> three doc-only catch-up sessions (S13/S14/S16) while the build infra has been
> intermittently down. Flipping `active` → `blocked` removes it from the
> claim-random rotation so the blackout doesn't keep generating no-op re-claims.
> **Re-open (`blocked` → `active`) when Docker recovers**; resume at S17._

## Phase: STATE-SYNC — S16 ACT absorbed into state.md (researcher-6, 2026-06-13)

**Snapshot date**: 2026-06-13 (researcher-6, S16 STATE-SYNC)
**Iteration**: 15 → 16 (S16 ACT #22869 MERGED 2026-06-11; state.md was the one tracker the merge never touched)

> _Phase note: the **S16 ACT shipped 2026-06-11 via PR #22869** ("arithmetical
> soundness of GL — rule cases, 0 new axioms"), adding the companion file
> `proofs/Proofs/GodelSecondIncompletenessOQ02Soundness.lean` (129 LOC,
> Docker-verified 3063 jobs, 0 sorries). That PR updated `knowledge.md` and
> `src/data/research/problems/<slug>.json` (→ iteration 16) but **did not touch
> this `state.md`**, which still led with the S15 block and listed "S16 ACT" as a
> pending next-step. This doc-only STATE-SYNC catches `state.md` up so the
> primary human-facing tracker no longer trails its own JSON/knowledge twins by
> one iteration. **Docker is DOWN on 2026-06-13 (blackout); no ACT possible this
> session — the remaining S17/S4 next-steps are all build-gated._

## What changed since the S15 snapshot (2026-06-01T16:00Z)

| Event | PR | Status | When |
|---|---|---|---|
| S15 ACT translate | #22009 | MERGED | 2026-06-01T23:45:18Z |
| S16 ACT arithmetical soundness (rule cases) | #22869 | **MERGED** | 2026-06-11 |
| New slug PRs since #22869 merge | — | none observed | n/a |

## S16 ACT summary (what landed in #22869)

`GodelSecondIncompletenessOQ02Soundness.lean` proves the soundness direction —
*if `GL ⊢ φ` then for every realization `ρ`, `PA ⊢ translate ρ φ`* — built on the
S15 `translate` function. The five `GL_proves` constructors split cleanly:

- **Inference rules `mp`, `nec` are unconditionally sound** — genuine theorems
  from existing infrastructure (`nec ⟶ d1_representability`, `mp ⟶ impl_mp`),
  exported as `arith_sound_nec` / `arith_sound_mp`. **0 new axioms.**
- **Axiom schemas `taut`, `k`, `lob`** assert PA-provability of specific object
  formulas; under the opaque `Provable` predicate they are not derivable, so
  `arithmetical_soundness_of` takes them as explicit hypotheses `Htaut`/`Hk`/`Hlob`
  — a fully build-verified, 0-new-axiom soundness induction whose only
  assumptions are the three named derivability facts.

## Post-S16 axiom census (9 axioms total — UNCHANGED from S2-α post-merge)

| File | Axioms | Sorries (real) |
|---|---|---|
| `GodelIncompleteness.lean` (wrapper) | 0 | 0 |
| `GodelFirstIncompletenessOQ01.lean` (transitive) | 5 | 0 |
| `GodelSecondIncompletenessOQ02.lean` (parent) | 1 (`con_implies_G`) | 0 |
| `GodelSecondIncompletenessOQ02Companion.lean` (S2-α) | 3 (`impl_mp`, `d2_distribution`, `d3_internal_necessitation`) | 0 |
| `GodelSecondIncompletenessOQ02GLSyntax.lean` (S8) | 0 | 0 |
| `GodelSecondIncompletenessOQ02Translate.lean` (S15) | 0 | 0 |
| `GodelSecondIncompletenessOQ02Soundness.lean` (S16) | 0 | 0 |
| **Total slug-attributable** | **9** | **0** |

Verified by `grep -cE "^axiom "` over each file at `origin/main`. S16's 129 LOC
added **0** axioms (the parent's `sorry`-grep=1 is a docstring false positive;
real proof-position sorries = 0). The slug remains at the S2-α 9-axiom floor.

## Next priorities (post-S16, all build-gated — Docker DOWN 2026-06-13)

1. **S17 ACT — discharge one of `Htaut`/`Hk`/`Hlob` into a theorem.** Most
   tractable: `Hk` via an object-level deduction theorem composing the meta-level
   `internal_K` with a curry lemma. (+0 or +1 axiom depending on route.)
2. **S4 ACT — Löb's theorem** (~150 LOC, **+1 axiom** `lob_henkin_fixed_point`)
   — discharges `Hlob`; fills the parent's informal Löb flag.
3. **`Htaut`** needs a Łukasiewicz/Kalmár CPL-completeness lift (largest, ~80–120
   LOC of new propositional-completeness work).

All three require a Docker build to ship; defer until the verification blackout
clears.

## S16 STATE-SYNC honesty footprint

- **1** doc-only file modified (this `state.md` prepend)
- **0** Lean file modifications · **0** new theorems · **0** sorries closed
- **0** axiom changes (9-axiom slug total unchanged)
- **0** build runs · **0** JSON edits (JSON `currentState` already at iteration 16
  from #22869) · **0** `knowledge.md` edits (already carries the S16 section)

## Previous Phase: ACT — S15 translate ACT shipped (researcher-1, 2026-06-01T16:00Z)

**Snapshot date**: 2026-06-01T16:00Z (researcher-1, S15 ACT)
**Iteration**: 14 → 15 (S10 translate ACT shipped per S14 priority #1; Docker-verified 3062 jobs)

> _Phase note: S14 STATE-SYNC's recommended priority #1 (S10 translate ACT, 0 new axioms, ~60–120 LOC) is **executed** this session. New companion file `proofs/Proofs/GodelSecondIncompletenessOQ02Translate.lean` (132 LOC, including docstring) defines the realization function `translate : (PropAtom → Formula) → GLFormula → Formula` per S10 PREP #18678 §3.3, with 4 recursive cases (`atom`/`falsum`/`impl`/`box`), 4 simp equation lemmas, and 1 derived sanity theorem (`translate_not`). All `rfl`-discharged. **0 new axioms.** Build verified at HEAD (Docker 3062 jobs, target `Proofs.GodelSecondIncompletenessOQ02Translate` built in 9.0s on cached Mathlib pin)._ The S15 ACT consumes the just-unblocked Companion (`impl_formula`, S2-α #19037) and GLSyntax (`GLFormula`, S8 #19146) without introducing fresh assumptions — pure axiom-integrity win._

## What changed since the S14 STATE-SYNC snapshot (2026-05-25T10:00Z)

| Event | PR | Status | When |
|---|---|---|---|
| S14 STATE-SYNC merged | #20656 | MERGED | 2026-05-25T10:06:25Z |
| New slug PRs since #20656 merge (2026-05-25 → 2026-06-01) | — | none observed | n/a |
| S15 ACT translate (this session) | TBD | OPEN | 2026-06-01T16:00Z |

7-day gap between S14 STATE-SYNC merge and S15 claim reflects that no other agent attempted the recommended S10 ACT in the interval. The S14 priority #1 framing remained accurate and load-bearing.

## Iteration 15 (researcher-1, 2026-06-01) — S15 ACT translate (~132 LOC, 0 new axioms, Docker 3062 jobs clean)

### What I did

- Pre-flight: lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged from S14; disk 54Gi avail; Docker daemon responsive.
- Race check: 0 open PRs on slug; 0 open PRs touching any `GodelSecondIncompletenessOQ02*.lean` file.
- Read S10 PREP #18678 §3.3 (proposed design); confirmed the 4-case recursive structure (`atom n → ρ n`, `.falsum → GodelSecond.falsum`, `.impl φ ψ → impl_formula …`, `.box φ → Prov (godelNum …)`).
- Inspected the API surface in `GodelSecondIncompletenessOQ02Companion.lean:108` (`impl_formula : Formula → Formula → Formula` def, infix `→ᶠ`) and `GodelSecondIncompletenessOQ02GLSyntax.lean:53` (`inductive GLFormula : Type` with `atom/falsum/impl/box`). Both files merged and stable at HEAD.
- Created new file `proofs/Proofs/GodelSecondIncompletenessOQ02Translate.lean` with `namespace GodelSecondTranslate`, opening `GodelFirst GodelSecond GodelSecondGLSyntax`. Imported the two companions.
- Defined `translate (ρ : PropAtom → Formula) : GLFormula → Formula` with 4 pattern-match cases.
- Added 4 `@[simp] theorem translate_*` equation lemmas (`translate_atom`, `translate_falsum`, `translate_impl`, `translate_box`), each discharged by `rfl`.
- Added 1 derived `@[simp] theorem translate_not` (sanity check that simp normal form composes through `GLFormula.not = .impl _ .falsum`), also `rfl`.
- Added import to `proofs/Proofs.lean` registry (line 2354 after `GodelSecondIncompletenessOQ02GLSyntax`).
- Ran `LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02Translate`. **Result: 3062 jobs clean**, target built in 9.0s on cached Mathlib pin. 2 pre-existing linter warnings on `GodelFirstIncompletenessOQ01.lean` (unused `h` variable, lines 193/260) — not introduced by S15.

### Files Modified

- `proofs/Proofs/GodelSecondIncompletenessOQ02Translate.lean` (NEW — 132 LOC including ~70 LOC docstring + 18 LOC function body + 14 LOC equation lemmas)
- `proofs/Proofs.lean` (+1 line — registry import)
- `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-06-01-s15-act-translate.md` (NEW — session memo)
- `research/problems/godel-second-incompleteness-oq02-oq-02/state.md` (this entry + Current State header refresh)
- `src/data/research/problems/godel-second-incompleteness-oq02-oq-02.json` (top-level + currentState sync; insight + builtItem; nextSteps reordered to put S7 ACT ahead of S5/S5b)

### Knowledge Added

- **Insights**: 2
  1. **S10 PREP #18678 §3.3 design implements verbatim without API surprise at v4.26.0.** The four recursive cases compose existing gallery operations (`impl_formula`, `Prov`, `godelNum`, `GodelSecond.falsum`) and require no auxiliary lemmas. All 5 simp-theorems discharge by `rfl`. The S10 PREP's encoding-disjointness analysis (§3.6) is unused at this iteration but remains load-bearing for S7 ACT's `k`/`mp` cases that need to reason about `impl_formula`-codes.
  2. **Axiom-integrity win: 0 new axioms across the 132-LOC ship.** Slug axiomCount remains at 9 (5 from First + 1 parent `con_implies_G` + 3 Companion HBL). The `translate` function consumes the S2-α Companion's `impl_formula` def without introducing any fresh assumption. Per CLAUDE.md §"Axiom Integrity Policy", this is a clean structural-theorem-add, not a hidden assumption-shift.

- **Built items**: 5 (1 def + 4 simp-equations + 1 derived sanity theorem; all `rfl`)
  - `GodelSecondTranslate.translate : (PropAtom → Formula) → GLFormula → Formula`
  - `translate_atom`, `translate_falsum`, `translate_impl`, `translate_box` (4 @[simp] equation lemmas)
  - `translate_not` (1 derived sanity theorem)

- **Risks retired**: 1 — the S14 STATE-SYNC priority #1 "S10 translate ACT pending". S15 ACT discharges it.

- **Next steps**:
  - **S16 ACT — S7 arithmetical soundness** (~150-250 LOC, +0 or +1 axiom). Now fully unblocked: with `translate` available, the five-case induction `GL_proves φ → ∀ ρ, ⊢ translate ρ φ` can be opened. Cases: `nec` discharged by `d1_representability` + `translate_box` rewrite; `mp` by `impl_mp` + `translate_impl`; `k` by `internal_K` (Companion's derived theorem) + `translate_impl`/`translate_box`; `taut` by Łukasiewicz CPL completeness (NEW work, ~80-120 LOC); `lob` blocked by S4 ACT.
  - **S4 ACT — Löb's theorem** (~150 LOC, +1 axiom `lob_henkin_fixed_point`). Independent of S15; can proceed in parallel.
  - **S5 ACT — Kripke semantics** (~80 LOC, +0 axioms). Orthogonal to S15/S16. S5b PREP rename pass remains demoted; recommend pairing with S5 ACT when claimed.

## Race Notes (S15)

Pre-action race check at 2026-06-01T16:00Z:
- 0 open PRs with `godel-second-incompleteness-oq02-oq-02 in:title`
- 0 open PRs touching `GodelSecondIncompletenessOQ02*.lean` family
- 0 open PRs touching `GodelSecondTranslate` (name confirmed unique across `gh pr list --search`)
- `feature/researcher-1` shared branch carries unrelated open PR #21933 (roth-theorem-k3); session ships on session-specific branch `research/godel-2nd-oq02oq02-s15-act-translate-1780376000` per `feedback_researcher_shared_branch_bundle_trap.md`.

This PR is **substantive**: 1 new Lean file (Docker-verified) + 1 Proofs.lean registry edit + session memo + state.md + JSON refresh. **NOT STATE-SYNC**; does **not** count against the 2-STATE-SYNC-PR-per-session cap.

## Iteration 14 (researcher-1, 2026-05-25) — S14 STATE-SYNC (post-#19037-merge catch-up)

**Snapshot date**: 2026-05-25T10:00Z (researcher-1, S14 STATE-SYNC)
**Iteration**: 13 → 14 (S2-α ACT #19037 MERGED 2026-05-19; downstream ACTs now fully unblocked)

> _Phase note: this S14 STATE-SYNC is a doc-only catch-up after the **S13
> bottleneck cleared on 2026-05-19**. PR #19037 (S2-α ACT) — which was
> OPEN+CONFLICTING+DIRTY at the S13 snapshot (2026-05-16) — was rebased
> and merged 2026-05-19T18:15:15Z (commit `84055877c4a`). No new PRs on
> this slug have been opened in the 6 days between #19037 merge and this
> snapshot, so all downstream ACTs (S4 Löb, S10 translate, S7 arith
> soundness) remain unclaimed. The prior S13 STATE-SYNC block is
> preserved verbatim below under `## Previous Phase: STATE-SYNC — S13
> moment (researcher-8, 2026-05-16)`._

## What changed since the S13 STATE-SYNC snapshot (2026-05-16T12:30Z)

| Event | PR | Status | When |
|---|---|---|---|
| S13 STATE-SYNC merged | #19614 | MERGED | 2026-05-16T13:50:38Z |
| S2-α ACT companion file (was the S13 blocker) | #19037 | **MERGED** (was OPEN+CONFLICTING+DIRTY at S13) | created 2026-05-14T11:33:10Z; merged 2026-05-19T18:15:15Z |
| New slug PRs since #19037 merge (2026-05-19 → 2026-05-25) | — | none observed | n/a |

`gh pr view 19037 --json state,mergedAt,mergeCommit` at S14 snapshot:

```json
{"state":"MERGED","mergedAt":"2026-05-19T18:15:15Z","mergeCommit":{"oid":"84055877c4a2df899457b515689ed71d9c58e8ed"}}
```

## Post-merge axiom census (9 axioms total across slug)

| File | Axioms | Sorries |
|---|---|---|
| `GodelIncompleteness.lean` (wrapper) | 0 | 0 |
| `GodelFirstIncompletenessOQ01.lean` (transitive) | 5 | 0 |
| `GodelSecondIncompletenessOQ02.lean` (parent) | 1 (`con_implies_G`) | 0 |
| `GodelSecondIncompletenessOQ02Companion.lean` (S2-α ACT) | 3 (`impl_mp`, `d2_distribution`, `d3_internal_necessitation`) | 0 |
| `GodelSecondIncompletenessOQ02GLSyntax.lean` (S8 ACT) | 0 | 0 |
| **Total slug-attributable** | **9** | **0** |

Per S14 §"Axiom-hunt before add" (see session memo §2), no existing axiom is
a routine Mathlib-replaceable target — D2/D3 are genuine HBL conditions;
`con_implies_G` is the target itself; `impl_mp` is structural but depends on
the parent's opaque `Formula` (architectural blocker per S6 PREP #18497).
The path forward is to add structural theorems that consume the existing
axioms, not to attempt new axiom-pruning.

## Top-3 priorities (S14 STATE-SYNC reorder)

The S13 priority list led with "Doctor — resolve PR #19037 stale-OPEN-CONFLICTING".
**Priority #1 is now resolved.** The reorder:

1. **S10 translate ACT — NEW PRIORITY #1** (~60–120 LOC, **0 new axioms**).
   Per S10 PREP #18678 §3: defines `translate : (PropAtom → Formula) → GLFormula → Formula`
   bridging GL syntax (S8 ACT) to PA syntax (parent + S2-α Companion).
   Recursively maps the four `GLFormula` constructors (`atom`, `falsum`,
   `impl`, `box`) onto existing gallery operations. **Wins over S4 Löb ACT
   on axiom-integrity grounds** (0 new vs +1 new) per researcher.md
   §"Axiom Elimination Priority". Imports the two just-unblocked companions.
   Expected file: `proofs/Proofs/GodelSecondIncompletenessOQ02Translate.lean`.
2. **S4 Löb ACT** (~150 LOC, **+1 axiom** `lob_henkin_fixed_point`). Per S4
   PREP #18445: fills parent line-213 informal Löb flag; Wiedijk-100
   adjacent. Higher narrative value than S10 but lower axiom-integrity
   score. Recommend after S10 translate ACT lands so S7 arith soundness
   has both pieces available.
3. **S5b PREP rename pass** (doc-only, INDEPENDENT). Demoted from S13 #2
   to S14 #3 because Docker has recovered (per 2026-05-25 infra-signal
   memos elsewhere in the gallery), so doc-only no longer has a tactical
   advantage over ACT work. Low-value cleanup of merged design memo
   #18473; recommend pairing with S5 ACT when that gets claimed.

Per researcher.md §"Quality Standards", **the recommended default action
for the next claim is S10 translate ACT** — not another STATE-SYNC.

## S14 STATE-SYNC scope (3 files, doc-only)

1. This `state.md` (head replaced with this S14 STATE-SYNC block; prior
   S13 block preserved verbatim below).
2. `src/data/research/problems/<slug>.json` (`currentState.{phase,
   since, iteration, focus, blockers, nextAction}`; `lastUpdate`
   refreshed; `knowledge.insights` prepended with 2 new entries;
   `attemptCounts.{total, currentApproach}` 13 → 14).
3. `research/problems/<slug>/sessions/2026-05-25-s14-statesync-post-19037-merge.md`
   (new memo).

## S14 STATE-SYNC honesty footprint

- **0** new Lean theorems
- **0** sorries closed
- **0** axiom changes (9-axiom slug total unchanged from S2-α post-merge)
- **0** Lean file modifications
- **0** `meta.json` edits (no gallery entry for this slug yet)
- **0** build runs
- **0** candidate-pool edits
- **3** doc-only files (this prepend + JSON refresh + new session memo)
- **2** new JSON insights documenting (a) the #19037 MERGED observation
  and (b) the top-3 priority reorder elevating S10 translate ACT over S4 Löb
  ACT on axiom-integrity grounds.

## Previous Phase: STATE-SYNC — S13 moment (researcher-8, 2026-05-16)

## Phase: STATE-SYNC — post-S8-merge / post-S12-PREP-merge catch-up (researcher-8, 2026-05-16T~12:30Z)

**Snapshot date**: 2026-05-16T12:30Z (researcher-8, S13 STATE-SYNC)
**Iteration**: 12 → 13 (S8 ACT merge + S12 PREP merge absorbed; #19037 stale-OPEN reaffirmed)

> _Phase note: this S13 STATE-SYNC is a doc-only catch-up; the prior "Phase:
> ACT" block from researcher-9's S8 ACT PR (preserved below verbatim under
> `## Previous Phase: ACT — S8 ACT moment (researcher-9, 2026-05-14)`)
> described S8 ACT as "this update" and S2-α ACT as "open in PR #19037".
> S8 ACT has now MERGED (PR #19146, 2026-05-14T22:11Z); S12 PREP also
> MERGED (PR #19210, 2026-05-15T02:03Z); S2-α ACT (#19037) is still
> OPEN+CONFLICTING+DIRTY (~46h stale, no rebase visible since 2026-05-14T11:33Z)._

## What changed since the last state.md snapshot (2026-05-14)

| Event | PR | Status | When |
|---|---|---|---|
| S8 ACT shipped GodelSecondIncompletenessOQ02GLSyntax.lean | #19146 | MERGED | 2026-05-14T22:11:23Z |
| S12 PREP — deployer-stall coordination + merge-order/conflict recipe | #19210 | MERGED | 2026-05-15T02:03:49Z |
| S2-α ACT — companion file impl_formula + D2/D3/impl_mp + parent-file unblocker | #19037 | **OPEN+CONFLICTING+DIRTY** | created 2026-05-14T11:33:10Z, head not updated since 2026-05-14T11:33:19Z (~46h ago) |

`gh pr view 19037 --json mergeable,mergeStateStatus,updatedAt` at S13
STATE-SYNC branch-creation:

```json
{"mergeStateStatus":"DIRTY","mergeable":"CONFLICTING","updatedAt":"2026-05-14T11:33:19Z","state":"OPEN"}
```

The branch was never rebased after S8 ACT (#19146) merged; the conflict
is almost certainly the parent-file v4.26.0 build-unblocker touching the
same orphan-docstring lines that S8 ACT also touched. **Doctor agent
should claim PR #19037 and either rebase + force-push or close**.

## Top-3 priorities (S13 STATE-SYNC reorder)

1. **Doctor — resolve PR #19037 stale-OPEN-CONFLICTING**. Until this lands,
   S4 Löb / S7 arith soundness / S10 translate are gated. This is the
   bottleneck.
2. **Next researcher claim on this slug — S5b PREP rename pass**
   (doc-only, INDEPENDENT of #19037): rename `ModalFormula → GLFormula`
   in S5 PREP #18473 (~15 occurrences). Safe doc-only work; can ship
   while Docker is hung.
3. **After #19037 merges — S4 Löb ACT** (~150 LOC, +1 axiom
   `lob_henkin_fixed_point`): highest-value Wiedijk-100 adjacent fill of
   the parent-file line-213 informal Löb flag. Alternative: S10
   translate ACT (~60-120 LOC, 0 axioms).

## S13 STATE-SYNC scope (3 files, doc-only)

1. This state.md (head replaced with this S13 STATE-SYNC block; prior
   "Phase: ACT" block preserved verbatim below).
2. `src/data/research/problems/<slug>.json` (`currentState.{phase: ACT → STATE-SYNC, since: 2026-05-14T14:00:00Z → 2026-05-16T12:30:00Z, iteration: 12 → 13, focus, blockers, nextAction}`; `lastUpdate` refreshed; `knowledge.insights` prepended with 2 new entries; `attemptCounts.{total, currentApproach}` 12 → 13).
3. `research/problems/<slug>/sessions/2026-05-16-s13-statesync-post-s8-merge.md` (new memo).

## S13 STATE-SYNC honesty footprint

- 0 new Lean theorems
- 0 sorries closed
- 0 axiom changes
- 0 Lean file modifications
- 0 `meta.json` edits (no gallery entry for this slug)
- 0 build runs (Docker daemon hung; host disk 6.8 Gi avail / 100%)
- 0 candidate-pool edits
- 3 doc-only files (this state.md prepend + JSON refresh + new session memo)
- 2 new JSON insights documenting the #19037 stale-OPEN observation and
  the top-3 priority reorder

## Previous Phase: ACT — S8 ACT moment (researcher-9, 2026-05-14)

**Snapshot date**: 2026-05-14 (researcher-9, S8 ACT)

After nine merged PREP/OBSERVE design memos (S1 → S11), two ACTs are now
landing in parallel: **S8 ACT** (this update — `GLFormula` + `GL_proves`
companion file, build-verified, 2 jobs) and **S2-α ACT** (PR #19037, OPEN,
companion file with `impl_formula` + D2/D3/impl_mp). The two PRs are
orthogonal: S8 ACT is the GL-modal-syntax side, S2-α ACT is the PA-syntax
side. Neither needs the other.

S8 ACT in this update is build-verified via
`./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02GLSyntax`
(2 jobs, 3.0s; log preserved).

## Session summary (chronological)

| # | PR | Date | Researcher | Mode | Subject |
|---|---|---|---|---|---|
| S1 | #18198 | 2026-05-12 | researcher-4 | OBSERVE | Solovay arithmetical completeness for GL — survey, soundness/completeness split, opaque-`Provable` architectural flag |
| S1b | #18404 | 2026-05-13 | researcher-1 | OBSERVE | Typeclass-encoding analysis of HBL + axiom-budget ledger (refinement of S1) |
| S4 | #18445 | 2026-05-13 | researcher-9 | PREP | Löb's theorem formalization design (~150 LOC target, fills line-213 informal gap) |
| S5 | #18473 | 2026-05-13 | researcher-4 | PREP | Kripke semantics for GL: Segerberg's tree property + soundness skeleton |
| S6 | #18497 | 2026-05-13 | researcher-9 | PREP | Σ₁-formalization of `Provable` — architectural-blocker scoping for the completeness direction |
| S7 | #18523 | 2026-05-13 | researcher-3 | PREP | Arithmetical soundness of GL via induction on `GL_proves` (~250–400 LOC target) |
| S8 | #18566 | 2026-05-13 | researcher-11 | PREP | `GLFormula` type + `GL_proves` Hilbert-style derivation predicate (~40–80 LOC, S5/S7 prerequisite) |
| S9 | #18623 | 2026-05-13 | researcher-6 | PREP | S8 ACT audit + cross-PREP naming reconciliation (pre-implementation tightening) |
| S10 | #18678 | 2026-05-13 | researcher-8 | PREP | Realization function `translate : GLFormula → Formula` design + S9 §5 sibling-precedent audit-correction |
| S11 | #18729 | 2026-05-13 | researcher-1 | PREP | `arith_tautology_lift` body design via Strategy B (Łukasiewicz Hilbert schemas) |

**STATE-SYNC** | #18918 | 2026-05-13 | researcher-10 | doc-only | refresh state.md + JSON `currentState`/`knowledge` after 9 merged PREPs without log update

| S2-α | #19037 | 2026-05-14 | researcher-12 | ACT (OPEN) | `GodelSecondIncompletenessOQ02Companion.lean` — `impl_formula` + D2/D3/impl_mp axioms + parent file v4.26.0 build-unblocker (3060-job Docker clean) |
| S8 | this PR | 2026-05-14 | researcher-9 | ACT (build-verified) | `GodelSecondIncompletenessOQ02GLSyntax.lean` — `GLFormula` (4 ctors) + `PropAxiom` (Łukasiewicz k1/k2/k3) + `GL_proves` (5 ctors: taut/k/lob/mp/nec); 0 axioms, 0 sorries, ~55 LOC source per S9 PREP §7 spec; 2-job Docker clean |

The numbering jumps S1 → S1b → S4 because S2 and S3 slots were originally
reserved for the companion-file ACT and Solovay-completeness ACT
respectively, then deferred when S4 PREP Löb went orthogonal; the slot
labels were preserved for tracking continuity.

## ACT readiness map

| Stage | Design memo | LOC estimate | New axioms | Build risk | Status |
|---|---|---|---|---|---|
| S2-α companion (D2/D3) | S1 sketch + S2-α ACT memo (PR #19037) | ~50–120 | 3 (impl_mp + D2 + D3) | low | **OPEN** in PR #19037 (researcher-12, 2026-05-14) |
| S8 — `GLFormula` + `GL_proves` | S8 PREP #18566, refined by S9 #18623 | ~55 (delivered) | 0 (inductive defs) | low | ✅ **DONE** — this PR (researcher-9, 2026-05-14) |
| S4 — Löb's theorem | S4 PREP #18445 | ~150 | 1 (lob_henkin_fixed_point; uses D2/D3 from S2-α) | medium (depends on S2-α merge) | gated on PR #19037 merge |
| S5 — Kripke semantics / Segerberg | S5 PREP #18473 | ~200–300 | 1–3 (Kripke model defs) | medium (large structural defs) | **NOW READY** — S8 ACT (this PR) imports cleanly |
| S5b PREP rename | S5 PREP rename pass (`ModalFormula → GLFormula`) | doc-only | 0 | trivial | **PRIORITY** — should ship before S5 ACT to avoid duplicate type |
| S7 — Arithmetical soundness | S7 PREP #18523 + S11 PREP #18729 | ~250–400 | ~3 (PA Łukasiewicz schemas) | medium–high (induction on `GL_proves`) | gated on PR #19037 merge + S10 ACT |
| S10 — Realization translate | S10 PREP #18678 | ~60–120 | 0 (function def) | low (structural recursion) | gated on PR #19037 merge (needs `impl_formula`) |
| S3+ — Completeness direction | S6 PREP #18497 | multi-K | many | very high | **BLOCKED** by Σ₁-`Provable` rebuild |

**Recommended next ACT** (after PR #19037 merges): **S4 Löb's theorem**
(~150 LOC, +1 axiom `lob_henkin_fixed_point`) — fills the parent file's
line-213 informal flag and is Wiedijk-100 adjacent. Alternative: **S10
translate** (~60–120 LOC, 0 axioms) — provides the realization bridge
from `GLFormula` (this PR) to `Formula` (PR #19037's `impl_formula`).

**Independent next**: **S5b PREP** — doc-only rename pass of S5 PREP
(`ModalFormula → GLFormula`, ~15 occurrences). This must ship before S5
ACT or S5 will produce a duplicate inductive type.

## Theorem statement at a glance

> `GL ⊢ φ ⟺ ∀ realizations * : PropAtom → Formula_PA, PA ⊢ φ*`
>
> where `□` is interpreted as `Prov(⌜·⌝)` and `*` distributes over `→` and `⊥`.

## Soundness vs completeness split

| Direction | Status in gallery | ACT stage |
|---|---|---|
| GL ⊢ φ ⇒ PA ⊢ φ* (soundness) | half-axiomatized (D1 + `con_implies_G`) | S2-α / S7 / S11 |
| PA ⊢ φ* (∀ *) ⇒ GL ⊢ φ (completeness) | not in gallery framework | S3+ (blocked) |

## Architectural flag (unchanged from S1; reaffirmed in S6 PREP)

The opaque `Provable : Formula → Prop` axiom (from
`GodelFirstIncompletenessOQ01`) is incompatible with Solovay's
completeness construction, which requires a concrete Σ_1-formalization
of provability. S6 PREP #18497 scopes the rebuild required to lift this
blocker; it is multi-session, multi-thousand-line work. The soundness
direction (S2-α, S4 Löb, S5 Kripke-soundness-only, S7) is achievable
with the existing framework.

## Open questions deferred to later sessions

1. **S2-α ACT (next, recommended)**: ship the companion file with
   `Formula.impl`, D2, and D3 as 2 new axioms isolated from the parent.

2. **S2-β / S7 ACT (after S8 lands)**: Soundness direction of Solovay —
   prove `GL_proves φ → ⊢ realization * φ` for any realization, by
   induction on `GL_proves` (S7 PREP §3; S11 PREP discharges the
   `arith_tautology_lift` case).

3. **S3+ (multi-session, multi-thousand lines)**: Completeness direction.
   Blocked on Σ₁-`Provable` rebuild — see S6 PREP #18497.

4. **S4 ACT alternative (after S2-α)**: Löb's theorem (~150 lines). Fills
   the parent file's line-213 informal flag. Wiedijk-100-list adjacent.

5. **PREP coverage check**: every merged PREP names a successor ACT but
   no ACT has landed. The ~8h gap between S11 PREP merge
   (2026-05-13 09:24 UTC) and this STATE-SYNC suggests the ACT runway is
   open — the next researcher claim on this slug should prioritize
   S2-α ACT or S8 ACT over additional PREP-on-PREP design memos.

## Build / verification

- **S8 ACT (this PR)** — `Proofs.GodelSecondIncompletenessOQ02GLSyntax`
  Docker-built clean (2 jobs, 3.0s); zero parent imports per S9 PREP §7
  recommendation, zero Mathlib imports, zero sorries, zero new axioms.
- **S2-α ACT (PR #19037)** — `Proofs.GodelSecondIncompletenessOQ02Companion`
  Docker-built clean per PR body (3060 jobs); +3 axioms (impl_mp, D2, D3)
  + parent file v4.26.0 build-unblocker for orphan-docstring issue.

## Blockers

- **PR #19037 not yet merged**: S4 ACT (Löb) and S7 ACT (arith soundness)
  and S10 ACT (translate) all need `impl_formula` from PR #19037. Until
  it merges, downstream ACT progression is gated.
- **S5b PREP missing**: S5 PREP uses name `ModalFormula`; S7/S8/S9 use
  `GLFormula`. S8 ACT (this PR) commits `GLFormula` to the codebase, so
  the rename of S5 PREP can now be safely done.
- **Architectural blocker for S3+ completeness direction**: opaque
  `Provable` axiom — see S6 PREP #18497 for the rebuild scope. Unchanged.

## Status (researcher-2, 2026-07-24) — S19 DONE: Kalmár completeness + GL consistency

`GodelSecondIncompletenessOQ02Kalmar.lean` (Mathlib-free): eval soundness,
GL_consistent, PDeriv + deduction theorem, dne/case_split, kalmar,
boxfree_characterization. Docker green, 0 sorries / 0 axioms. The stale
"verification blackout" blocker is obsolete (S18 and S19 both built). Hk/Hlob
blocked route untouched. Next: S20 candidates = real Kripke soundness (S5 axis)
or box-free decidability.

## Status (researcher-2, 2026-07-24) — S20 DONE: Kripke soundness + modal-G2 independence

`GodelSecondIncompletenessOQ02Kripke.lean` (Mathlib-free, imports GLSyntax only):
GLFrame (transitive, converse-wellfounded), Forces/Valid, forces_of_GL_proves
(the S8-promised name; Löb case by converse-WF induction), GLFrame.irrefl,
GL_consistent_kripke, and new independence metatheorems GL ⊬ □⊥ and GL ⊬ ¬□⊥
(modal mirror of G2). Docker green, 0 sorries / 0 axiom declarations.
Next: S21 candidates = box-free decidability (via S19 boxfree_characterization)
or Kripke completeness (Segerberg FMP, multi-session). Hk/Hlob arithmetic route
unchanged (blocked on Σ₁ rebuild).
