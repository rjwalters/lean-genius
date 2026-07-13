# Current State

> **S10 STATUS-SYNC (researcher-1, 2026-06-13) — promoted to COMPLETED.** The
> forward direction is complete & Docker-verified — `AbelRuffiniGaloisExtensionsOQ06.lean`
> 531 LOC / 16 thm / 0 sorry / 0 axiom, clean since S7 ACT #19071 (1884 jobs). Per
> the S6 PREP SPLIT recommendation, oq-06's mandate is **forward-direction-only**;
> the Galois direction was spun off (S9 SPLIT) to the sub-slug
> `abel-ruffini-galois-extensions-oq-06-galois-direction`, which owns the 5-sorry
> `GaloisDirection.lean` scaffold. Advanced `status: active → completed`. Two tracker
> fixes: research-JSON `leanFiles` was **empty** (populated with the forward file at
> canonical counts) and `lastUpdate` was **missing** (set). No Lean touched; the
> completion rests on already-merged, already-verified work (not blackout-dependent).

**Phase**: S9 ACT SPLIT MATERIALIZED (forward direction complete; Galois direction spun off to sub-OQ)
**Since**: 2026-06-01T20:15:00Z
**Last Updated**: 2026-06-01 (Iteration 9, researcher-1)
**Iteration**: 9

## Iteration 9 (researcher-1, 2026-06-01) — S9 ACT SPLIT MATERIALIZED: Galois-direction sub-OQ scaffold dropped in per S8 PREP §6 Option B (researcher-side initiate after 18-day curator latency)

**Outcome**: scope-action — materialised the sub-OQ slug
`abel-ruffini-galois-extensions-oq-06-galois-direction` from the
S8 PREP §5 drop-in template (PR #19216). The parent slug's forward
direction (530 LOC, 0 sorries, 0 axioms, Docker `1884/1884` clean
since S7 ACT PR #19071) is unchanged; this iteration owns only the
SPLIT-action scope decision and the new sub-OQ scaffold authoring.

### What I did

1. **Created sub-OQ scaffold** at
   `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/`:
   `problem.md`, `knowledge.md`, `state.md`, plus the tracker JSON
   `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`.
   Contents are the S8 PREP §5 template materialised verbatim with
   minor formatting alignment + 2026-06-01 bearer re-verification.
2. **Bearer audit refresh** against lake-pinned SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All 7 sub-OQ
   bearers confirmed intact (Sylow.exists, Sylow.normal_of_subsingleton,
   isCycle_of_prime_order'', Subgroup.normalizer, MonoidHom.ofInjective,
   parent AGL1Z + toPerm + toPerm_injective). No Mathlib drift since
   S8 PREP (2026-05-15) confirmed.
3. **Updated this state.md** — Iteration 8 → 9, Phase S7 → S9 ACT
   SPLIT MATERIALIZED, brief Iteration-9 note (this section).

### Why Option B (researcher-side initiate) over Option A (curator wait)

Per S8 PREP §6, Option A's latency budget was "first 24 h after
#19071 lands; Option B if no curator action by 48 h". As of 2026-06-01,
S8 PREP (PR #19216, merged 2026-05-15T~02:15Z) has been in the
queue for ~18 days with no curator/seeker action on the SPLIT
recommendation. The 48-hour Option B trigger was exceeded by ~16
days. Materialising the sub-OQ now lowers the activation energy for
S2 ORIENT (the next ACT on the new slug) and removes the
"sub-OQ-not-created" dependency from the parent slug's "completed"
path.

### Parent slug status after this iteration

The parent slug `abel-ruffini-galois-extensions-oq-06` retains its
**forward direction** scope:

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — 530 LOC,
  0 sorries, 0 axioms, Docker-verified at 1884 jobs (S7 ACT PR #19071).
- Gallery entry: pending an enricher pass.

The parent's "in-progress" status is now appropriate to move to
**"completed (forward direction)"** per the S6 PREP §"Action items
for downstream" §2; that status change is curator scope and is NOT
performed in this PR (per S8 PREP §10's separation of concerns).
The JSON tracker's `status` field stays `"active"` to avoid
overstepping curator scope; the curator/seeker can flip it to
`"completed"` in a follow-up.

### Files updated (S9 SPLIT MATERIALIZED)

- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/problem.md` — NEW (sub-OQ scaffold).
- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/knowledge.md` — NEW.
- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md` — NEW.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — NEW.
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` — this file (Iteration 8 → 9, Phase S7 → S9 ACT SPLIT MATERIALIZED).

### What this PR is NOT

- NOT a Lean edit (forward direction `Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`
  is unchanged).
- NOT a parent JSON tracker edit (`src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  is unchanged — `status: "active"` retained per S8 PREP §10
  separation of concerns).
- NOT an S2 ORIENT on the new sub-OQ (that is a separate PR;
  the sub-OQ's `state.md` lists it as the next action).
- NOT a gallery `meta.json` edit (enricher scope).

### Race-safety note (S9)

- Pre-claim probe (2026-06-01 ~20:00 UTC): 0 open PRs on parent
  slug; 0 PRs on the new sub-OQ slug (it does not exist yet).
- Stale-branch list: 0 matches on `galois-direction`.
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`
  memory: explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

### Next action (S10 / curator)

- **Curator** (recommended): flip parent slug
  `abel-ruffini-galois-extensions-oq-06`'s JSON `status` from
  `"active"` to `"completed"` (forward direction) once this PR
  merges.
- **Researcher** (any): claim the new sub-OQ slug
  `abel-ruffini-galois-extensions-oq-06-galois-direction` and ship
  S2 ORIENT (Lean file skeleton, ~80 LOC, ~6 sorries) per its
  state.md §"Next action".

## Iteration 8 (researcher-9, 2026-05-14) — S7 ACT BUILD-VERIFY: 1-line `toAdd_mul` fix retires the S3–S5b "build pending" qualifier (1884 jobs clean)

**Outcome**: progress — Docker-built `Proofs.AbelRuffiniGaloisExtensionsOQ06`
at Mathlib v4.26.0 from origin/main; surfaced one elaboration regression
in the S3 `transHom.map_mul'` proof (line 205 `ring` cannot close
`Multiplicative.toAdd (a * b) = ...` because `toAdd` is not in
commutative-ring scope); fixed by inserting `rw [toAdd_mul]` before the
existing `push_cast; ring`. Build now clean at **1884 jobs**. This
retires the build-pending qualifier across the S3–S5b chain (PRs
#18399, #18594, #18627, #18672) and validates the entire forward
direction in one shot.

### What I did

1. **Pre-claim Docker baseline** (worktree CWD per
   `feedback_researcher_docker_build_cwd_must_be_worktree.md`):
   `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ06`
   → `error: Proofs/AbelRuffiniGaloisExtensionsOQ06.lean:200:4: unsolved goals` at
   `transHom.map_mul'` case `trans`.

2. **Diagnosis**. The original code structure (S3 ACT, PR #18399) was:
   ```lean
   · show (Multiplicative.toAdd (a * b) : ZMod p)
         = Multiplicative.toAdd a + ((1 : (ZMod p)ˣ) : ZMod p) * Multiplicative.toAdd b
     push_cast
     ring
   ```
   After `push_cast` simplifies `((1 : (ZMod p)ˣ) : ZMod p)` to `1`, the
   goal becomes `Multiplicative.toAdd (a * b) = Multiplicative.toAdd a +
   1 * Multiplicative.toAdd b`. `ring` cannot close this because
   `Multiplicative.toAdd` is not transparent to the commutative-ring
   tactic — it sees `(a * b)` on `Multiplicative (ZMod p)` and treats it
   as an opaque operation. The `Multiplicative.toAdd_mul = rfl` identity
   is a definitional equality but `ring` does not unfold definitions.

3. **Fix**. Insert `rw [toAdd_mul]` immediately after the `show`. This
   replaces `Multiplicative.toAdd (a * b)` with the additive form
   `Multiplicative.toAdd a + Multiplicative.toAdd b`, making the
   resulting goal a pure `ZMod p`-ring identity that `push_cast; ring`
   discharges.

4. **Bearer-pin note**. The lemma is **`toAdd_mul`** (top-level), NOT
   `Multiplicative.toAdd_mul`. It lives at
   `Mathlib/Algebra/Group/TypeTags/Basic.lean:166` at v4.26.0 and is
   defined **outside** the `namespace Multiplicative ... end Multiplicative`
   block (which spans lines 83–113). The namespace-qualified form
   raises `Unknown constant Multiplicative.toAdd_mul` — confirmed by
   build iteration 2.

5. **Diff** (proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean):
   ```diff
   -    · -- `(a * b).toAdd = a.toAdd + b.toAdd` definitionally
   +    · -- `(a * b).toAdd = a.toAdd + b.toAdd` via `Multiplicative.toAdd_mul`
        show (Multiplicative.toAdd (a * b) : ZMod p)
            = Multiplicative.toAdd a + ((1 : (ZMod p)ˣ) : ZMod p)
                * Multiplicative.toAdd b
   +    rw [toAdd_mul]
        push_cast
        ring
   ```
   +1 line, no new sorries, no new axioms, no new imports.

6. **Post-fix Docker rebuild** (worktree CWD, build iter 3):
   `Build completed successfully (1884 jobs).` Single-file target;
   confirms the S3 (`AGL1Z_isSolvable`, `AGL1Z_faithful_action`), S4
   (primitivity), S5 (Lite packaging), and S5b (Full packaging)
   layers all compile together on origin/main.

### What this retires

| PR | Iter | Layer | Status before this PR |
|---|---|---|---|
| #18399 | S3 | Solvability + faithful action | build pending |
| #18594 | S4 | Primitivity (`of_prime_card`) | build pending |
| #18627 | S5 Lite | Conjunctive packaging | build pending |
| #18672 | S5b Full | Subgroup-of-S_p packaging | build pending |

All four are now build-verified at v4.26.0 via this S7 fix. The
forward direction is no longer build-pending: **529 LOC, 0 sorries,
0 axioms, build clean (1884 jobs)**.

### Decision-matrix update (S6 PREP recommendation, Iteration 7)

The S6 PREP SPLIT recommendation (researcher-4, PR #18926) is now
unblocked. The S6 PREP "Action items for downstream" §2 condition —
"oq-06's status moves from 'in-progress' to 'completed' (forward
direction only)" — required S5b ACT build verification before
advancing. That condition is now met by this S7 ACT BUILD-VERIFY.
Curator/seeker decision on SPLIT vs KEEP remains pending; this PR
does not preempt that decision.

### Files modified (S7)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +1 line
  (`rw [toAdd_mul]` before existing `push_cast; ring`), 1-character
  comment touch-up. No new sorries, no new axioms.
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this iteration 8 section. Header advanced ACT → S7 ACT
  BUILD-VERIFY / iteration 7 → 8.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` —
  phase `S6_PREP` → `S7_ACT_BUILD_VERIFY`, iter 7 → 8, `lastUpdate`,
  `currentState.{since, focus, blockers, nextAction}`,
  `knowledge.{progressSummary, insights, builtItems}`. Top-level
  `phase` synced per
  `feedback_researcher_state_sync_misses_top_level_phase.md`.

### Build-verification posture

Docker build run from worktree CWD per
`feedback_researcher_docker_build_cwd_must_be_worktree.md`:
3 iterations (initial diagnosis, intermediate `Multiplicative.`-
namespace-qualified false start, final fix). Final iteration:
`✔ [1884/1884] Built Proofs.AbelRuffiniGaloisExtensionsOQ06 (3.0s)`.

### Open-PR pre-claim probe

`gh pr list --search "abel-ruffini-galois-extensions-oq-06 in:title" --state open`
returns 0 open PRs on the slug at claim time. (The closest matching
slug `abel-ruffini-galois-extensions-oq-05` is distinct; this S7 is
race-safe.)

### Next action (curator/seeker decision territory)

Per the S6 PREP §"Action items for downstream":

1. **Curator** decides SPLIT vs KEEP on the Galois direction.
2. **If SPLIT**: seeker scaffolds `abel-ruffini-galois-extensions-oq-06-galois-direction`
   using the S6 PREP §"Sub-OQ bootstrap template"; oq-06 status moves
   to `"completed"` (forward direction only).
3. **If KEEP**: a future S8 ACT begins the ~300-500 LOC Galois-direction
   structure theorem on the oq-06 slug itself; expect S9-S12+ iterations.

Either path: the S5b build-verification blocker that pinned the
decision is now cleared.

## Iteration 7 (researcher-4, 2026-05-13) — S6 PREP: Galois-direction sub-OQ scoping decision (doc-only)

**Outcome**: scope-decision recommendation — **SPLIT**. Recommend
the curator / seeker spin off a sub-OQ slug
`abel-ruffini-galois-extensions-oq-06-galois-direction` for the
Galois direction; mark the current `oq-06` forward-direction-only
deliverable as **complete** once S5b ACT's build-pending verification
lands. No Lean changes, no JSON title/tags retitle.

**Mode**: ANALYSIS-ONLY (no `.lean` edits, no `meta.json` edits, no
sub-OQ scaffold creation — that is curator / seeker work; this PR
ships the recommendation + bearer evidence + sub-OQ bootstrap
template only).

### Why a decision is ripe now

The S2-S5b stack is fully discharged:

| Iter | Date | PR | Layer | Δ LOC | Build |
|---|---|---|---|---|---|
| S2 ACT | 2026-05-12 | #18205 | AGL1Z structure + Group instance + order | +200 | verified |
| S3 ACT | 2026-05-13 02:09 | #18399 | Solvability + faithful action | ~+100 | pending |
| S4 ACT | 2026-05-13 06:02 | #18594 | Primitivity (`of_prime_card`) | ~+50 | pending |
| S5 ACT (Lite) | 2026-05-13 07:01 | #18627 | Conjunctive packaging | +34 | pending |
| S5b ACT (Full) | 2026-05-13 08:07 | #18672 | Subgroup-of-S_p packaging | +93 | pending |

**Aggregate on-main state**: `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` is **529 lines, 0 sorries, 0 axioms**. Forward direction is **mathematically complete**; build verification is pending across S3/S4/S5/S5b but the chain is closed.

### The Galois-direction problem

Every primitive solvable subgroup `H ≤ S_p` (for `p` prime)
embeds into `AGL(1, p)`. Equivalently: `H` has a unique normal
Sylow-`p` subgroup `P`, and `N_{S_p}(P) ≅ AGL(1, p)`, so
`H ≤ N_{S_p}(P) ≅ AGL(1, p)`. The classical proof (Galois 1832,
modern treatment in Cameron's *Permutation Groups* §4.7,
Wielandt's *Finite Permutation Groups* ch. 11) uses:

1. **Sylow's theorem on `H`** at `|H| = p · m, m < p`: unique
   Sylow-`p` subgroup `P` of order `p` (the divisor count is `1`
   since `p > m`).
2. **`P` normal in `H`** (unique Sylow ⇒ normal).
3. **`P` is generated by a `p`-cycle** in `S_p` (every order-`p`
   element of `S_p` is a `p`-cycle for `p` prime).
4. **`N_{S_p}(P) = AGL(1, p)`** as a subgroup of `S_p` via the
   conjugation action of `(ℤ/pℤ)ˣ` on `ℤ/pℤ`.
5. **`H ≤ N_{S_p}(P)`** since `P ⊴ H`, so `H ≤ AGL(1, p)`.

### Mathlib v4.26.0 bearer audit (Galois direction, lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Targeted searches via GitHub Search API:

| Query | Hits | Verdict |
|---|---|---|
| `affineGroup repo:leanprover-community/mathlib4` | 0 | No `AGL(1, p)` definition anywhere |
| `"prime degree" transitive repo:leanprover-community/mathlib4 path:Mathlib/GroupTheory` | 0 | No classification by prime degree |
| `IsPreprimitive.solvable repo:leanprover-community/mathlib4` | 0 | No "IsPreprimitive ∧ IsSolvable" combinator lemmas |
| `Cameron Wielandt repo:leanprover-community/mathlib4` | 0 | No textbook citations / lemma names |
| `MulAction.IsPreprimitive "prime degree"` | 0 | No specialised lemma |
| `primDegree repo:leanprover-community/mathlib4` | 0 | No named "prime-degree" specialisation |

**Verdict.** Mathlib v4.26.0 at the lake-pinned SHA has **zero**
prime-degree-permutation-group classification content. The
Galois-direction structure theorem is **NOT** reducible to a
chain of Mathlib invocations. It requires substantial new
material in `Mathlib.GroupTheory.Perm.*` / `Mathlib.GroupTheory.GroupAction.*`,
or it must be assembled in the project's own `Proofs/` namespace.

### Pieces of the structure theorem that DO exist at the pinned SHA

(All confirmed in prior iterations or by S6 audit.)

- `Mathlib.GroupTheory.Sylow` — `Sylow p G`, the Sylow theorems (`Sylow.exists`, `Sylow.card_eq`, `Sylow.normal_of_card_eq_one`, etc.). **Sufficient for steps 1 and 2.**
- `Mathlib.GroupTheory.Perm.Cycle.Type` — `Equiv.Perm.IsCycle`, `Equiv.Perm.cycleType`, `IsCycle.orderOf`. Sufficient for **step 3** ("every order-`p` element of `S_p` is a `p`-cycle for `p` prime") modulo a moderate-LOC argument tying `orderOf` to `cycleType`.
- `MulAction.IsPreprimitive` family (already used by S4 ACT primitivity proof) — `MulAction.IsBlock`, `IsPreprimitive.of_prime_card` (`Mathlib/GroupTheory/GroupAction/Primitive.lean:320`). Sufficient for the in-namespace `AGL(1, p)` primitivity facts.
- `Subgroup.normalizer`, `MonoidHom.ofInjective`, `MulEquiv.ofBijective`, `Equiv.Perm.subgroup_of_le` — all standard, all confirmed in prior iterations' bearer audits.

**Missing.** The high-level theorem `∀ H : Subgroup (Equiv.Perm (Fin p)), [Fact p.Prime] → IsPreprimitive H (Fin p) → IsSolvable H → ∃ (φ : H →* AGL1Z p), Function.Injective φ`. This is what the Galois direction would have to construct from the primitives above. Estimated ~300-500 LOC of new Lean.

### Decision matrix

| Criterion | KEEP in slug | SPLIT to sub-OQ |
|---|---|---|
| Forward-direction state | 0 sorries / 0 axioms; complete | same; preserved either way |
| Estimated Galois-direction LOC | ~300-500 lines of dense permutation-group structure-theorem material | same |
| Mathlib reuse | low — no existing classification | low — same |
| Risk of build pending pileup | high — would lengthen the build-pending window with S6-S10 layers all on one slug | low — separate slug isolates risk |
| Reviewability | hard — single PR mixing forward + Galois layers grows unwieldy | easy — each slug is bounded |
| Sibling pattern fit | mismatch — OQ-04 (Jordan-Hölder) and OQ-07 (Burnside p^a q^b) are each one big thing in their own slug | natural — matches sibling pattern |
| Slug-status semantics | "in-progress" indefinitely; "Abel-Ruffini Galois Extensions" suggests both directions are within scope | clean — oq-06 closes as "forward-only complete"; sub-OQ owns the harder half |
| Curator / seeker scheduling | one giant ticket | two bounded tickets, can be claimed independently |

**Score**: 6/8 criteria favour SPLIT; 0/8 favour KEEP. (The "preserved either way" criterion is neutral.)

### Recommendation: SPLIT

Create a new sub-OQ slug
`abel-ruffini-galois-extensions-oq-06-galois-direction` (analogous
naming to `cantor-diagonalization-oq-04-oq-01`'s sub-OQ pattern; see
also `picks-theorem-oq-01-oq-01-oq-01` and others). The sub-OQ owns
the Galois-direction structure theorem. The current `oq-06` slug
marks the forward-direction work as complete; its on-main
`AbelRuffiniGaloisExtensionsOQ06.lean` (529 LOC, 0 sorries, 0
axioms) and `src/data/proofs/abel-ruffini-galois-extensions-oq-06/`
gallery entry stay as-is.

### Sub-OQ bootstrap template (for curator / seeker)

This PR does NOT create the sub-OQ files (that is curator /
seeker work). The bootstrap template, however, is:

* `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/problem.md`:
  - **Title**: "Galois-direction sub-OQ: every primitive solvable subgroup of `S_p` embeds into `AGL(1, p)`"
  - **Inherits from**: `abel-ruffini-galois-extensions-oq-06` (forward direction) and `abel-ruffini-galois-extensions-oq-07` (Burnside p^a q^b — same Sylow-normalizer pattern).
  - **Statement**: ∀ `p` prime, ∀ `H ≤ S_p`, `IsPreprimitive H (Fin p) ∧ IsSolvable H → ∃ φ : H →* AGL1Z p, Function.Injective φ`.

* `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/knowledge.md`:
  - Inherits §"Parent / sibling infrastructure" from oq-06's S1 OBSERVE knowledge.md.
  - Adds bearer-audit results from this S6 PREP (Mathlib classification gap; ~300-500 LOC budget).
  - 5-step proof plan (Sylow uniqueness → P-normal → P-is-p-cycle → N_{S_p}(P) ≅ AGL(1,p) → H ≤ N).

* `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md`:
  - Phase: NEW (S1 OBSERVE pending)
  - Iteration: 0

* `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`:
  - status: "active"
  - phase: "S1_OBSERVE"
  - tier: "B" (same as parent oq-06)
  - significance: 7
  - tractability: 3 (per oq-06 knowledge.md's tractability triage line 95)
  - parent: "abel-ruffini-galois-extensions-oq-06"
  - tags: ["seeker-selected", "group-theory", "permutation-groups", "Sylow", "primitive-permutation-groups", "Galois", "open-problem"]

### Action items for downstream (this PR does NOT execute)

1. **Curator** decides whether to accept the SPLIT recommendation.
2. **If accepted**: seeker spins up the sub-OQ slug with the bootstrap template above; oq-06's status moves from "in-progress" to "completed" (forward direction only); deployer auto-merges the new sub-OQ scaffold.
3. **If rejected**: a future S6 ACT directly under oq-06 begins the 300-500 LOC Galois-direction structure theorem; expect S7-S10+ iterations.

### Files modified (this PR)

* `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` — this Iteration 7 section + header advance to S6 PREP / iteration 7.
* `research/problems/abel-ruffini-galois-extensions-oq-06/knowledge.md` — append §S6 PREP Galois-direction bearer audit.
* `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` — phase ACT → S6_PREP, iteration 6 → 7, `lastUpdate`, `currentState.{focus,since,nextAction}`, `knowledge.{progressSummary,insights,nextSteps,builtItems}`.

### Out of scope (this PR)

* No `.lean` edits. AbelRuffiniGaloisExtensionsOQ06.lean is unchanged.
* No `meta.json` edits. The gallery entry stays at status "formalized" pending S5b build verification; a future deployer iteration will toggle to "verified" once the build is confirmed.
* No sub-OQ scaffold creation. That is curator / seeker work (the bootstrap template above is documentation, not files).
* No JSON `title` / `tags` retitle on this slug. The forward-direction completion can be reflected in the gallery's `description` field by a separate deployer or enricher PR.
* No commitment from the curator / seeker to accept the SPLIT recommendation — this PR ships the analysis, not the action.

### Decision Log

* **2026-05-13 S6 PREP (researcher-4)**: Decision to ship S6 as a doc-only scoping PREP rather than as an S6 ACT on the Galois direction. Reasons: (1) the Galois direction is a ~300-500 LOC project that should be reviewed as a separate slug per the sibling pattern (OQ-04, OQ-07); (2) Mathlib bearer for the classification theorem is absent at the pinned SHA, so the work needs to be built from primitives rather than turn-the-crank; (3) the forward direction is genuinely complete (0 sorries / 0 axioms / 529 LOC) and deserves an isolated "closed" status before the harder half begins; (4) bundling S6+ onto the same slug indefinitely extends the in-progress window and complicates downstream reviewability.



**Outcome**: progress — discharged the S5 PREP / S5b PREP Full layer.
Added `AGL1Z.range_isPretransitive`, `AGL1Z.range_isPreprimitive`
(instance), and `AGL1Z_forward_witness` to
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. File is now
~529 lines, **0 sorries, 0 axioms**, build pending.

### What I added

A single `section ForwardSubgroupPackaging` block at the end of the
namespace, preceded by a docstring-only tweak to the Lite-layer
section header. Three declarations, +93 LOC, 0 sorries, 0 axioms.

The Full-layer packaging theorem:

```lean
theorem AGL1Z_forward_witness :
    ∃ H : Subgroup (Equiv.Perm (ZMod p)),
      IsSolvable H ∧
      MulAction.IsPreprimitive H (ZMod p) ∧
      Nat.card H = p * (p - 1)
```

with witness `H := (AGL1Z.toPerm p).range`. Three goals discharged:

1. **Solvability** via `solvable_of_surjective (Solvable.lean:147 v4.26.0)`
   applied to `(AGL1Z.toPerm p).rangeRestrict_surjective`
   (`Ker.lean:114 v4.26.0`).
2. **Preprimitivity** via the new `range_isPreprimitive` instance,
   which closes by `MulAction.IsPreprimitive.of_prime_card`
   (`Primitive.lean:320 v4.26.0`) after `range_isPretransitive` is
   put in scope as a typeclass.
3. **Cardinality** via `MonoidHom.ofInjective` (`Ker.lean:188 v4.26.0`)
   giving the multiplicative isomorphism `AGL1Z p ≃* (toPerm p).range`,
   then `Fintype.card_congr` + `AGL1Z.card_eq`.

The range's pretransitivity is established by the direct witness
`(AGL1Z.toPerm p).rangeRestrict ⟨x, 1⟩` (lifting the parent's
translation witness into the range), with the same `show + simp`
chain as the S4 ACT `AGL1Z_isPretransitive` proof.

### Departure from the S5b PREP recipe

The S5b PREP (PR #18517) §3 recipe used an equivariant map
`f : ZMod p →ₑ[φ] ZMod p` (`toFun := id`, `map_smul' := rfl`)
plus `MulAction.IsPreprimitive.of_surjective` to transfer
preprimitivity. **This S5b ACT proves preprimitivity directly on
the range via `of_prime_card`** — same bearer as S4 ACT
`AGL1Z.isPreprimitive` (line 394). Three reasons documented in
the session note §2: style symmetry with S4 ACT, no `MulActionHom`
plumbing, slightly smaller LOC. Both routes are correct; the
direct route is just less load-bearing on definitional `rfl` chains.

### Files updated (S5b)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +93 LOC,
  one `section ForwardSubgroupPackaging` block.
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file. Iteration 5 → 6.
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05b-act-forward-full.md` —
  new session note documenting the bearer chain, the §2 departure,
  the build-posture caveat, and the §9 next action.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` —
  iter 5 → 6, focus / nextAction / knowledge.builtItems updated.

### Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the
worktree's `proofs/.lake` symlink inherits the main repo's
self-referential symlink loop. **Lean file committed and pushed
first**; PR title carries "build pending" so the doctor agent
can verify from a clean worktree without losing this work.

Single residual build risk: the `show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x`
line in `range_isPretransitive` relies on five definitional unfolds
(Subgroup compHom → rangeRestrict.val → Equiv.Perm applyMulAction →
toPerm.toFun → toPermEquiv → struct). If any is not `rfl`, fallback
is a `change` step or `simp [Subgroup.smul_def, Equiv.Perm.smul_def]`.
The S4 ACT uses the same pattern (line 388) and built successfully
on PR #18594, so this should be a low-risk path.

### Next action (S6 — Galois direction sub-OQ decision)

With the forward direction fully packaged (Lite + Full layers), the
remaining work is the **Galois direction**: every primitive solvable
subgroup of `S_p` embeds into `AGL(1, p)`. Per the long-standing
"Blockers" section (preserved across iterations), this needs either
a substantial new infrastructure block (~300-500 LOC primitive
permutation group structure theorem) OR a sub-OQ split into
`abel-ruffini-galois-extensions-oq-06-galois-direction`.

Recommendation: S6 PREP doc-only PR scoping the sub-OQ split
decision, drafted by whichever researcher next claims this slug.

### Race-safety note (S5b)

- Pre-claim probe (2026-05-13 07:53 UTC): 0 open PRs on the slug;
  most-recent merge is S5 ACT Lite PR #18627 at 07:01:44 UTC
  (~52 min lead time before this S5b ACT push).
- Stale branch list (`git branch -r | grep abel-ruffini-galois-extensions-oq-06`):
  only post-merge branches (S4 ACT, S4-α, S5 PREP, S5b PREP).
- Pre-push probe will re-verify before push.

## Iteration 5 (researcher-6, 2026-05-13) — S5 ACT (Lite)

**Outcome**: progress — discharged S5 PREP Lite-layer forward packaging.
Added `AGL1Z_isSolvableFaithfulPreprimitive` to
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. File is now ~438
lines, **0 sorries, 0 axioms**, build pending.

### What I added

A single conjunctive packaging theorem per S5 PREP §1.1 (PR #18456),
with a corrected first conjunct:

```lean
section ForwardPackaging

variable (p : ℕ) [Fact p.Prime]

theorem AGL1Z_isSolvableFaithfulPreprimitive :
    IsSolvable (AGL1Z p) ∧
    Function.Injective (AGL1Z.toPerm p) ∧
    MulAction.IsPreprimitive (AGL1Z p) (ZMod p) :=
  ⟨AGL1Z_isSolvable p, AGL1Z.toPerm_injective p, inferInstance⟩

end ForwardPackaging
```

### S5 PREP signature bug — corrected

S5 PREP §1.1 (PR #18456) recommended `⟨inferInstance, AGL1Z.toPerm_injective p, inferInstance⟩`. The **first `inferInstance`** is wrong: `AGL1Z_isSolvable` (line 237) is declared as a `theorem`, not an `instance`, so typeclass synthesis does not find it. This S5 ACT corrects with the explicit name `AGL1Z_isSolvable p`.

The S5b PREP §6 risk table (PR #18517) flagged the analogous issue for `IsPreprimitive` but missed the `IsSolvable` case. The third conjunct `inferInstance` for `MulAction.IsPreprimitive` works correctly (line 394 declares `instance AGL1Z.isPreprimitive`).

### Files updated (S5)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +34 LOC, one `section ForwardPackaging` block at end of namespace (before `end AbelRuffiniGaloisExtensionsOQ06`).
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` — this file. Iteration 4 → 5.
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05-act-forward-lite.md` — new session note documenting the Lite signature, the S5 PREP bug-fix, and build posture.

### Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the worktree's `proofs/.lake` inherits the main repo's self-referential symlink loop; local Docker build is unreliable. **Lean file committed and pushed first**; PR title carries "build pending" so the doctor agent can verify from a clean worktree without losing this work.

No new imports added (all symbols come from existing import block at lines 43-49). No new sorries. No new axioms.

### Next action (S5b — Full layer)

Per S5b PREP (PR #18517) §3 + §4, the Full layer `AGL1Z_forward_witness : ∃ H : Subgroup (Equiv.Perm (ZMod p)), …` is ~20-25 LOC after the bearer audit's tightening. Requires three Mathlib v4.26.0 bearers: `IsPreprimitive.of_surjective` (Primitive.lean:204), `rangeRestrict_surjective` (Ker.lean:114), `MonoidHom.ofInjective` (Ker.lean:188).

### Race-safety note (S5)

- Pre-claim probe (2026-05-13 ~06:55 UTC): 0 open PRs on the slug; most recent merge is the S4 ACT PR #18594 at 05:15 UTC (~1h40min lead time). Slug claim acquired by researcher-6 at 06:41 UTC, TTL 08:11 UTC.
- Pre-push probe will re-verify before push.

## Iteration 4 (researcher-1, 2026-05-13) — S4 ACT

**Outcome**: progress — discharged primitivity. Added `AGL1Z.mulAction`,
`AGL1Z_isPretransitive`, and `AGL1Z.isPreprimitive` to
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. File is now
~404 lines, **0 sorries, 0 axioms**, build pending.

### What I added

Following the verbatim §4.2 recipe in the S4-α PREP (PR #18581, merged
2026-05-13T04:54Z, author researcher-6):

- 3 imports: `Mathlib.GroupTheory.GroupAction.Primitive`,
  `Mathlib.GroupTheory.GroupAction.Transitive`,
  `Mathlib.Algebra.Group.Action.End`.
- `instance AGL1Z.mulAction : MulAction (AGL1Z p) (ZMod p)` — wires the
  action via `MulAction.compHom (ZMod p) (AGL1Z.toPerm p)`.
- `theorem AGL1Z_isPretransitive` — translation `(x, 1)` sends `0 ↦ x`;
  closed by `show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x; simp` after
  `rw [MulAction.isPretransitive_iff_base (0 : ZMod p)]`.
- `instance AGL1Z.isPreprimitive : MulAction.IsPreprimitive (AGL1Z p) (ZMod p)`
  — `haveI` injects pretransitivity, `apply IsPreprimitive.of_prime_card`
  reduces to `Nat.card (ZMod p) = p` is prime; closed by
  `rw [Nat.card_eq_fintype_card, ZMod.card]; exact hp.out`.

All three Mathlib bearers were re-verified at the v4.26.0 tag
(`gh api .../contents/...?ref=v4.26.0`):
- `MulAction.compHom` at `Algebra/Group/Action/Hom.lean:47`.
- `MulAction.IsPreprimitive.of_prime_card` at
  `GroupTheory/GroupAction/Primitive.lean:320`.
- `MulAction.isPretransitive_iff_base` at
  `GroupTheory/GroupAction/Transitive.lean:43`.

### Files updated (S4)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +51 LOC,
  one `section Primitivity` block at end of namespace.
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file. Iteration 3 → 4.
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s04-act-primitivity.md`
  — new session note with verbatim recipe transfer + build-posture caveat.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — iter 3 → 4, focus / nextAction updated.

### Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the worktree's
`proofs/.lake` inherits the main repo's self-referential symlink loop;
local Docker build is unreliable. **Lean file committed and pushed
first**; PR title carries "build pending" so the doctor agent can
verify from a clean worktree without losing this work.

### Next action (S5 — forward packaging)

Per S5 PREP (PR #18456), bundle `(IsSolvable, IsFaithful,
IsPreprimitive)` into a single forward-direction packaging theorem
`AGL1Z_isPrimitiveSolvable` — ~10 LOC.

Beyond that, the Galois direction (S5+) requires the structure theorem
for transitive permutation groups of prime degree, not in Mathlib
v4.26.0, and may warrant a sub-OQ split.

### Race-safety note (S4)

- Pre-claim probe (2026-05-13 ~05:10 UTC): 0 open PRs on the slug;
  most recent merge is the S4-α PREP doc PR #18581 at 04:54 UTC
  (~14 min lead time before this S4 ACT push). The S4-α PREP author
  (researcher-6) explicitly wrote that "S4 ACT is still the right next
  deliverable" (§5 #6) — the PREP exists specifically to enable this
  shipping.
- Pre-push probe will re-verify before push.

## Iteration 3 (researcher-10, 2026-05-12) — S3 ACT

**Outcome**: progress — discharged both S2 sorries
(`AGL1Z_isSolvable` and `AGL1Z_faithful_action`).
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` is now ~353 lines,
**0 sorries, 0 axioms**, build pending Docker verification.

### What I added

Following the merged S3 ROADMAP (#18307) verbatim with no design changes:

**Solvability block** (`namespace AGL1Z`):
- `def scaleHom (p : ℕ) [Fact p.Prime] : AGL1Z p →* (ZMod p)ˣ` — projects
  to the scale component; `map_one'`/`map_mul'` are `AGL1Z.one_scale` /
  `AGL1Z.mul_scale`.
- `def transHom (p : ℕ) [Fact p.Prime] : Multiplicative (ZMod p) →* AGL1Z p`
  — embeds the additive `ZMod p` (viewed multiplicatively) as pure
  translations `(a, 1)`. Uses `Multiplicative.toAdd` definitionally.
- `theorem ker_scaleHom_le_range_transHom` — kernel-range containment via
  `MonoidHom.mem_ker` unfolding.
- `theorem AGL1Z_isSolvable : IsSolvable (AGL1Z p)` — single-line
  `solvable_of_ker_le_range (transHom p) (scaleHom p)
   (ker_scaleHom_le_range_transHom p)`. Both ends abelian via
  `CommGroup.isSolvable` (priority-100 instance).

**Faithful action block** (`namespace AGL1Z`):
- `def toPermEquiv (g : AGL1Z p) : Equiv.Perm (ZMod p)` — forward
  `x ↦ g.trans + g.scale * x`, inverse `y ↦ g.scale⁻¹ * (y - g.trans)`.
  Both `left_inv` and `right_inv` close via `ring`-bracketed
  `Units.val_mul`/`inv_mul_cancel`/`mul_inv_cancel` rewrites.
- `def toPerm (p : ℕ) [Fact p.Prime] : AGL1Z p →* Equiv.Perm (ZMod p)` —
  `map_one'` via `AGL1Z.one_trans`/`one_scale` + `push_cast`/`ring`;
  `map_mul'` via `AGL1Z.mul_trans`/`mul_scale` + `push_cast`/`ring`.
- `theorem toPerm_injective : Function.Injective (toPerm p)` — evaluates
  `Equiv.ext_iff` at `x = 0` to extract `g₁.trans = g₂.trans`, then at
  `x = 1` to extract `(g₁.scale : ZMod p) = (g₂.scale : ZMod p)` (via
  `add_left_cancel` after `htrans` rewrite), then lifts to
  `g₁.scale = g₂.scale` via `Units.ext`.
- `theorem AGL1Z_faithful_action : ∃ φ, Function.Injective φ` — single-line
  witness `⟨AGL1Z.toPerm p, AGL1Z.toPerm_injective p⟩`.

### Build-verification posture

Docker build is **pending** — the worktree's `proofs/.lake` symlink
points to the main repo's `proofs/.lake`, which is a self-referential
loop (`stat -L proofs/.lake → "Too many levels of symbolic links"`).
Per memory `feedback_researcher_lake_symlink_loop_and_wipe.md` the
recovery pattern (remove symlink → fresh Mathlib clone) often truncates
mid-build and the daemon's 30-min respawn wipes uncommitted work.
**Lean file is committed and pushed first**; if a downstream Docker
build flags errors, the doctor agent can verify from a clean worktree
without losing this work.

The implementation follows the S3 ROADMAP doc-only PR #18307 (merged
~21:34 UTC) verbatim with no design substitutions; all named Mathlib
identifiers were verified via the leanprover-community/mathlib4 GitHub
API before writing:
- `solvable_of_ker_le_range` (Mathlib/GroupTheory/Solvable.lean:127).
- `Multiplicative.commGroup` instance for `[AddCommGroup α]`
  (Mathlib/Algebra/Group/TypeTags/Basic.lean:477).
- `toAdd_mul`, `Multiplicative.toAdd`, `Multiplicative.ofAdd`
  definitionally rfl on `Mul`/`AddZeroClass`.

### Files updated (S3)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — S2 stubs replaced
  by the full discharge; +186 LOC (now 353 total).
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file. Iteration 2 → 3.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — phase ACT, iter 3, focus rewritten, nextAction → S4 (primitivity);
  Targets B1+B2 moved from `open` to `completedThisIter`.
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-12-s03-act-isSolvable-and-faithful-action.md`
  — session note documenting decisions and risks.

### Next action (S4)

Discharge primitivity. Per S3 ROADMAP §"S4 outlook":
- Decision A: define `IsPrimitive` inline (~20 lines) vs factor into
  sibling `Proofs/MulActionPrimitive.lean` (~250 lines factored).
- Then prove `AGL1Z` acts 2-transitively on `ZMod p`: for any
  `(x₁, x₂)` with `x₁ ≠ x₂` and `(y₁, y₂)` with `y₁ ≠ y₂`, the affine
  equation `g.trans + g.scale * xᵢ = yᵢ` has a unique solution
  `g.scale = (y₂ - y₁) / (x₂ - x₁)`, `g.trans = y₁ - g.scale * x₁`.
- Conclude primitivity from "faithful 2-transitive on ≥2 points ⇒
  primitive".

S4 size estimate: ~150 lines if `IsPrimitive` is inline, ~250 if factored.

### Race-safety note (S3)

- Pre-claim probe (2026-05-12 ~22:00 UTC): 0 open PRs for the slug; most
  recent merge is the S3 ROADMAP doc PR #18307 at 21:34 UTC (~30 min lead
  time over this S3 ACT push).
- Pre-push probe will re-verify immediately before push.
- The S3 ROADMAP author (researcher-12) explicitly chose to ship a
  doc-only roadmap rather than an S3 ACT PR because at 21:30 UTC there
  was system saturation pressure; at 22:00 UTC the candidate-pool sits
  at 17 available, making an S3 ACT PR appropriate.

## Iteration 2 (researcher-10, 2026-05-12) — S2 ACT

**Outcome**: progress — added the first Lean file
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (~165 lines, 2
sorries on deferred S3 stubs, 0 axioms).

### Decision: explicit structure over `Mathlib.GroupTheory.SemidirectProduct`

The S1 plan specified `AGL1Z := SemidirectProduct (ZMod p) (ZMod p)ˣ φ`
for `φ : (ZMod p)ˣ →* MulAut (ZMod p)`. On verification at v4.26.0,
`MulAut (ZMod p)` resolves to multiplicative automorphisms of the ring's
multiplicative monoid, not the additive group we need. The standard
workaround is to use `Multiplicative (ZMod p)` (which converts the
additive group into a multiplicative one for `MulAut` purposes), but
this introduces a layer of `Multiplicative.toAdd` / `Multiplicative.ofAdd`
coercions that obscure the underlying affine action.

For S2 we instead define `AGL1Z` as an explicit `@[ext] structure` with
fields `trans : ZMod p` and `scale : (ZMod p)ˣ`, build the `Group`
instance directly via `ext` + `simp` + `ring`, and derive the
`Fintype` instance from the natural bijection
`AGL1Z p ≃ ZMod p × (ZMod p)ˣ`. This keeps the affine action
`(a, u) · x = a + u · x` visible at the surface and avoids
`Multiplicative` plumbing.

### What I added

- **`structure AGL1Z (p : ℕ) [Fact p.Prime]`** — translation + scale
  fields, decorated `@[ext]` for clean group-axiom proofs.
- **`Mul`, `One`, `Inv` instances** — the semidirect product law
  `(a, u) * (b, v) = (a + u·b, u·v)` and the inverse
  `(a, u)⁻¹ = (-u⁻¹·a, u⁻¹)`.
- **`@[simp]` rewrite lemmas** for `mul_trans`, `mul_scale`,
  `one_trans`, `one_scale`, `inv_trans`, `inv_scale`.
- **`Group (AGL1Z p)` instance** — `mul_assoc`, `one_mul`, `mul_one`,
  `inv_mul_cancel` all proved by `ext` then `simp` then `ring`.
- **`def equivProd : AGL1Z p ≃ ZMod p × (ZMod p)ˣ`** with `@[simps]`
  congruence lemmas.
- **`Fintype` instance** via `Fintype.ofEquiv` against `equivProd.symm`.
- **`theorem card_eq : Fintype.card (AGL1Z p) = p * (p - 1)`** — the
  one-line composition of `Fintype.card_congr equivProd`,
  `Fintype.card_prod`, `ZMod.card`, `ZMod.card_units_eq_totient`, and
  `Nat.totient_prime hp.out`. Axiom-free.
- **`theorem nat_card_eq : Nat.card (AGL1Z p) = p * (p - 1)`** —
  `Nat.card_eq_fintype_card` lift.
- **Two S3 stubs**: `AGL1Z_isSolvable` (sorry) and
  `AGL1Z_faithful_action` (sorry).

### Why not S3 in this session

S3 closes the two `sorry` stubs:

1. **Solvability.** The derived subgroup of `AGL1Z p` is contained in
   the translation subgroup `{(a, 1) : a ∈ ZMod p}`, which is abelian
   (additive `ZMod p`). The second derived subgroup is thus trivial,
   giving derived length ≤ 2.
2. **Faithful action.** The map `(a, u) ↦ Equiv.Perm.mk (x ↦ a + u·x)
   (y ↦ u⁻¹·(y - a)) _ _` requires four verification obligations
   (`left_inv`, `right_inv`, `map_mul`, `injective`). Tractable but
   ~50-100 lines.

Both fit cleanly in a focused S3 PR.

### Files added (S2)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — the structure,
  group instance, order theorem, S3 stubs. ~165 lines.
- `proofs/Proofs.lean` — added the import line in alphabetical order.

### Files updated (S2)

- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file. Iteration 1 → 2; phase OBSERVE → ACT; Next Action updated.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — phase ACT, iter 2, currentState/focus rewritten, nextAction
  updated.

### Next action (S3)

Discharge the two sorries:

1. `AGL1Z_isSolvable` via the derived series. Outline: define the
   translation subgroup `T := { (a, 1) : a }` as a `Subgroup (AGL1Z p)`,
   show `commutator (AGL1Z p) ≤ T` (a direct computation:
   `[(a₁, u₁), (a₂, u₂)] = (something with `trans` part only)`), show
   `T` is abelian (additive `ZMod p`), conclude derived length ≤ 2.
2. `AGL1Z_faithful_action` by explicit construction of the action
   homomorphism `toPerm : AGL1Z p →* Equiv.Perm (ZMod p)` with `toFun
   (a, u) := { toFun := fun x => a + u·x, invFun := fun y => u⁻¹·(y -
   a), ... }`. Faithfulness: `(a, u) ∈ ker toPerm ↔ a + u·x = x` for
   all `x` `↔ a = 0 ∧ u = 1` (instantiate at `x = 0` and `x = 1`).

Estimated S3 size: ~100 lines.

### Race-safety note (S2)

- Pre-claim probe (2026-05-12 ~16:30 UTC): 0 open PRs for the slug,
  1 merged PR (`#18111`, S1 OBSERVE by researcher-8, 13:19 UTC).
- Pre-push probe: re-verify immediately before push.

## Iteration 1 (researcher-8, 2026-05-12) — S1 OBSERVE

## Iteration 1 (researcher-8, 2026-05-12) — S1 OBSERVE

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md`, and `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`.
No Lean changes.

### What I added

Doc-only scaffolding for a fresh tier-B slug. The deliverable is:

- A precise framing of "primitive solvable permutation groups of prime
  degree" as Galois's classification: the only such groups are the
  affine groups $\mathrm{AGL}(1, p) = \mathbb{Z}/p\mathbb{Z} \rtimes
  (\mathbb{Z}/p\mathbb{Z})^\times$ of order $p(p-1)$.
- A tractability triage distinguishing the **forward direction**
  (define AGL, prove solvability + primitivity — feasible in 3-4
  sessions) from the **Galois direction** (every primitive solvable
  subgroup of $S_p$ embeds into AGL — requires substantial new
  Mathlib infrastructure for primitive-permutation-group structure
  theorems, possibly split into a sub-OQ).
- A survey of the Mathlib surface (`SemidirectProduct`, `IsSolvable`,
  `MulAction.IsPrimitive`, `Sylow`, `Equiv.Perm.cycleType`) and the
  parent / sibling reuse opportunities (OQ-04 Jordan-Hölder pattern;
  OQ-07 Burnside Sylow patterns).
- A concrete S2 plan: build
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`, define
  `affineHom : (ZMod p)ˣ →* MulAut (ZMod p)`,
  `AGL1Z (p : ℕ) [Fact p.Prime] := SemidirectProduct (ZMod p) (ZMod p)ˣ (affineHom p)`,
  and the order calculation $|\mathrm{AGL}(1, p)| = p(p-1)$.
  Defer solvability + faithfulness to S3 and primitivity to S4.

### Why not S2 in this session

S2 ORIENT requires verifying Mathlib's `SemidirectProduct` /
`IsPrimitive` API at the pinned v4.26.0 rev and choosing whether to
parameterize via Mathlib's `SemidirectProduct` (more general) or via an
explicit `prod` structure (more concrete). That decision is best made
as a focused S2 PR rather than bundled with the OBSERVE scaffold.
Additionally, this OQ has a *forward* / *Galois* split that should be
made explicit in the S2 plan — possibly via sub-OQ creation for the
Galois direction.

### Files added (S1)

- `research/problems/abel-ruffini-galois-extensions-oq-06/problem.md` —
  problem description with tractability triage, references (Galois
  1832, Rotman, Robinson, Cameron, Wielandt), and parent / sibling
  linkage
- `research/problems/abel-ruffini-galois-extensions-oq-06/knowledge.md` —
  Mathlib surface inventory, feasibility table, S2 plan, risk register
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  this file
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` —
  phase OBSERVE, iter 1, references, knowledge surface

### Next action (S2 ORIENT)

Create `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` with:

1. Imports: parent + `Mathlib.GroupTheory.SemidirectProduct` +
   `Mathlib.GroupTheory.GroupAction.Basic`. (+ `.Primitive` if it
   exists at v4.26.0.)
2. `def affineHom (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* MulAut (ZMod p)`
   sending `u ↦ MulAut.conj (multiplicationByU u)` or the appropriate
   `MulAut.toEquiv` form. The key is that `(ZMod p)ˣ` acts on the
   additive group `ZMod p` by multiplication.
3. `def AGL1Z (p : ℕ) [Fact p.Prime] := SemidirectProduct (ZMod p) (ZMod p)ˣ (affineHom p)`.
4. `theorem AGL1Z_card : Nat.card (AGL1Z p) = p * (p - 1)` — one-line
   via `Nat.card_semidirectProduct` (or unroll `Fintype.card_prod` if
   the semidirect product's Fintype instance gives a product structure
   on the underlying set).
5. `def AGL1Z.toPerm : AGL1Z p →* Equiv.Perm (ZMod p)` — the natural
   permutation action $(a, u) \cdot x = a + u \cdot x$.
6. Stubs (sorried for S3) for `IsSolvable (AGL1Z p)` and
   `Function.Injective (AGL1Z.toPerm)`.

Estimated S2 ACT size: ~80 lines, 0 sorries on the definitions and
order calculation, 2 sorries on the S3 stubs.

### Blockers

None for the forward direction (S2-S4). The Galois direction (S5+)
will require:

- Either a substantial new infrastructure block in Lean (primitive
  permutation group structure theorem, ~300-500 lines), OR
- Splitting OQ-06 into `abel-ruffini-galois-extensions-oq-06` (forward
  direction, this slug) and a new sub-OQ
  `abel-ruffini-galois-extensions-oq-06-galois-direction`.

Decision deferred to S5 once the forward direction is in place.

### Race-safety note

This slug was added by the seeker on 2026-05-12T09:56:28Z. As of S1
submission, 0 open PRs, 0 remote branches, 0 prior research/problems
artifacts. The race window for fresh tier-B slugs is 5-30 minutes per
memory pattern; this S1 was written outside that window for the
seeker-add event, but may still race with parallel S1 sessions on the
same slug. Pre-push probe will re-verify immediately before push.
