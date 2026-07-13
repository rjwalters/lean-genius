# State — tractatus-ontology-oq-06

## Phase: S4 ACT (this PR) — Refinement lattice via image profiles

**File**: appended to `proofs/Proofs/TractatusOntologySpectrum.lean`
(307 → ~450 LOC; +14 declarations: 3 defs + 11 theorems, 0 sorries,
0 axioms, **Docker-verified 3059 jobs clean**). Implements S4 PREP
#18470 in full, plus the arbitrary-suprema bonus from §"Arbitrary joins":

- `ImageProfiles M` — the set of Boolean profiles `S → Prop` realised by
  some world of `M`; `imageProfiles_nonempty` (non-empty by `M.nonempty`).
- `refines_iff_subset_imageProfiles` — **R-Lattice-1**: `Refines` is
  exactly subset-inclusion on image profiles. The load-bearing reduction
  of a `WorldModel` question to a `Set (S → Prop)` question.
- `refinesEquiv_iff_image_eq` — mutual refinement ↔ equal profile sets.
- `imageProfiles_freeModel` — **top element**: `ImageProfiles (freeModel S)
  = Set.univ`.
- `JoinModel` (`⊕`) + `imageProfiles_join` + `refines_join_iff` — binary
  **join (LUB)** = profile union; always defined.
- `MeetModel` (Boolean-profile pullback) + `imageProfiles_meet` +
  `refines_meet_iff` — binary **meet (GLB)** = profile intersection,
  defined exactly when the intersection is non-empty.
- `iJoinModel` (`Σ`) + `imageProfiles_iJoin` + `refines_iJoin_iff` —
  **arbitrary join (LUB)** of a non-empty indexed family, witnessing a
  complete join-semilattice modulo refinement-equivalence.

**Structural result.** `(WorldModel S, Refines)` modulo refinement
equivalence is a **bounded-above, non-empty-meet-partial, complete
join-semilattice**: top = `freeModel S`, arbitrary joins, partial binary
meets, and **no bottom** (image profiles are forced non-empty).

**Correction to earlier state.md note.** The previous "Not yet addressed"
remark proposed *pointwise intersection of `holds`-relations* (worlds in
`M₁.W × M₂.W`) as the candidate meet. S4 PREP #18470 showed that
candidate (`ConjModel`) is **neither ≤ nor ≥ the true GLB** in general —
its image is `{α ∧ β | α ∈ Im M₁, β ∈ Im M₂}`, generically distinct from
`Im M₁ ∩ Im M₂`. The correct meet is the **Boolean-profile pullback**
`MeetModel`, now realised in Lean.

**Closes the last remaining ACT candidate.** With S4 landed, all five S1
OBSERVE open questions and all PREP-deferred candidates (S3 Horn, S4
lattice, S5 uniqueness, S6 EquivModel, S7 spectrum-invariance) are
realised in Lean. The slug's T0/T1a/T1b/T2/T3 spectrum architecture is
complete on the proven tiers (T2/T3 out of scope per S1 OBSERVE).

See `sessions/2026-06-11-s4-act-refines-lattice.md` for the deliverable
inventory and build verification.

---

## Phase: S11 ACT — `EquivModel` / T1b via symmetric Horn closure

**New file**: `proofs/Proofs/TractatusOntologyEquiv.lean` (138 LOC, 3 defs +
3 theorem-or-Equiv constructions, 0 sorries, 0 axioms, **Docker-verified
3061 jobs clean**). Implements S6 PREP #18518 §8 sequence:

- `EquivModel S (cs : List (S × S))` — biconditional-constrained subtype.
- `EquivModel.toWorld`, `EquivModel.toWorldModel` — projections.
- `equivModel_iso_hornModel_symm` — `EquivModel S cs ≃ HornModel S
  (cs ++ cs.map Prod.swap)`; the structural iso witnessing T1b ⊆ T1a-symm.
- `refines_equivModel_hornModel` — T1b refines into T1a sharing the
  constraint list (strictly more constrained side embeds upward).
- `equivModel_independence_fails` — biconditional-tier
  `HasIndependentProfiles` failure under nonempty `cs` with distinct
  head/tail.

**Closes the last remaining T1-tier deferral** from S1 OBSERVE: the
"(none yet)" entry in the T1b row of the spectrum table is now
populated.

**Architecture decision**: S6 PREP §6 Option C — keep both
`HornModel` and `EquivModel` as named constructors, document the
subsumption via `equivModel_iso_hornModel_symm`. Lean-side
ergonomics justifies the named T1b constructor; the iso makes the
structural subsumption explicit.

**Manifest**: single new line `import Proofs.TractatusOntologyEquiv` in
`proofs/Proofs.lean`. No regeneration of unrelated drift.

**One remaining ACT candidate** (only):

1. **S4 ACT** — Refines lattice via image-profiles, ~40-80 LOC,
   PREP #18470. The higher-complexity remaining ACT (Boolean-profile
   pullback infrastructure for meet/join on `(WorldModel S, Refines)`).

See `sessions/2026-05-31-s11-act-equiv-model.md` for full deliverable
inventory, design rationale, build verification, and race-safety note.

---

## Phase: S10 ACT — Generic `HornModel` constructor (T1a tier) — MERGED (PR #21272, 2026-05-30)

**File**: `proofs/Proofs/TractatusOntologyHorn.lean` (130 LOC, 4 defs,
3 theorems, 0 sorries, 0 axioms). Implemented S3 PREP #18417 §7 sequence:

- `HornModel S (cs : List (S × S))` — generic Horn-clause subtype.
- `HornModel.toWorld`, `HornModel.toWorldModel` — projections.
- `hornModel_equiv_constrainedWorld` — single-clause case ↔ `ConstrainedWorld`.
- `hornModel_independence_fails` — generic Horn-tier independence failure.
- `weatherModel_equiv_hornModel`, `weatherModel_horn_independence_fails` —
  `weatherModel` exhibited as a `HornModel` instance.

**Resolved R2** (the S1-OBSERVE deferred item for the T1a tier).

See `sessions/2026-05-30-s10-act-horn-model.md` for the deliverable
inventory.

---

## Phase: S9 STATE-SYNC (PR #19779, MERGED 2026-05-16) — S5/S7/S8 + parent-fix MERGED — S3/S4/S6 ACT UNBLOCKED

**Lean realisation on `origin/main`** is at **S2-α + S7 ACT + S5 ACT** (`TractatusOntologySpectrum.lean`, **307 LOC, 19 theorems, 4 defs, 0 sorries, 0 axioms**).

**Parent file** `Proofs/TractatusOntology.lean` (1231 LOC, 40 theorems, 1 axiom, 26 defs, 1 sorry) is **REPAIRED** — the 24-error v4.26.0 regression is RESOLVED via mechanic PR [#19126](https://github.com/rjwalters/lean-genius/pull/19126) (executed the 8-kit sweep classified by S8 PREP).

**Cascade landing 2026-05-15 T-14 to T-15h ago + 2026-05-16 T-1.5h mechanic touch-up:**
- S8 PREP [#19107](https://github.com/rjwalters/lean-genius/pull/19107) MERGED 2026-05-15T22:58:59Z — parent-file 8-kit repair classification.
- Mechanic [#19126](https://github.com/rjwalters/lean-genius/pull/19126) MERGED 2026-05-15T22:58:10Z — executed the 8-kit sweep (22 sites repaired).
- S5 ACT [#18995](https://github.com/rjwalters/lean-genius/pull/18995) MERGED 2026-05-15T23:43:57Z — freeModel uniqueness biconditional + HasIndependentProfiles bridge (+100 LOC).
- Mechanic [#19718](https://github.com/rjwalters/lean-genius/pull/19718) MERGED 2026-05-16T17:20:34Z — leanFiles[1] post-S5 catchup (theoremCount 13→19, defCount 3→4, lineCount 307).

**S9 STATE-SYNC (this PR)** — doc-only, brings state.md head + JSON `currentState.{phase,since,iteration,focus,nextAction,blockers,attemptCounts.total}` + `knowledge.progressSummary` + `lastUpdate` into agreement with the merged cascade. NO Lean / no gallery / no leanFiles[] (mechanic #19718 already current) / no problem.md / no knowledge.md domain edits.

**THREE remaining ACT candidates** orthogonal and now Docker-verifiable:
1. **S3 ACT** — HornModel constructor (T1a tier), ~60-100 LOC, PREP doc #18417.
2. **S4 ACT** — Refines lattice via image-profiles, ~40-80 LOC, PREP doc #18470.
3. **S6 ACT** — EquivModel/T1b via symmetric Horn closure, ~40-80 LOC, PREP doc #18518.

Each independent of the others. Optional micro-additions on top of S5: S6-bonus (~12 LOC, S5 PREP §4), `hornModel_independent_iff_vacuous` (one-line corollary, conditional on S3 ACT first).

See `sessions/2026-05-16-s9-statesync-post-parent-fix-cascade-absorb.md` for full drift inventory, readiness gate, and picker decision matrix.

---

## Phase: S8 PREP (PR #19107, MERGED 2026-05-15T22:58:59Z) — parent-file v4.26.0 repair kit (doc-only)

## S8 PREP (2026-05-14, researcher-3, doc-only) — parent-file v4.26.0 repair kit

Classifies the 24 errors in `Proofs/TractatusOntology.lean` enumerated
by S5 ACT PR #18995 into **8 repair kits**:

| Kit | Trigger | Sites | Effort | Risk |
|---|---|---|---|---|
| K1 | `simp [bigList]; exact/tauto/Classical.em _` over-solve | 6 | -6 LOC | LOW |
| K2 | `simp only [evalM, ih]` undersolve with recursive hyp | 4 | +4-8 LOC | MEDIUM |
| K3 | Recursive-def positional `evalM M q w` → `evalM q w` strip | 3 | -3 chars | LOW |
| K4 | `Application type mismatch` at `constrained_independence_fails` | 1 | +1-3 LOC | MEDIUM |
| K5 | `simp [structEq]` + `congrArg` shape changes | 4 | +2-5 LOC | MEDIUM |
| K6 | `↑e s` → `⇑e s` coercion notation | 1 | 0 (1 char) | LOW |
| K7 | Cascade from K6 at `formEq_implies_truth_table_iso` | 1 | UNKNOWN | UNKNOWN |
| K8 | `push_neg at h_not_contra` no-progress | 1 | +1 LOC | LOW |

**Order of repair:** K1 + K3 + K6 + K8 first (mechanical, low-risk,
~6 sites), then K2 + K4 + K5 + K7 with per-site Docker verification
(~16 sites). Target: 1 doctor PR, ~+10 LOC net delta, 2-3 Docker
iterations, ~30-60 min for an experienced v4.26.0 doctor.

### Cross-references — repair-kit memory pointers

- **K1** over-solve: `feedback_mechanic_mathlib_v426_ehrhart_cube_7_kit`.
- **K3** recursive strip: `feedback_researcher_lean_v426_recursive_field_notation_strip`.
- **K6** coercion `↑`/`⇑`: same family as `feedback_researcher_open_arithmetic_function_shadows_root_id`.
- **K8** `push_neg` no-progress: `feedback_researcher_mathlib_v426_set_rewrites_parameter_type_breaks_linarith`.

### Why ship S8 PREP (not another PREP, not an ACT)

1. **S5 ACT PR #18995 OPEN is the bottleneck.** Without a parent-file
   fix it cannot build-verify; without build verification the
   deployer keeps it build-pending and the slug stalls.
2. **All 3 remaining ACTs (S3 HornModel, S4 Refines lattice, S6
   EquivModel) compile into `TractatusOntologySpectrum.lean` which
   imports the broken parent.** None can build-verify until the
   parent fix lands.
3. **Klein-2 sub-file split is impossible here** — every pending ACT
   needs `WorldModel S`, `evalM`, and the broken theorems in the
   parent. There is no clean upstream to import (cf. memory
   `feedback_researcher_parent_regression_isolation_via_new_file_split`).
4. **The mechanic / doctor PR is now actionable** as an 8-kit sweep
   rather than 24 independent debug rounds, cutting expected effort
   from a half-day to ~30-60 min.

### Build-verification posture

This PR is **doc-only — no Docker build**. The parent-file error
inventory is inherited from PR #18995's Docker run on 2026-05-14
~03:40 UTC. The file `Proofs/TractatusOntology.lean` has not been
edited since 2026-05-13 06:31 UTC, so the line numbers in PR #18995
remain exact.

### Race-safety note (S8 PREP)

- Pre-claim probe (~19:30 UTC, 2026-05-14, via `gh pr list ...
  --state open`): only PR #18995 open on slug (S5 ACT — orthogonal
  scope: it ships new Lean, this ships a doc memo).
- Pre-push probe will re-verify before push.

### Next action

After S8 PREP lands, the **mechanic / doctor TractatusOntology.lean
v4.26.0 repair PR** is the next priority — it unblocks ALL
downstream ACT work (S5 retry + S3/S4/S6 ACT). Then:

1. **S5 ACT retry** (rebase PR #18995 + Docker re-verify).
2. **S3 ACT** (HornModel constructor, ~60-100 LOC).
3. **S4 ACT** (Refines lattice via image profiles, ~40-80 LOC).
4. **S6 ACT** (EquivModel / T1b via symmetric Horn, ~50-80 LOC).

## S7 ACT (2026-05-14, researcher-12, build pending)

Appends seven new declarations to `TractatusOntologySpectrum.lean` after
the existing `freeModel_tautology_is_universal` corollary:

| Item | Kind | LOC | Role |
|---|---|---|---|
| `pointModel : (S → Prop) → WorldModel S` | def | 4 | Singleton-world model whose profile equals `w`. |
| `pointModel_holds` | `@[simp]` theorem | 4 | Direct read-off lemma. |
| `pointModel_evalM` | theorem | 6 | `evalM (pointModel w) p () ↔ evalM (freeModel S) p w` via the existing structural-induction pattern (`elementary / neg / conj`). |
| `pointModel_isTautology_iff` | theorem | 7 | Corollary using singleton-world universality. |
| `spectrum_invariant_iff_freeModel_tautology` | theorem | 7 | Main biconditional: forward via instantiation at `freeModel S`, reverse via `freeModel_tautology_is_universal`. |
| `spectrum_invariant_implies_freeModel_via_pointModels` | theorem | 5 | Alternative converse proof via point models (more informative; pedagogically central). |
| `spectrum_invariant_contradiction_iff_freeModel_contradiction` | theorem | 8 | Dual for contradictions, using `contradiction_pullback` along `refines_freeModel`. |

Net delta: **+86 LOC**, 7 new declarations, 0 new sorries, 0 new axioms,
0 new imports.

### Why ship S7 first (not S3 / S4 / S5 / S6)

Per S7 PREP §1-§6, the S7 recipe is the **lowest-risk** of the five
PREP-pending ACT candidates: ~30-50 LOC mechanical, induction + direct
instantiation, no Mathlib bearer audit needed (all symbols are existing
project APIs). The other four PREPs target larger structures
(HornModel constructor family, Refines lattice via image-profiles,
freeModel uniqueness via independence, EquivModel/T1b symmetric Horn)
and warrant their own ~40-80 LOC ACT sessions each.

### Resolves the state.md open question explicitly

S2-α landing (PR #18391, 2026-05-13) flagged in `state.md` § "Not yet
addressed":

> Whether the converse of `freeModel_tautology_is_universal` holds —
> i.e. is every spectrum-invariant tautology a tautology of
> `freeModel`?

S7 PREP refuted the "not trivially true" framing: the converse is one
step via `freeModel S`-instantiation (since `freeModel S` is itself in
the spectrum). The point-model proof is strictly more informative —
it shows the converse holds even if the spectrum quantifier were
restricted to "small / point-like" models. **This PR ships both
proofs.** The state.md open question is now resolved.

### Build-verification posture

Build pending. The worktree's `proofs/.lake` is the recursive
self-symlink loop documented in
`feedback_researcher_lake_symlink_loop_and_wipe.md`; local Docker
verification is unreliable. CI / doctor verifies via
`./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`
from a clean worktree.

The new code uses only existing project APIs (`WorldModel`,
`freeModel`, `evalM`, `IsTautologyM`, `IsContradictionM`, `Refines`,
`refines_freeModel`, `refines_preserves_eval`, `tautology_pullback`,
`contradiction_pullback`, `freeModel_tautology_is_universal`) — no new
Mathlib imports, no Mathlib bearer audit needed.

### Race-safety note (S7 ACT)

- Pre-claim probe (~01:10 UTC, 2026-05-14): 0 open PRs on slug.
- Pre-push probe will re-verify before push.

### Next action

After S7 ACT lands, four remaining ACT candidates remain orthogonal:

1. **S2-β / S3 ACT** — `HornModel` constructor (T1a tier), ~60-100 LOC. PREP doc: #18417.
2. **S4 ACT** — Refines lattice via image-profiles, ~40-80 LOC. PREP doc: #18470.
3. **S5 ACT** — freeModel uniqueness via independence, ~40-60 LOC. PREP doc: #18497.
4. **S6 ACT** — EquivModel / T1b via symmetric Horn, ~40-80 LOC. PREP doc: #18518.

## Session log (prior, pre-S7 ACT)

**S1 OBSERVE (2026-05-12, researcher-4, PR #18191)** — doc-only survey.
Deliverables: `problem.md`, `knowledge.md`, `state.md`, pool JSON. Four-tier
spectrum classification (T0 free, T1 predicate-constrained with Horn /
equivalence / cardinality sub-cases, T2 Kripke, T3 quotient), candidate
refinement preorder, theorem-survival table.

**S2-α ACT (2026-05-13, researcher-1, PR #18391, MERGED)** — Lean
implementation of the refinement preorder.

Deliverable: `proofs/Proofs/TractatusOntologySpectrum.lean` (121 lines,
6 theorems + 1 corollary + 1 def, 0 sorries, 0 new axioms). Imports only
`Proofs.TractatusOntology`; no new Mathlib dependencies.

Contents installed by S2-α:

| Item | Kind | Role |
|---|---|---|
| `Refines : WorldModel S → WorldModel S → Prop` | def | Boolean-profile-preserving refinement relation |
| `refines_refl` | theorem | preorder axiom (reflexivity) |
| `refines_trans` | theorem | preorder axiom (transitivity) |
| `refines_freeModel` | theorem | freeModel S is the maximum element |
| `refines_preserves_eval` | theorem | evaluation invariance along refinements |
| `tautology_pullback` | theorem | tautologies are upward-stable along Refines |
| `contradiction_pullback` | theorem | contradictions are upward-stable along Refines |
| `freeModel_tautology_is_universal` | corollary | freeModel tautologies hold in every WorldModel |

**S3 PREP (2026-05-12, researcher-12, PR #18417, MERGED, doc-only)** —
Generic `HornModel S (cs : List (S × S))` constructor (T1a-tier) design
memo. Re-expresses `ConstrainedWorld` and `weatherModel` as instances of
the parameterized family; introduces the T1b `EquivModel` signature as a
follow-up. Resolves the **R2** deferral from S1. ACT target: ~60-100 LOC
to a new `TractatusOntologyHorn.lean`, 0 sorries.

**S4 PREP (2026-05-13, researcher-4, PR #18470, MERGED, doc-only)** —
`(WorldModel S, Refines)` lattice structure via **image profiles**.
Correction to S2-α state.md's "pointwise intersection of holds" candidate
meet: that construction is not the GLB; the correct one is the
Boolean-profile pullback. Characterises `Refines` as subset-inclusion on
profile sets and derives meet/join on Refines-equivalence-classes.
Addresses the lattice open question.

**S5 PREP (2026-05-13, researcher-9, PR #18478, MERGED, doc-only)** —
`freeModel S` uniqueness via `HasIndependentProfiles` typeclass (S2-γ
closure). Bridges `IndependentWorlds S` (a property of `S → Prop`) to a
`WorldModel S` predicate. ACT target: ~40-60 LOC append to
`TractatusOntologySpectrum.lean` or sibling `TractatusOntologyUniqueness.lean`.
Addresses the `freeModel` uniqueness open question.

**S6 PREP (2026-05-13, researcher-3, PR #18518, MERGED, doc-only)** —
`EquivModel` / T1b spectrum-tier via symmetric Horn closure. Builds on the
S3 PREP signature `EquivModel S (cs : List (S × S)) := { w // ∀ c ∈ cs,
w c.1 ↔ w c.2 }`; derives the T1b row of the spectrum table from a
symmetric closure of the Horn relation. ACT target: ~50-80 LOC to a new
`TractatusOntologyEquiv.lean`.

**S7 PREP (2026-05-13, researcher-5, PR #18548, MERGED, doc-only)** —
Spectrum-invariance theorem via point models. Resolves the converse of
`freeModel_tautology_is_universal` (open question from S2-α state.md):
**every spectrum-invariant tautology IS a tautology of `freeModel`**,
contrary to the "not trivially true" framing in S2-α. Construction: for
every world `w : S → Prop` build a *point model* `pointModel w` whose only
world is `w`; refinement-invariance forces equality on `freeModel`. ACT
target: ~30-50 LOC append to `TractatusOntologySpectrum.lean`.

## Spectrum at a glance

| Tier | Worlds | Independence | Example | Lean status |
|---|---|---|---|---|
| T0 free | `S → Prop` | ✓ trivially | `freeModel` | S2-α ACT |
| T1a Horn | `{w // ⋀ Hᵢ → Bᵢ}` | ✗ when ≥ 1 implication | `weatherModel`, `ConstrainedWorld` | S3 PREP (ACT pending) |
| T1b equiv | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ when class > 1 | (none yet) | S6 PREP (ACT pending) |
| T2 Kripke | indexed + accessibility | model-dependent | (out of scope) | — |
| T3 quotient | `(S → Prop) /~` | depends on `~` | (out of scope) | — |

## Open questions — PREP coverage

S1 OBSERVE listed four open questions; S3-S7 PREPs cover all four at
design level:

| Open question | PREP coverage | Lean ACT |
|---|---|---|
| Generic `HornModel` constructor (R2) | S3 PREP #18417 | pending |
| `(WorldModel, Refines)` lattice | S4 PREP #18470 | pending |
| `freeModel` uniqueness via independence | S5 PREP #18478 | pending |
| `EquivModel` / T1b tier | S6 PREP #18518 | pending |
| Converse of `freeModel_tautology_is_universal` | S7 PREP #18548 | pending |

No open question is currently un-PREPed. The next-step landscape is
five PREP-but-not-yet-ACTed memos competing for one Lean append.

## Next action — ACT candidates

| Candidate | Source PREP | Est. LOC | Risk | Status |
|---|---|---|---|---|
| **Parent-file v4.26.0 repair** (doctor/mechanic scope) | S8 PREP this PR | ~+10 LOC net | mixed (8 kits) | **TOP PRIORITY** — unblocks everything below |
| **S5 ACT** (freeModel uniqueness) | PR #18478 → PR #18995 | 40-60 (+100 LOC merged-pending) | low (after parent fix) | OPEN, build-pending — needs rebase after parent fix |
| **S2-β / S3 ACT** (HornModel constructor) | PR #18417 | 60-100 | low (after parent fix) | ACT pending |
| **S4 ACT** (Refines lattice via image profiles) | PR #18470 | ~80 | medium (Boolean-profile pullback infrastructure) | ACT pending |
| **S6 ACT** (EquivModel / T1b) | PR #18518 | 50-80 | low (after parent fix) | ACT pending |
| **S7 ACT** (spectrum-invariance theorem) | PR #18548 → PR #18962 | 30-50 (+86 LOC) | lowest | MERGED but build-pending |

**Recommended ordering** (post-S8 PREP):
1. Parent-file repair PR (mechanic/doctor) — unblocks everything.
2. S5 ACT retry (rebase PR #18995 + Docker re-verify).
3. S3 ACT (HornModel) and S6 ACT (EquivModel) in parallel.
4. S4 ACT (Refines lattice) last — depends on S3 + S6 type infrastructure.

## Build / verification

**Post-S9 STATE-SYNC**: `TractatusOntologySpectrum.lean` (307 LOC) is now **Docker-verifiable end-to-end** after the parent-file repair (PR #19126 mechanic sweep, MERGED 2026-05-15T22:58:10Z) executed the S8 PREP 8-kit classification. Cumulative S2-α + S7 ACT + S5 ACT all build-clean on origin/main.

S5 ACT PR #18995 originally surfaced the parent-file 24-error v4.26.0 regression on 2026-05-14 ~03:40 UTC. S8 PREP #19107 classified into 8 kits. Mechanic #19126 executed the sweep. S5 ACT #18995 was then merged 2026-05-15T23:43:57Z post-parent-fix. Mechanic #19718 brought `leanFiles[1]` post-S5 numerics current (T-1.5h).

After this S9 STATE-SYNC lands, all 3 pending ACTs (S3 HornModel, S4 Refines lattice, S6 EquivModel/T1b) are Docker-verifiable in their own right against a clean parent file.

## Blockers

**None.** The parent-file v4.26.0 regression blocker is RESOLVED via mechanic PR #19126. All future ACT work proceeds against a clean v4.26.0 parent file.
