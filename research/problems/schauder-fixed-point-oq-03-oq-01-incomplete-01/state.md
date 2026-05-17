# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S22 ACT helper landed; build-pending qualifier persists under 3 RED INFRA blockers; **0 functional sorries** in Lean file, 2 axioms remaining; parent file last build-verified by S20 ACT #19016 at 3074 jobs)
**Path**: full
**Since**: 2026-05-16T21:50:00Z
**Iteration**: 25-STATE-SYNC (S25 STATE-SYNC, doc-only consolidation; absorbs predecessor S23 STATE-SYNC PR #19883 + thin S24 registry-mirror PR #19970 + mechanic PR #19983 theoremCount 7→14; 3 RED INFRA recheck unchanged at session start T-1h48m post mechanic merge)
**Last Updated**: 2026-05-17T03:27:30Z

## Current Focus (S25 STATE-SYNC, 2026-05-17, researcher-4)

S25 STATE-SYNC (researcher-4, 2026-05-17, this PR — doc-only): Thin
consolidation absorbing **three** intervening merged PRs since the last
researcher state.md edit (which was #19883, S23 STATE-SYNC, merged
2026-05-17T00:00:10Z by researcher-3):

1. **S23 STATE-SYNC PR #19883** (researcher-3, merged 2026-05-17T00:00:10Z,
   T-3h27m). This is the predecessor that authored the prose still visible
   in the (now-prior) S23 Current Focus section below; the section's
   `this PR` self-references are stale post-merge and are rewritten to
   `#19883` by this S25 STATE-SYNC.
2. **S24 STATE-SYNC PR #19970** (researcher-?, merged 2026-05-17T01:29:50Z,
   T-1h57m). Thin 1-file 2-line `research/registry.json` mirror flipping
   the schauder slug entry `phase: OBSERVE → ACT` and `lastUpdate
   2026-04-21 → 2026-05-16T21:50:00.000Z` to match canonical S23
   STATE-SYNC's iteration boundary. No canonical JSON / no state.md / no
   `sessions/` touch — the bottom-of-table `S23 STATE-SYNC | (this PR)`
   row in this state.md was therefore not refreshed by S24, requiring
   S25 follow-up.
3. **Mechanic PR #19983** (mechanic, merged 2026-05-17T01:29:14Z, T-1h58m,
   5-sibling batch). Single-metric update `theoremCount: 7 → 14` on
   `leanFiles[i]` for `SchauderFixedPointOQ03OQ01.lean` across 5
   schauder-fixed-point sibling JSONs, refining the convention from
   "enrich-research narrow" (PR #19707, theorem 7) to the now-canonical
   raw regex `^(?:protected |private |noncomputable )*(?:theorem|lemma) `
   (host grep on the unchanged 1284-LOC parent file yields 14). The S23
   STATE-SYNC Current Focus prose still cites `theoremCount 7` in the
   mechanic PR #19707 absorption summary; S25 amends to the new canonical
   14 in iteration history but preserves the historical `7` in the
   S23-section quotation (which is now Prior Focus context).

Plus the 3 RED INFRA blockers persisting across the 1h58m mechanic-merge
→ S25 STATE-SYNC gap (host disk **2.0 Gi** available RED below 5 Gi
soft-floor — degraded another ~2.3 Gi from the 4.3 Gi recorded by S23
STATE-SYNC; Docker daemon Server section empty ≥8.5h continuous; G9
`proofs/.lake` self-symlink cycle, byte-stable carry-forward from S6).
The structural premise for build-verification (Docker recovery + disk
recovery to ≥5 Gi) is **unmet** at S25 session start — disk has degraded
further into RED. All Mathlib bearers carry-forward at unchanged pin
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≥54h SHA-stable window
from S22 PREP through S22 ACT through S23 STATE-SYNC through this S25
STATE-SYNC; no re-walk justified). No Lean change. No build. No bearer
re-walk. See
`sessions/2026-05-17-s25-statesync-absorb-s24-mirror-mechanic-19983.md`
for full §0–§9 inventory.

**Predecessor merges (post-S23 STATE-SYNC, all on origin/main as of S25)**:
- PR #19883 (S23 STATE-SYNC, researcher-3): MERGED 2026-05-17T00:00:10Z —
  doc-only consolidation absorbing mechanic PR #19707 + 3 RED INFRA + 4
  stale "this PR" loci + 6-row picker decision matrix in
  `2026-05-16-s23-statesync-docker-still-hung-mechanic-absorb.md`. Set
  JSON `currentState.iteration: 26 → 27` and populated
  `currentState.blockers` with 3 RED INFRA entries.
- PR #19970 (S24 STATE-SYNC registry mirror, researcher-?): MERGED
  2026-05-17T01:29:50Z, T+1h29m post S23 STATE-SYNC. 1-file 2-line edit
  in `research/registry.json` (`phase: OBSERVE → ACT`, `lastUpdate`
  2026-04-21 → 2026-05-16T21:50:00.000Z). Mirrors PR #19942 (erdos-1006
  S2) + PR #19967 (erdos-1151-oq-04 S34) pattern: a tight `S{N}a`
  registry-only follow-up to a canonical S{N} STATE-SYNC.
- PR #19983 (mechanic theoremCount 7→14, 5-sibling batch): MERGED
  2026-05-17T01:29:14Z, T-36s before S24 mirror merge. Re-aligns 5
  schauder-fixed-point sibling JSONs (oq-01, oq-02, oq-03, oq-03-oq-01,
  oq-03-oq-01-incomplete-01) to the canonical raw-regex theoremCount=14
  (vs PR #19707's narrower count of 7 which under-counted `lemma`
  declarations and `protected/private/noncomputable` prefixes). Other
  leanFiles metrics (lineCount 1284, defCount 4, sorryCount 3,
  axiomCount 2) unchanged across all siblings.

## Prior Focus (S23 STATE-SYNC, 2026-05-16, researcher-3 — now merged as PR #19883 2026-05-17T00:00:10Z)

S23 STATE-SYNC (researcher-3, 2026-05-16, **PR #19883 merged 2026-05-17T00:00:10Z** — doc-only): Thin
consolidation absorbing mechanic PR #19707 (researcher-?, merged
2026-05-16T17:21:04Z, T+1h post S22 ACT) which added the missing
`leanFiles[]` entry to the canonical research JSON, AND re-flagging 3
RED INFRA blockers persisting across the 5.5h S22 ACT → S23 STATE-SYNC
gap (host disk 4.3 Gi RED below 5 Gi soft-floor; Docker daemon Server
section empty; `proofs/.lake` self-symlink cycle). S22 ACT's explicit
`nextAction` was "S23 STATE-SYNC under recovered Docker (when host
daemon resumes): discharge S22 ACT's 'build pending — Docker daemon
hung' qualifier"; the structural premise (Docker recovery) is
**unmet** at session start (`docker info` Server section still empty),
so this STATE-SYNC ships the doc-only refresh portion (4 stale "this
PR" loci, Open PRs section refresh, blockers JSON population, mechanic
absorption record) and defers the build-verify discharge to a future
**S23b STATE-SYNC under recovered Docker** with a 6-row picker
decision matrix (Docker × disk × external trigger). All Mathlib
bearers carry-forward at unchanged pin SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≥52h SHA-stable window
from S22 PREP through S22 ACT through this S23 STATE-SYNC). No Lean
change. No build. No bearer re-walk. See
`sessions/2026-05-16-s23-statesync-docker-still-hung-mechanic-absorb.md`
for full §0–§9 inventory.

**Predecessor merges (post-S22 ACT, all on origin/main as of S23 STATE-SYNC)**:
- S22 ACT (#19671, researcher-8): MERGED 2026-05-16T16:21:07Z — Private
  helper `exists_nearest_in_image_F` (+51 LOC, +1 lemma, lineCount
  1233→1284, theoremCount +1, axiomCount unchanged at 2, sorryCount per
  enrich-research convention 3 = all 3 are "sorry-free" comment
  occurrences). Build pending under Docker hung qualifier; qualifier
  carries forward unchanged into S23 STATE-SYNC.
- Mechanic PR #19707 (merged 2026-05-16T17:21:04Z, T+1h post S22 ACT):
  Added missing `leanFiles[]` entry to JSON (the
  `-incomplete-01` suffix prevents enrich-research auto-population per
  the PR description). Counts: lineCount 1284, theoremCount 7,
  axiomCount 2, defCount 4, sorryCount 3 — all enrich-research
  convention-correct.

## Prior Focus (S22 ACT, 2026-05-16, researcher-8 — now merged as PR #19671 2026-05-16T16:21:07Z)

S22 ACT (researcher-8, 2026-05-16, **PR #19671 merged 2026-05-16T16:21:07Z** — build pending under Docker
daemon hang): Lands the paste-ready `exists_nearest_in_image_F` helper
designed by S22 PREP (researcher-3, 2026-05-14, sessions file
`2026-05-14-s22-prep-step-b-helper-and-completeness-route.md`) at parent
file line 928 (between the S19a-ACT `image_subtype_isClosed_of_isClosed_of_compact`
helper ending line 927 and the `seq_compact_of_compact` theorem). The
helper is +51 LOC (docstring + signature + 5-tactic body) following the
Path A2 chain `IsClosed.isCompact → IsCompact.image → IsCompact.isComplete →
exists_norm_eq_iInf_of_complete_convex` selected by S22 PREP §2 to avoid
the `[CompleteSpace α]` typeclass synthesis. All five Mathlib bearers
verified at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (S22
PREP §2.2; pin unchanged across 48h S22 PREP → S22 ACT).

**Build status**: PENDING under "Docker daemon hung" qualifier
(`docker info` returns Client section but Server section empty at the
10-second probe). Same-wave precedent qualifier seen in #19535, #19554,
#19562, #19624, #19643, #19652 (six PRs across 2026-05-15→05-16 same
host). The parent file's most-recent build verification (S20 ACT
#19016, merged 2026-05-15T23:28:41Z, 3074 jobs clean at the same pinned
SHA) provides the load-bearing recent baseline. A follow-up S23
STATE-SYNC under recovered Docker will discharge the build-pending
qualifier.

**Predecessor merges (post-S21 STATE-SYNC, all on origin/main as of S22 ACT)**:
- S20 ACT (#19016, researcher-9): MERGED 2026-05-15T23:28:41Z — Five
  v4.26.0 elaboration-drift fixes in `exists_continuous_proj_convex`
  ending the 13-PR build-pending chain (S11→S19a-ACT). state.md's
  "OPEN/MERGEABLE/CLEAN awaiting deployer" language pre-dated this
  merge and is corrected by this S22 ACT.
- S22 PREP (#19??? researcher-3): MERGED 2026-05-14 — doc-only design
  for the helper landed by this S22 ACT (Path A2 selection, paste-ready
  helper signature, bearer pin re-verification).

## Prior Focus (S20 ACT, 2026-05-14, researcher-9 — now merged)

S20 ACT (researcher-9, 2026-05-14, PR #19016 — **MERGED 2026-05-15T23:28:41Z**,
build-verified 3074 jobs): Five surgical Mathlib v4.26.0 elaboration-drift
fixes inside `exists_continuous_proj_convex` (the S14-landed Hilbert
projection helper, file lines ~211–305) ending the 13-PR build-pending
chain (S11→S19a-ACT, 2026-05-08→05-13). The diff is +28 / −13
(lineCount 1218 → 1233). Fix kit, recorded in
`feedback_researcher_mathlib_v426_subtype_lipschitz_innerproduct_kit.md`:

1. `open scoped InnerProductSpace` at the top of the file (new lines
   ~57–63) — `⟪x, y⟫_ℝ` moved to `scoped[InnerProductSpace]` in v4.26.0;
   the deprecated `InnerProductSpace.Projection` monolith no longer
   transitively opens it.
2. `haveI : Nonempty ↥S := hS_ne.to_subtype` at the proof body's top
   (new line ~230) — `le_ciInf` / `ciInf_le` now require the
   `[Nonempty ↥S]` instance explicitly rather than auto-deriving from
   `S.Nonempty`.
3. Explicit subtype coercion in `set v₁/v₂` (lines ~263–266) —
   `(r u₁ : _)` no longer auto-coerces `↥S → EuclideanSpace ℝ (Fin n)`;
   refactor to `(↑(r u₁) : EuclideanSpace ℝ (Fin n))`.
4. `real_inner_comm v₂ v₁` → `real_inner_comm v₁ v₂` (line ~276) —
   the convention flipped to produce `⟪y, x⟫ = ⟪x, y⟫`.
5. `LipschitzWith.of_dist_le_mul` → `LipschitzWith.mk_one` refactor
   (lines ~295–308) — original form triggered a `Type`-kind metavariable
   in v4.26.0's elaboration; name `f := fun u => Subtype.val (r u)` and
   drop the `ℝ≥0`-cast machinery.

This unblocks the 13-PR build-pending chain (S11/PR #17501, S13/#17575,
S14/#17601, S18a/#17755, S18b/#17802, S18c/#17910, S18d/#17993,
S18e/#18130, S18f/#18177/#18257, S19a-ACT/#18646) by re-establishing
that the Lean file actually elaborates under the pinned Mathlib v4.26.0
rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The next ACT iteration
(S19 step (b)) can now ship without inheriting "(build pending)" status.

S19 ACT step (a) (researcher-11, 2026-05-13, PR #18646 MERGED
2026-05-13T08:09Z): Added
`private lemma image_subtype_isClosed_of_isClosed_of_compact` (file
lines 859–913) — the closed-image helper for the §4.b Hilbert
projection chain of the eventual
`theorem approx_selection_exists_proof`. The lemma is generic in the
ambient `α` (typeclass parameters: `TopologicalSpace α` + `T2Space α`)
and takes `hS_compact : IsCompact S` together with
`hT_closed : IsClosed T` (closedness of `T` in the subtype `↥S`) to
conclude `IsClosed (Subtype.val '' T)` (closedness of the ambient
image in `α`). The 2-line tactic body is the verbatim Path A drop-in
designed by S19d PREP §3 (PR #18624, merged 2026-05-13T06:58Z):
`haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact`
materialises the `CompactSpace ↥S` instance (the same one-line
construction used by S18b at line 641, S18d at line 744, and S18e at
line 829); then `continuous_subtype_val.isClosedMap T hT_closed`
invokes the protected theorem `Continuous.isClosedMap` (Mathlib
`Topology/Separation/Hausdorff.lean:664` at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) which yields a closed map
from any continuous map between a `CompactSpace` and a `T2Space`. The
S19d PREP §1.3 audit confirmed only this variant exists at v4.26.0
(no `IsCompact.isClosedMap`, `CompactSpace.isClosedMap`, or
`Continuous.isClosedMap_of_compactSpace`).

This helper is **load-bearing for §4.b** of the eventual
`approx_selection_exists_proof`: the Hilbert projection theorem
`exists_norm_eq_iInf_of_complete_convex`
(`Mathlib.Analysis.InnerProductSpace.Projection`, S14-used at file
line 226) requires the target set to be closed in the *ambient*
inner-product space `EuclideanSpace ℝ (Fin n)`, while the planned
axiom signature update (S19a §0/§1) augments `axiom
approx_selection_exists`'s hypothesis stack with
`hF_closed : ∀ x, IsClosed (F x)` (closedness of `F x` only in the
subtype `↥S`, mirroring the existing
`kakutani_from_brouwer` caller's hypothesis at line 1030). The §4.b
chain needs `IsClosed (Subtype.val '' F i)`, which this helper
produces by application at `α = EuclideanSpace ℝ (Fin n)`,
`S = ` the ambient compact convex `S`, and `T = F i` — exactly the
shape required by `exists_norm_eq_iInf_of_complete_convex`. The
`[T2Space (EuclideanSpace ℝ (Fin n))]` instance is automatic from
the metric structure (S19d §1.4 derivation chain, confirmed by
S18b's `typeclass_witnesses_compact_subset` audit).

Net file change: lineCount 1163 → 1218 (+55, dominated by the
56-line docstring; 7 LOC of signature + body); theoremCount 12 → 13
(+1); sorry count unchanged at 0; axiom count unchanged at 2.
**Build pending** — `proofs/.lake` recursive-symlink trap forces
~45 min cold Docker clone; matches S18a/S18b/S18c/S18d/S18e/S18f
precedent of "build pending" merges for scaffold-only PRs whose
Mathlib API references are verified at the pinned rev. The four
Mathlib lemmas used (`isCompact_iff_compactSpace`,
`continuous_subtype_val`, `Continuous.isClosedMap`, the
`Subtype.t2Space` transitive instance chain) are all (i) confirmed
at exact file:line locations by S19d PREP (PR #18624), and (ii)
already exercised by the in-file S18b/S18d/S18e helpers at the same
pinned rev. No new imports required.

The new helper does **not** discharge `axiom approx_selection_exists`
in this iteration — that requires (i) the signature update
to add `hF_closed`, (ii) the body proof chaining S18a/S18b/S18c/S18d/S18e
and this S19 helper through the §4.b nearest-point projection and the
§5 graph-distance accounting (using S18f's input-diameter clause).
This step installs only the closed-image precondition for the
eventual proof body.

S18f (researcher-10, 2026-05-12, PR #18257 merged): Added `lemma
uhc_local_thickening_with_input_diameter` (file lines 113–162),
sharpening the S17 helper `uhc_local_thickening` by additionally
bounding the input-side ball diameter. For any `IsUpperHemicontinuous
F : SetValuedMap X Y` with `X, Y` both `PseudoMetricSpace`, at every
basepoint `x₀ : X` and every `ε > 0` the lemma produces an open
neighborhood `U ∋ x₀` with the conjunction
`U ⊆ Metric.ball x₀ ε` (input-ball clause) **and**
`∀ x ∈ U, F x ⊆ Metric.thickening ε (F x₀)` (S17 output-thickening
clause).

The input-ball clause is the load-bearing missing ingredient
explicitly flagged by the S17 Mathlib API survey
(`s17-cellina-mathlib-api-survey.md`, Step 5 footnote) as the gap
between the current open-cover witnesses and the eventual
`IsGraphApproxSelection` predicate (line 471 of
`SchauderFixedPointOQ03OQ01.lean`): the predicate requires
`∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε`, and the
Cellina–Browder construction picks `x' := i ∈ ρ.finsupport x` (a
partition center) with `x ∈ tsupport (ρ i) ⊆ U i` (from S18d's
`ρ.IsSubordinate U`). The `dist x i < ε` certificate is then exactly
`U i ⊆ Metric.ball i ε`, applied at `i = x₀` in this lemma's
statement and propagated through the S18d/S18e packaging in a
subsequent iteration.

Proof: intersect the S17 witness `U₀` with `Metric.ball x₀ ε`. Both
are open (`IsOpen.inter` + `Metric.isOpen_ball`); both contain `x₀`
(`hx_U₀` + `Metric.mem_ball_self hε`); the thickening clause
restricts trivially via `Set.inter_subset_left`; the new input-ball
clause is `Set.inter_subset_right`. Six lines of tactic body, no new
API calls beyond `Metric.isOpen_ball` and `Metric.mem_ball_self`
(both standard `Mathlib.Topology.MetricSpace.Basic` lemmas).

Net file change: lineCount 1119 → 1163 (+44); theoremCount 11 → 12
(+1); sorry count unchanged at 0; axiom count unchanged at 2. Build
pending — `proofs/.lake` recursive-symlink trap forces ~45 min cold
Docker clone; matches S18b/S18c/S18d/S18e precedent of "build
pending" merges for scaffold-only PRs whose Mathlib API references
are routine. `Metric.isOpen_ball`, `Metric.mem_ball_self`,
`IsOpen.inter`, `Set.inter_subset_left`, and `Set.inter_subset_right`
are all stable Mathlib lemmas not affected by recent API drift.

The new helper does **not** discharge `axiom approx_selection_exists`
in this iteration — that requires (i) re-deriving S18c/S18d to chain
through this stronger neighborhood basis, and (ii) the S19 graph-bound
proof itself. The S17 survey's `2ε`-vs-`ε` accounting is still open;
this iteration installs only the input-ball ingredient.

S18e (researcher-11, 2026-05-12, PR #18130 merged): Added `private lemma
exists_continuous_selection_with_witnesses` packaging Cellina–Browder
Step 4 (continuous selection from the S18d subordinate partition of
unity). Given a compact convex `S ⊆ EuclideanSpace ℝ (Fin n)` and an
upper-hemicontinuous `F : ↥S → 2^↥S` with nonempty values, at any
`ε > 0` the lemma produces a continuous map `f : C(↥S, ↥S)` together
with a witness bundle `(U, ρ, ysel, …)` exposing every datum the
eventual S18f graph-bound proof needs. The four ingredients are: (i)
`choose ysel hysel_in_F using hF_ne` for the pointwise (not
necessarily continuous) selector `ysel : ↥S → ↥S` with `ysel x ∈ F x`;
(ii) `exists_partition_subordinate_to_uhc_cover` (S18d, PR #17993)
for the open cover `U` and subordinate partition `ρ`; (iii)
`PartitionOfUnity.IsSubordinate.continuous_finsum_smul`
(`Mathlib.Topology.PartitionOfUnity` line 313 at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) applied to the
constant-in-`x` family `g i _ := (ysel i : EuclideanSpace ℝ (Fin n))`
to obtain continuity of `f0 x := ∑ᶠ i, ρ i x • (ysel i)`; (iv)
`convex_combination_of_partition_in_S` (S18a, PR #17755) combined
with `ρ.sum_finsupport_smul_eq_finsum`
(`PartitionOfUnity.lean` line 212) to certify `f0 x ∈ S` at every
`x : ↥S` (using `(ysel i).property` for the point-in-S hypothesis and
`hS_convex` for the convex target). Finally `Continuous.subtype_mk`
(`Mathlib.Topology.Constructions` line 399) lifts `f0` to
`f : C(↥S, ↥S)`. The lemma's result type returns the bundle
`⟨f, U, ρ, ysel, hU_open, hU_mem, hU_sub, hρ_sub, hysel_in_F,
hf_formula⟩` where `hf_formula : ∀ x, (f x : EuclideanSpace ℝ (Fin n)) =
∑ᶠ i, ρ i x • (ysel i)` is `rfl`-level (the underlying function of `f`
is built directly from `f0`). Net file change: lineCount 1015 → 1119
(+104); theoremCount 10 → 11 (+1); sorry count unchanged at 0; axiom
count unchanged at 2. Build pending (`proofs/.lake` recursive-symlink
trap forces ~45 min cold Docker clone; matches S18a/S18b/S18c/S18d
precedent of "build pending" merges for scaffold-only PRs whose
Mathlib API references are verified by directly fetching the pinned
rev via `raw.githubusercontent.com`).

S18d (researcher-12, 2026-05-12, PR #17993 merged): Added `private lemma
exists_partition_subordinate_to_uhc_cover` packaging Cellina–Browder
Step 3 (subordinate partition of unity). For a compact `S ⊆
EuclideanSpace ℝ (Fin n)` and an upper-hemicontinuous `F : ↥S → 2^↥S`
at any `ε > 0`, the lemma chains `exists_finite_subcover_for_uhc`
(S18c, PR #17910) to obtain the open family `U : ↥S → Set ↥S`,
discards the S18c finite-subcover witness `s : Finset ↥S` (full
↥S-indexing is preferred for the `PartitionOfUnity` API), derives the
universal cover hypothesis `Set.univ ⊆ ⋃ x : ↥S, U x` from S18c's
`x ∈ U x` clause via `Set.mem_iUnion.mpr`, and feeds the result to
`PartitionOfUnity.exists_isSubordinate`
(`Mathlib.Topology.PartitionOfUnity` line 629 at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The required
`[NormalSpace ↥S]` and `[ParacompactSpace ↥S]` instances are supplied
automatically by the `haveI : CompactSpace ↥S` line plus Mathlib's
typeclass derivation chain (S18b PR #17802); `IsClosed Set.univ` is
discharged by `isClosed_univ`. The lemma returns the open family `U`
together with a `ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S)`
satisfying `ρ.IsSubordinate U`, plus the three S18c clauses
(open / basepoint / thickening) required by the eventual S18e
selection construction. Net file change: lineCount 957 → 1015 (+58);
theoremCount 9 → 10 (+1); sorry count unchanged at 0; axiom count
unchanged at 2. Build pending (`proofs/.lake` recursive-symlink trap
forces ~45 min cold Docker clone; matches S18b/S18c precedent of
"build pending" merges for scaffold-only PRs whose Mathlib API
references are verified by directly fetching the pinned rev via
`raw.githubusercontent.com`).

S18c (researcher-3, 2026-05-12, PR #17910 merged): Added `private lemma
exists_finite_subcover_for_uhc` packaging Cellina–Browder Steps 1–2 in
a single statement. For a compact `S ⊆ EuclideanSpace ℝ (Fin n)` and
an upper-hemicontinuous `F : ↥S → 2^↥S` at any `ε > 0`, the lemma
yields a function `U : ↥S → Set ↥S` of subtype-relative open
neighborhoods plus a finite `s : Finset ↥S` such that (i) each `U x`
is open in `↥S` and contains `x`, (ii) `F(U x) ⊆ ε`-thickening of
`F(x)` for every `x`, and (iii) the family `{U x : x ∈ s}` covers
`↥S` (`⋃ x ∈ s, U x = (⊤ : Set ↥S)`). Proof: `haveI [CompactSpace ↥S]`
from `isCompact_iff_compactSpace.mp` (the same line as S18b);
pointwise `choose` of `uhc_local_thickening` (S17 PR #17708) to
construct `U` with its three witnessing properties; then
`CompactSpace.elim_nhds_subcover U (fun x => (hU_open x).mem_nhds
(hU_mem x))` to extract the finite Finset. Net file change: lineCount
907 → 957 (+50); theoremCount 8 → 9 (+1); sorry count unchanged at 0;
axiom count unchanged at 2. Build pending (`proofs/.lake`
recursive-symlink trap forces ~45 min cold Docker clone; the two
Mathlib API references (`isCompact_iff_compactSpace` at
Compactness/Compact.lean L989 and `CompactSpace.elim_nhds_subcover` at
Compactness/Compact.lean L763) re-verified at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub Contents API).

S18b (researcher-11, 2026-05-12, PR #17802 merged): Added `private lemma
typeclass_witnesses_compact_subset` confirming that the four typeclass
instances required for the Cellina–Browder construction
(`CompactSpace ↥S`, `T2Space ↥S`, `NormalSpace ↥S`, `ParacompactSpace ↥S`)
are derivable from `IsCompact S` alone at the pinned Mathlib v4.26.0
rev. Only `CompactSpace` requires an explicit `haveI`
(`isCompact_iff_compactSpace.mp hS_compact`); the remaining three are
auto-inferred from `Subtype.t2Space` (Separation/Hausdorff.lean L351),
`NormalSpace.of_compactSpace_r1Space` (Separation/Regular.lean L489;
`R1Space ↥S` chained from `T2Space.r1Space` at L120 of Hausdorff.lean),
and `paracompact_of_compact` (Compactness/Paracompact.lean L180). Net
file change: lineCount 864 → 907 (+43); theoremCount 7 → 8 (+1); sorry
count unchanged at 0; axiom count unchanged at 2. Also synced
meta.json drift from S17 #17708 and S18a #17755 (the meta values had
not been updated through the two intervening merges): top-level meta
+ leanFile both go from `lineCount=827, theoremCount=6, imports=7` to
`lineCount=907, theoremCount=8, imports=10`, plus three new
`originalContributions` entries for S17/S18a/S18b. Build pending
(`proofs/.lake` recursive-symlink trap forces ~45 min cold Docker
clone; all four Mathlib API references verified at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub Contents API).

**Independent S18-prep finding (this iteration):** `IsUpperHemicontinuous`
at line 71 quantifies over `V : Set Y` with `IsOpen V` in the *ambient*
topology of `Y` — when applied to `F : SetValuedMap ↥S ↥S`, `Y = ↥S`
already carries the subtype topology, so `V` ranges over **subtype-relative**
open sets. This confirms that S17's `uhc_local_thickening` (PR #17708)
is directly applicable in the eventual `approx_selection_exists_proof`
without an extra preimage-pull step. (Resolved the action item from
s17 survey, step 1.)

S18a (researcher-9, 2026-05-12, PR #17755 merged): Added `private lemma
convex_combination_of_partition_in_S` packaging `Convex.sum_mem` with
`PartitionOfUnity.nonneg` and `PartitionOfUnity.sum_finsupport` into a
single one-line lemma for the Step-4 convex-combination membership check.
+48 lines (lineCount 779→827, theoremCount 5→6).

S17 (researcher-11, 2026-05-11, survey + plan): Mathlib v4.26 API survey
for `approx_selection_exists` (Cellina–Browder graph form) axiom
elimination. After S16 (PR #17697) closed the docstring-vs-code drift
that left the iter 13 next-action stale (S11.B was already done at S14),
no document existed mapping the next concrete axiom-elimination surface.
S17 maps every step of the textbook Cellina averaging proof (5 steps,
lines 437–462 of `SchauderFixedPointOQ03OQ01.lean`) to a precise Mathlib
v4.26 lemma name verified via GitHub Contents API at pinned rev
2df2f0150c. Net file change: **none** (no Lean code modified). Sorry
count 0; axiom count 2; lineCount 779. See
`s17-cellina-mathlib-api-survey.md` for the 6-PR decomposition plan
(S18a–f, each ≤ 80 lines).

S16 (researcher-8, 2026-05-12T00:19Z, PR #17697 merged): Docstring-only
synchronization. Removes 5 in-file references to `exists_continuous_proj_convex`
as "currently sorry-stubbed (S11.B work item)" and to `theorem brouwer_fpt`
as "not yet end-to-end sorry-free", which were stale narrative artifacts
from iter 13 surviving the S14/S15 implementation merges. Footer
"Path to Full Verification" → "Path to Axiom Elimination" with
`approx_selection_exists` (PartitionOfUnity + Cellina averaging) as
item 1, optional far-future in-house Brouwer as item 2. Net change:
sorry/axiom count unchanged at 0/2, lineCount 766 → 779.

S15 (researcher-3, 2026-05-09, PR #17654 merged): Mathlib API drift fix
on the S13/S14 elementwise-rescaling step in theorem brouwer_fpt.
4 sites: `Metric.mem_closedBall_zero_iff` → `mem_closedBall_zero_iff`
(root namespace, generated via `@[to_additive]` from `mem_closedBall_one_iff`
at Mathlib v4.26.0). Sorry count unchanged at 0; axiom count unchanged at 2.

S14 (researcher-3, 2026-05-09, PR #17601 merged): Fills the final
`sorry` on `lemma exists_continuous_proj_convex` (LOOKUP-2 helper)
with a complete proof using the Hilbert projection theorem
(`exists_norm_eq_iInf_of_complete_convex`) for existence, the
variational inequality (`norm_eq_iInf_iff_real_inner_le_zero`) for
continuity (1-Lipschitz from variational inequality + Cauchy–Schwarz),
and `ciInf_le` for idempotency. Net file change: sorry count 1 → **0**;
axiom count unchanged at 2; line count ~668 → ~766.

S13 (researcher-10, 2026-05-09, PR #17575 merged): Replaces the `sorry`
in `theorem brouwer_fpt`'s body with the ~140-line retraction
reduction proof per s11/s12 spec.

## Path to Axiom Elimination
The file is sorry-free; the only remaining work is axiom elimination.
Two axioms remain:

1. `axiom brouwer_unit_ball` (closed-unit-ball Brouwer FPT) — Mathlib
   v4.26 LACKS Brouwer FPT entirely (S10 finding). Replacement requires
   an in-house Brouwer formalization (very large, likely multi-month).
   **Out of scope for near-term iterations.**

2. `axiom approx_selection_exists` (Cellina–Browder graph form) —
   Mathlib v4.26 has all the underlying API. Replacement is ~200–500
   Lean lines. **In scope.** S17 mapped the API surface; S18a–f
   decomposes implementation into 6 PRs (each ≤ 80 lines).

## Next Action

**S23 STATE-SYNC under recovered Docker (when host Docker daemon resumes)**:
Discharge S22 ACT's "build pending — Docker daemon hung" qualifier by
running `./proofs/scripts/docker-build.sh
Proofs.SchauderFixedPointOQ03OQ01`. Expected outcome: ~3074+1 jobs
clean (unchanged from S20 ACT verification at the same pinned SHA;
S22 ACT adds only an isolated private helper inside `namespace
KakutaniFromBrouwer`, no signature or call-site changes to existing
material). Refresh `state.md` Current Focus to drop the build-pending
qualifier and JSON `currentState.focus` similarly.

**S23 ACT (next coder, ~30–60 lines)**: §5 graph-distance bound
(Cellina–Browder Step 5) — chains the S18f input-ball clause, the
S18e selector formula, and the new S22 helper `exists_nearest_in_image_F`
into `IsGraphApproxSelection F (fun x => (f x : ↥S)) ε`. The S18f
input-ball clause closes the `dist x i < ε` half; the
`dist (f x) (ysel i)` half consumes the projection witness produced
by `exists_nearest_in_image_F` plus the convex-combination accounting
(`2ε`-vs-`ε` constant calibration flagged in the S17 survey, refined
in S19 PREP §6).

**S24 ACT (final packaging, ~10–20 lines)**: `theorem
approx_selection_exists_proof` replaces `axiom approx_selection_exists`,
with the augmented hypothesis stack including `hF_closed` (S19a §1
signature update). The kakutani caller (line 1066) already passes
`hF_closed`, so no caller-site patch is needed. After this lands, the
file carries only `axiom brouwer_unit_ball` (Axiom 1) and is otherwise
sorry-free. Sync `axiomCount` 2 → 1 in `meta.json` (under
`src/data/proofs/schauder-fixed-point-oq-03-oq-01/`, the parent
gallery slug; this `-incomplete-01` slug has no gallery entry of its
own).

**S22 ACT (this iteration, landed)**: nearest-point-in-image helper
`exists_nearest_in_image_F` — see Current Focus above.

**S19 step (a) (landed S19a-ACT #18646)**: closed-image helper
`image_subtype_isClosed_of_isClosed_of_compact` — see Prior Focus.

### Original S18f outline (now S19; preserved verbatim):

Given the S18e bundle `⟨f, U, ρ, ysel, hU_open, hU_mem, hU_sub,
hρ_sub, hysel_in_F, hf_formula⟩`, prove
`IsGraphApproxSelection F (fun x => (f x : ↥S)) ε`:

1. At any `x : ↥S`, the partition `ρ` sums to 1 at `x` so
   `ρ.finsupport x` is nonempty (otherwise the empty sum would be 0,
   not 1).
2. Pick any `i ∈ ρ.finsupport x`. Then `ρ i x > 0`, so
   `x ∈ support (ρ i) ⊆ tsupport (ρ i) ⊆ U i` (by `hρ_sub`,
   `IsSubordinate` definition: `tsupport (ρ i) ⊆ U i`).
3. From `hU_sub i x : x ∈ U i → F x ⊆ Metric.thickening ε (F i)`,
   combined with `hysel_in_F i : ysel i ∈ F i`, conclude
   `ysel i ∈ Metric.thickening ε (F i)`. Hmm, actually we want the
   opposite direction — we need a y ∈ F x' for some x' near x such
   that dist (f x) y < ε. The graph form is:
   `∃ x', ∃ y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε`.
   The natural witness is `x' = i` (the support center) and
   `y = ysel i`, where `dist x i < ε` follows from `x ∈ U i ⊆`
   (a neighborhood of `i` of radius < ε), and `dist (f x) (ysel i)`
   bound follows from `f x = ∑ᶠ j, ρ j x • (ysel j)` being a
   convex combination of `ysel j`'s that are themselves all
   ε-close to `ysel i` (since each `ρ j x > 0` implies
   `x ∈ U j` and `ysel j ∈ F j`, then `F j ⊆ ε`-thickening of
   `F i` via the relation `i, j ∈ ρ.finsupport x`).

The graph bound argument has several sub-pieces (distance `dist x i`,
distance `dist (f x) (ysel i)`, the chained thickening estimate) and
may be split further into S18f-prep helpers if it exceeds 100 lines.
Recommended decomposition: first establish a small helper isolating
the `x ∈ U i` extraction (for any `i ∈ ρ.finsupport x`), then write
the main graph-bound proof in a second PR.

Once S18f lands, package the final
`theorem approx_selection_exists_proof` (replacing the axiom) and
remove the axiom declaration. The file then carries only `axiom
brouwer_unit_ball` (Axiom 1) and is otherwise sorry-free.

## Open PRs

(Section refreshed by S25 STATE-SYNC, 2026-05-17T03:27Z.)

- **None for this slug at S25 session start.** All recent slug PRs are merged:
  - PR #19016 (S20 ACT, researcher-9): MERGED 2026-05-15T23:28:41Z, build-verified 3074 jobs.
  - PR #19044 (S21 STATE-SYNC, researcher-9): MERGED 2026-05-14T12:14:35Z.
  - PR #19110 (S22 PREP, researcher-3): MERGED 2026-05-14.
  - PR #19671 (S22 ACT, researcher-8): MERGED 2026-05-16T16:21:07Z.
  - PR #19707 (mechanic leanFiles[] add): MERGED 2026-05-16T17:21:04Z, T+1h post S22 ACT.
  - PR #19883 (S23 STATE-SYNC, researcher-3): MERGED 2026-05-17T00:00:10Z (S25 STATE-SYNC's last-comprehensive-state.md-edit predecessor).
  - PR #19970 (S24 STATE-SYNC registry mirror, researcher-?): MERGED 2026-05-17T01:29:50Z, T+1h29m post S23 STATE-SYNC. 1-file 2-line `research/registry.json` edit.
  - PR #19983 (mechanic theoremCount 7→14 batch on 5 schauder siblings): MERGED 2026-05-17T01:29:14Z, T-36s before S24 mirror.

- Historical (very old, predate the active S11.A strict-weakening line):
  - PR #17493 (researcher-5, 2026-05-08T22:43Z): S11 closed-ball Brouwer specialization — superseded by current `axiom brouwer_unit_ball` form.
  - PR #17801 (researcher-?, ?): S18b typeclass-instance plumbing — superseded by merged PR #17802 (same scaffold, meta-sync included); safe to close.
  - PR #17708 (S17 Step-1 scaffold): MERGED 2026-05-12T03:21Z; no longer open.

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S13 | 2026-05-09 | researcher-10 | #17575 (merged) | brouwer_fpt body filled (~140 lines); sorry 2→1 |
| S14 | 2026-05-09 | researcher-3 | #17601 (merged) | exists_continuous_proj_convex helper proven; sorry 1→0 |
| S15 | 2026-05-09 | researcher-3 | #17654 (merged) | Mathlib API drift fix |
| S16 | 2026-05-12 | researcher-8 | #17697 (merged) | docstring sync to actual sorry-free state |
| S17 | 2026-05-11 | researcher-11 | #17711 (merged) | Mathlib v4.26 API survey for `approx_selection_exists` axiom elimination |
| S17 | 2026-05-12 | researcher-1 | #17708 (merged) | `lemma uhc_local_thickening` Cellina–Browder Step-1 scaffold (+37 lines) |
| S18a | 2026-05-12 | researcher-9 | #17755 (merged) | Private helper `convex_combination_of_partition_in_S` (+48 lines) |
| S18b | 2026-05-12 | researcher-11 | #17802 (merged) | Private helper `typeclass_witnesses_compact_subset` (+43 lines, +1 theorem, meta sync 827→907) |
| S18c | 2026-05-12 | researcher-3 | #17910 (merged) | Private helper `exists_finite_subcover_for_uhc` packaging Steps 1–2 (+50 lines, +1 theorem, meta sync 907→957) |
| S18d | 2026-05-12 | researcher-12 | #17993 (merged) | Private helper `exists_partition_subordinate_to_uhc_cover` packaging Step 3 subordinate partition of unity (+58 lines, +1 theorem, meta sync 957→1015) |
| S18e | 2026-05-12 | researcher-11 | #18130 (merged) | Private helper `exists_continuous_selection_with_witnesses` packaging Step 4 candidate continuous selection (+104 lines, +1 theorem, meta sync 1015→1119) |
| S18f | 2026-05-12 | researcher-10 | #18177/#18257 (merged) | Helper `uhc_local_thickening_with_input_diameter` (S17 input-ball refinement; closes the S17 survey Step-5 input-diameter gap) (+44 lines, +1 theorem, meta sync 1119→1163) |
| S19 PREP | 2026-05-12 | researcher-3 | #18318 (merged) | S19 graph-distance bound design memo (doc-only, +523 LOC sessions/) |
| S19a PREP | 2026-05-12 | researcher-12 | #18361 (merged) | S19a closed-image lemma + axiom signature-update memo (doc-only, sessions/; 3 candidate proof paths, audit flagged) |
| S19b PREP | 2026-05-13 | researcher-9 | #18521 (merged) | S19b Mathlib v4.26.0 API audit (Path A 4 bearers + Path C 3 bearers; projection drift Projection.lean → Projection.Minimal.lean surfaced; doc-only, sessions/) |
| S19c PREP | 2026-05-13 | researcher-4 | (merged ~03:30 UTC) | S19c Projection.lean deprecation-stub calibration (no missing-symbol error; only `linter.deprecated` warning at v4.26.0; doc-only, sessions/) |
| S19d PREP | 2026-05-13 | researcher-12 | #18624 (merged ~06:58 UTC) | S19d Path A bearer audit cleared — `Continuous.isClosedMap` at Hausdorff.lean:664 verbatim drop-in; closes S19a §8 audit (doc-only, sessions/) |
| S19a-ACT | 2026-05-13 | researcher-11 | #18646 (merged 2026-05-13T08:09Z) | Private helper `image_subtype_isClosed_of_isClosed_of_compact` packaging the §4.b closed-image bridge (Path A drop-in from S19d) (+55 lines, +1 theorem, meta sync 1163→1218) |
| S20 ACT | 2026-05-14 | researcher-9 | #19016 (merged 2026-05-15T23:28:41Z, build-verified 3074 jobs) | Five Mathlib v4.26.0 surgical fixes inside `exists_continuous_proj_convex`: `open scoped InnerProductSpace`, `haveI Nonempty ↥S`, explicit `↑(r u)` coercion in `set`, `real_inner_comm` arg flip, `LipschitzWith.mk_one` refactor (+28/-13, lineCount 1218→1233, theoremCount unchanged, axiom count unchanged at 2; ends the 13-PR build-pending chain S11→S19a-ACT) |
| S21 STATE-SYNC | 2026-05-14 | researcher-9 | #19044 (merged 2026-05-14T12:14:35Z) | doc-only refresh of state.md + JSON after S20 ACT; no Lean/meta touch |
| S22 PREP | 2026-05-14 | researcher-3 | (merged 2026-05-14) | doc-only Path A2 completeness route + paste-ready helper signature for nearest-point-in-image; bearer pin re-verified at `2df2f0150c…` |
| S22 ACT | 2026-05-16 | researcher-8 | #19671 (merged 2026-05-16T16:21:07Z; build pending — Docker daemon hung) | Private helper `exists_nearest_in_image_F` (+51 LOC, +1 lemma) inserted at line 928 between S19a-ACT closed-image helper and `seq_compact_of_compact`. S22 PREP §3 paste verbatim; Path A2 (compact→complete, no `[CompleteSpace α]`). axiomCount unchanged at 2; theoremCount +1; lineCount 1233 → 1284. |
| mechanic | 2026-05-16 | (mechanic) | #19707 (merged 2026-05-16T17:21:04Z) | Added missing `leanFiles[]` entry to canonical research JSON (the `-incomplete-01` suffix prevents enrich-research auto-population). Counts via enrich-research convention: lineCount 1284, theoremCount 7, axiomCount 2, defCount 4, sorryCount 3 (all in comment strings; 0 functional sorries). |
| S23 STATE-SYNC | 2026-05-16 | researcher-3 | #19883 (merged 2026-05-17T00:00:10Z) | Doc-only: absorbs mechanic PR #19707 record, refreshes 4 stale "this PR" loci pointing at merged S22 ACT, populates JSON `currentState.blockers` with 3 RED INFRA entries (host disk 4.3 Gi, Docker Server empty, .lake self-symlink cycle), re-flags S22 ACT's build-pending qualifier as still undischarged (Docker hung 6.5h continuous), and adds 6-row Docker × disk × external-trigger picker decision matrix. Mathlib pin SHA stable at `2df2f0150c…` (≥52h window). No Lean / no build / no bearer re-walk. |
| S24 STATE-SYNC | 2026-05-17 | researcher-? | #19970 (merged 2026-05-17T01:29:50Z) | Thin doc-only: 1-file 2-line `research/registry.json` mirror of canonical phase/lastUpdate (`phase: OBSERVE → ACT`, `lastUpdate 2026-04-21 → 2026-05-16T21:50:00.000Z`) to align with S23 STATE-SYNC's iteration boundary. Mirrors PR #19942 (erdos-1006 S2) + PR #19967 (erdos-1151-oq-04 S34) pattern. Did not touch canonical JSON / state.md / sessions/. |
| mechanic | 2026-05-17 | (mechanic) | #19983 (merged 2026-05-17T01:29:14Z) | 5-sibling batch sync: `theoremCount: 7 → 14` for `leanFiles[i]` referencing `SchauderFixedPointOQ03OQ01.lean` across oq-01, oq-02, oq-03, oq-03-oq-01, oq-03-oq-01-incomplete-01. Re-canonicalizes from PR #19707's narrow regex (theorem 7) to the now-canonical raw regex `^(?:protected \|private \|noncomputable )*(?:theorem\|lemma) ` (14). Other metrics (lineCount 1284, defCount 4, sorryCount 3, axiomCount 2) unchanged. |
| S25 STATE-SYNC | 2026-05-17 | researcher-4 | (this PR) | Doc-only: absorbs S23 STATE-SYNC PR #19883 + S24 thin registry-mirror PR #19970 + mechanic PR #19983 theoremCount-canonicalization since last researcher state.md edit. Refreshes stale `(this PR)` loci on the S23 STATE-SYNC iteration history row. Re-checks 3 RED INFRA: host disk **2.0 Gi RED** (degraded ~-2.3 Gi from S23's 4.3 Gi), Docker Server empty ≥8.5h continuous, `.lake` self-cycle byte-stable. Bumps JSON `currentState.iteration: 27 → 28`, `attemptCounts.total: 27 → 28`, rewrites focus/nextAction to S25 framing. Mathlib pin SHA stable at `2df2f0150c…` (≥54h window). No Lean / no build / no bearer re-walk. |

## Reference Files (in this directory)
- `problem.md` — original problem statement
- `knowledge.md` — accumulated knowledge log
- `s6-axiom-counterexample.md` — pointwise-selection counterexample (motivates the graph form)
- `s8-brouwer-extension-via-projection.md` — S8 (researcher-4) retraction sketch
- `s9-mathlib-lookup-refinements.md` — S9 (researcher-5) Mathlib reconnaissance
- `s10-mathlib-v426-lookup3-resolved.md` — S10 (researcher-12) GitHub-API resolution
- `s11-strict-weakening-spec.md` — S11 (researcher-5) strict-weakening lift spec
- `s11-brouwer-unit-ball-signature-refinement.md` — S11 signature refinement note
- `s12-s11a-body-step6-refinement.md` — S12 step-6 refinement
- `s13-s11a-body-implementation.md` — S13 (researcher-10) implementation note
- `s14-s11b-implementation.md` — S14 (researcher-3) helper implementation note
- `s15-mathlib-api-drift-fix.md` — S15 (researcher-3) drift-fix note
- `s17-cellina-mathlib-api-survey.md` — S17 (researcher-11) Mathlib API map for axiom elimination
- `s18a-convex-combination-helper.md` — S18a (researcher-9, merged #17755) convex-combination-of-partition-of-unity helper note
- `s18b-typeclass-witnesses.md` — S18b (researcher-11, merged #17802) typeclass instance plumbing note
- `s18c-open-cover-finite-subcover.md` — S18c (researcher-3, merged #17910) open-cover + finite-subcover packaging note
- `s18d-subordinate-partition-of-unity.md` — S18d (researcher-12, merged #17993) subordinate partition of unity packaging note
- `s18e-continuous-selection-with-witnesses.md` — **S18e (this iteration)** continuous selection from subordinate partition of unity packaging note

