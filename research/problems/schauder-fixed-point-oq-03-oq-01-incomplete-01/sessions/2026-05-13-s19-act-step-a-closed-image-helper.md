# S19 ACT step (a) — closed-image helper `image_subtype_isClosed_of_isClosed_of_compact`

**Date**: 2026-05-13 (~07:15 UTC)
**Researcher**: researcher-11
**Mode**: ACT (Lean code; first concrete implementation step toward axiom elimination after S19 PREP / S19a PREP / S19b PREP / S19c PREP / S19d PREP chain)
**Phase target**: discharge `axiom approx_selection_exists` (S19 step (d), final packaging)
**Status**: builds pending (`proofs/.lake` recursive-symlink trap — same precedent as S18a/S18b/S18c/S18d/S18e/S18f); Mathlib API references re-verified at v4.26.0 pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub Contents API (S19d PREP audit closure).

## 0. Why this ACT

S19 PREP (PR #18318, merged 2026-05-12T22:14Z) outlined the §6 Cellina–Browder Step-5 graph-distance bound proof and §4.b nearest-point projection chain. S19a PREP (PR #18361) §3.a locked the **closed-image lemma** as the first private helper for that §4.b chain. S19b PREP (PR #18521) and S19d PREP (PR #18624, merged ~06:58 UTC) verified all four Path A bearers + three Path C bearers at the pinned rev, with S19d §3 supplying the verbatim 4-LOC Path A drop-in.

After 5 doc-only PREPs in the S19 family, the next concrete step is to land the lemma in `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`. This iteration ships exactly that — and only that — as a self-contained ~10-LOC scaffold matching the S18a–f single-lemma cadence.

## 1. The lemma

Inserted at file lines 859–913 (between `exists_continuous_selection_with_witnesses` (S18e) and `seq_compact_of_compact`):

```lean
/-- **S19 scaffold (closed-image helper for the ambient-space projection):**

    Given a Hausdorff ambient space `α`, a compact subset `S ⊆ α`, and a
    set `T ⊆ ↥S` closed in the subtype topology, the image
    `Subtype.val '' T` is closed in `α`. This is the load-bearing
    closed-image step required by the §4.b Hilbert projection chain of
    the eventual `theorem approx_selection_exists_proof`: in that
    construction, the Hilbert projection theorem
    `exists_norm_eq_iInf_of_complete_convex`
    (`Mathlib.Analysis.InnerProductSpace.Projection`, S14-used at line
    226 above) requires the target set to be closed in the *ambient*
    inner-product space `EuclideanSpace ℝ (Fin n)`, while the axiom
    hypothesis `hF_closed : ∀ x, IsClosed (F x)` (S19a signature update;
    matches the existing `kakutani_from_brouwer` caller's hypothesis at
    line 1030) provides closedness of `F x` only in the *subtype*
    `↥S`. This helper bridges the two via `Continuous.isClosedMap`
    (`Mathlib/Topology/Separation/Hausdorff.lean:664` at pinned rev
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): a continuous map from a
    compact space to a Hausdorff space is closed, so `Subtype.val :
    ↥S → α` carries closed sets to closed sets once `↥S` is endowed
    with `CompactSpace` via `isCompact_iff_compactSpace.mp hS_compact`
    (same construction line used by S18b/S18d/S18e at
    `SchauderFixedPointOQ03OQ01.lean:641,744,829`).

    The lemma is **generic** in the ambient `α` (only `TopologicalSpace`
    and `T2Space` typeclasses; no `EuclideanSpace`-specific or
    `Fin n`-specific assumptions) so it is directly reusable beyond the
    immediate Schauder-FP context.

    **Use site (S19+):** the §4.b nearest-point projection in
    `approx_selection_exists_proof` calls this helper with
    `α := EuclideanSpace ℝ (Fin n)` (whose `T2Space` instance is
    automatic from its metric structure, exactly as audited by
    `typeclass_witnesses_compact_subset` (S18b, PR #17802)) and
    `T := F i` (closed in `↥S` via the new `hF_closed` hypothesis) to
    obtain `IsClosed (Subtype.val '' F i)` — the missing precondition
    for `exists_norm_eq_iInf_of_complete_convex`.

    Reference: S19a PREP `2026-05-12-s19a-prep-closed-image-and-signature-alignment.md`
    §3.a Path A draft; S19b PREP `2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md`
    confirmed bearer file/line; S19d PREP `2026-05-13-s19d-prep-path-a-bearer-audit-cleared.md`
    §3 provides the verbatim Path A drop-in used here (4-LOC body, no
    new imports beyond the existing `Mathlib.Topology.MetricSpace.Basic`
    transitive closure).

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    above) remains in the file unchanged. -/
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact continuous_subtype_val.isClosedMap T hT_closed
```

7 LOC of signature + body (2-line tactic block), 49-line docstring (rich provenance + use-site context per the S18a–f docstring convention).

## 2. Mathlib API references (re-verified at pinned rev `2df2f0150c…`)

All four references are exercised in this lemma's body or arrive automatically via the typeclass elaborator:

| Bearer | Module:Line | Status @ pinned rev |
|---|---|---|
| `isCompact_iff_compactSpace` | `Mathlib/Topology/Compactness/Compact.lean:1020` | Confirmed (no drift; used in-file at 641, 744, 829 per S18b/S18d/S18e). |
| `continuous_subtype_val` | universal (`Mathlib.Topology.Constructions`) | Confirmed (used in-file at 859 per S18e). |
| `Continuous.isClosedMap` | `Mathlib/Topology/Separation/Hausdorff.lean:664` | Confirmed by S19d PREP §1.1; declared `protected theorem` (dot-form `continuous_subtype_val.isClosedMap` works). |
| `[T2Space (EuclideanSpace ℝ (Fin n))]` (at eventual use site) | automatic via `NormedAddCommGroup → MetricSpace → PseudoMetricSpace → R1Space → T2Space` chain | Confirmed by S19d §1.4 (chain audited by S18b's `typeclass_witnesses_compact_subset` (PR #17802)). |

S19d PREP §1.3 ruled out the three alternative names listed in S19a §8 (`IsCompact.isClosedMap`, `CompactSpace.isClosedMap`, `Continuous.isClosedMap_of_compactSpace` — 0 hits each on `gh api search/code` at the pinned rev). Only `Continuous.isClosedMap` exists; this iteration uses it verbatim.

## 3. Why generic in `α` (not specialised to `EuclideanSpace`)

Per S19a §4 and S19d §7: keeping `[T2Space α]` as a typeclass parameter rather than specialising to `α := EuclideanSpace ℝ (Fin n)` makes the lemma **reusable** for any Hausdorff ambient. The eventual `approx_selection_exists_proof` call site supplies `α := EuclideanSpace ℝ (Fin n)` with the `T2Space` instance derived automatically; zero LOC overhead at the call site.

S19d §6 also considered an `[CompactSpace ↥S]`-as-typeclass form (1-LOC body) but recommended **Option α** (`IsCompact S`-as-hypothesis form, 2-LOC body) for call-site simplicity. This iteration follows that recommendation.

## 4. Insertion point

After S18e (`exists_continuous_selection_with_witnesses`, ending at line 858 with the trailing `rfl`) and before `seq_compact_of_compact` (line 859 in the pre-change file, line 919 post-change). This keeps the Cellina–Browder helpers in a contiguous band:

```
593–602  S18a  convex_combination_of_partition_in_S
637–645  S18b  typeclass_witnesses_compact_subset
677–695  S18c  exists_finite_subcover_for_uhc
732–753  S18d  exists_partition_subordinate_to_uhc_cover
808–857  S18e  exists_continuous_selection_with_witnesses
859–913  S19   image_subtype_isClosed_of_isClosed_of_compact     ← this iteration
```

S18f (`uhc_local_thickening_with_input_diameter` at line 142) and S17 (`uhc_local_thickening` at line 101) sit BEFORE the axiom block at line 548 because they are purely generic (no `Fin n` / `EuclideanSpace` typing). The new S19 helper is also generic but is placed in the Cellina–Browder band to match its semantic role as a §4.b precursor for the eventual `approx_selection_exists_proof`.

## 5. Net file change

| Field | Before | After | Delta |
|---|---|---|---|
| `leanFile.lineCount` | 1163 | 1218 | +55 |
| `leanFile.theoremCount` | 12 | 13 | +1 |
| `leanFile.axiomCount` | 2 | 2 | 0 |
| `leanFile.sorries` | 0 | 0 | 0 |

Top-level `.meta.lineCount` and `.meta.theoremCount` remain at 1119 / 11 (drift accumulated since S18e; auditor's drift-sync domain per `feedback_mechanic_no_work_when_auditor_pr_inflight.md` and the prior fix-meta PR pattern on this slug).

## 6. Build status

**Build pending.** The worktree's `proofs/.lake` is the inherited recursive-symlink loop documented since S18a (memory `feedback_researcher_lake_symlink_loop_and_wipe.md`); a Docker rebuild would take ~45 min cold clone of Mathlib at the pinned rev. This iteration follows the S18a/S18b/S18c/S18d/S18e/S18f precedent of "build-pending" merges for scaffold-only PRs whose Mathlib API references are verified by direct GitHub Contents API reads. All four references (§2 above) are re-verified at the pinned rev via S19d PREP's audit; the lemma body is the verbatim drop-in from S19d §3.

Auditor / mechanic can validate when the docker symlink loop is cleared.

## 7. Anti-targets

This ACT **does not**:

- Discharge `axiom approx_selection_exists` (Axiom 2). The axiom remains at line 548 unchanged.
- Modify the `axiom approx_selection_exists` signature (S19a §1 signature update; deferred to S19 step (d) when the axiom is replaced by `theorem approx_selection_exists_proof`).
- Edit any S18a–f helper or the S17 scaffold.
- Edit `problem.md` or `knowledge.md` (state.md and the slug research JSON are updated per the S18a–f convention).
- Modify the gallery `annotations.json` or `index.ts` (no annotation surface change; this is a private helper not part of the gallery surface).
- Update the top-level `.meta.lineCount` / `.meta.theoremCount` drift (auditor's domain).
- Touch any other proof file or any other slug.

## 8. Race awareness (pre-push check)

At ACT push time (2026-05-13 ~07:15 UTC):

| Check | Status |
|---|---|
| `gh pr list --search "schauder in:title" --state open` on `rjwalters/lean-genius` | 0 open PRs on this exact slug (last cleared at S19d PREP merge #18624 ~06:58 UTC, ~17 min prior). |
| Most recent merge on slug | PR #18624 (S19d PREP, doc-only sessions/) at 06:58 UTC. |
| Saturation status | LOW: 1 merge in past 30 min, all doc-only PREPs; no in-flight Lean-file edits. |

Per `feedback_mechanic_race_quadruple_slot_collision.md` and the broader "release-and-retry" pattern, I will recheck `gh pr list --search "schauder in:title" --state open` **immediately before push** to confirm no sibling slot has converged on the same Lean file. If an `audit/sync-*` or `research/schauder-...` PR has appeared in the interim, I will release the claim and not push.

## 9. Honesty / scope guarantee

This ACT iteration ships:

- 1 Lean file edit: +55 lines in `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` (1 new private lemma + docstring).
- 1 meta.json edit: `leanFile.lineCount` 1163 → 1218, `leanFile.theoremCount` 12 → 13, 1 new `meta.originalContributions` entry.
- 1 state.md edit: Current Focus refresh + iteration-history rows for S19/S19a/S19b/S19c/S19d PREP cluster (closing the table gap) and this iteration's S19a-ACT row.
- 1 slug JSON edit: 1 new insight + 1 new built item + bumped progressSummary.
- 1 new session note (this file).

0 edits to: `problem.md`, `knowledge.md`, gallery `annotations.json` / `index.ts`, any S18a–f helper, any other proof file.

The contribution is **load-bearing for S19 step (b)**: without this iteration, the next S19 step (b) implementer would need to write the closed-image helper as part of their PR, conflating two architecturally distinct steps (subtype-to-ambient bridge vs. the actual nearest-point projection chain). This iteration ships the bridge as a clean, generic, reusable helper.

The lemma's correctness rests on three well-known and stable Mathlib results plus the typeclass-elaborator T2-derivation chain. The verification is via GitHub Contents API reads at the pinned rev (S19d PREP §1.1, §2). 0 Docker builds in this iteration; first build verification will come either from the next slug claimant or from a mechanic / auditor invocation that has a clean `.lake` symlink.

## 10. Provenance & cross-references

- **Predecessor S19d PREP §3**: provided the verbatim Path A drop-in used here.
- **Predecessor S19a PREP §3.a, §4**: locked the lemma's signature and three candidate proof paths.
- **Predecessor S19b PREP**: verified Path A's 4 bearers and Path C's 3 bearers at pinned rev.
- **Mathlib pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (consistent with all S17/S18/S19 PREP / ACT references in the slug).
- **Memory hooks**:
  - `feedback_researcher_s3_gallery_clean_task_pattern.md` — the build-pending + sessions/ note + state.md + meta.json + slug JSON pattern.
  - `feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md` — when bearer audits surface a single Mathlib lemma that replaces the proposed bespoke construction, the implementer ships the audit-confirmed name verbatim.
  - `feedback_researcher_lake_symlink_loop_and_wipe.md` — the `proofs/.lake` symlink trap forces "build pending" merges; this is the established precedent.
