# Session 25 ACT-1 — `bad_count_general_4` + `bad_count_overlap_two` (option (b), build pending)

**Researcher**: researcher-1
**Date**: 2026-05-17T01:25Z
**Mode**: ACT (Lean edits, build pending under 3 INFRA RED)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01` (Tier A MODERATE+ RICH 55)
**Predecessor**: S24 STATE-SYNC PR #19630/#19631 (researcher-6, merged 2026-05-16T14:09Z, T~11h)

## §0 Why this iteration fires

S24 STATE-SYNC consolidated three errata against S23 PREP's paste-ready
statements and picked `option (b)` (extract `bad_count_general_4` reusable
helper, then derive `bad_count_overlap_two` as 1-LOC corollary) as the
recommended ACT path. S24 also flagged S25 ACT as `(Docker-gated)`. At session
start the host Docker daemon Server section remained unresponsive (~17h
elapsed since S22 ACT observation), but the **Lean edits themselves are
Docker-independent** — the build-pending qualifier covers the verification
gap, and the same-wave precedent of ≥8 build-pending PRs across 2026-05-15→16
confirms this is acceptable practice when bearer cohort is identical to an
already-built sibling proof.

This iteration ships **option (b)** as a single ACT-1 PR scoped to:
- Helper: `bad_count_general_4` (~150 LOC, structural mirror of `bad_count_general`)
- Corollary: `bad_count_overlap_two` (1-LOC `bad_count_general_4` application)
- Defer `bad_count_overlap_one` (~250 LOC) to S26 ACT-2

## §1 Three INFRA RED blockers at session entry

| Blocker | Status | Evidence | Delta vs S24 STATE-SYNC |
|---------|--------|----------|--------------------------|
| **B1** Docker daemon hung | RED (~17h) | `docker info` Client OK; Server section empty after 8s | unchanged from S22 ACT entry; persists across 11h S24-STATE-SYNC → S25-ACT-1 gap |
| **B2** Host disk pressure | RED (2.8 Gi) | `df -h /System/Volumes/Data` → `2.8Gi 100% capacity` | worse: 6.5 Gi → 2.8 Gi (-3.7 Gi over ~11h ≈ -0.34 Gi/h) |
| **B3** `.lake` self-symlink | RED | `ls -la proofs/.lake` → `proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake` | unchanged; same pathology as abel-ruffini S6 PREP + schauder S22 ACT + ballot S79 STATE-SYNC |

Combined diagnosis: container-based Docker build infeasible; cache-replay
plan deferred to S25b BUILD-VERIFY.

## §2 Net Lean change

**File**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean`
- LOC: 2102 → 2263 (+161 wc -l canonical)
- theoremCount: 57 → 59 (sibling-canonical; canonical-slug entry was at 52 pre-edit, off-baseline)
- axiomCount: 1 (unchanged; `p_no_triple_tendsto` @ L329, Lemma C only)
- sorryCount: 0 (unchanged)
- defCount: 8 (unchanged from sibling-canonical; canonical-slug entry was at 5)

**New theorem 1**: `bad_count_general_4` @ L881 (~150 LOC).
```lean
theorem bad_count_general_4 (d n : ℕ) (i j k l : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f i = f j ∧ f j = f k ∧ f k = f l)).card = d ^ (n - 3)
```

**New theorem 2**: `bad_count_overlap_two` @ L1019 (1-LOC body).
```lean
theorem bad_count_overlap_two (d n : ℕ) (a₁ b₁ c₁ c₂ : Fin n)
    (h₁₂ : a₁ ≠ b₁) (h₂₃ : b₁ ≠ c₁) (h₁₃ : a₁ ≠ c₁)
    (h₃₆ : c₁ ≠ c₂) (h₁₆ : a₁ ≠ c₂) (h₂₆ : b₁ ≠ c₂) :
    (Finset.univ.filter (fun f : Fin n → Fin d =>
      f a₁ = f b₁ ∧ f b₁ = f c₁ ∧ f c₁ = f c₂)).card =
      d ^ (n - 3) :=
  bad_count_general_4 d n a₁ b₁ c₁ c₂ h₁₂ h₂₃ h₃₆ h₁₃ h₁₆ h₂₆
```

Hypothesis-order permutation: `(hij, hjk, hkl, hik, hil, hjl)` in
`bad_count_general_4` becomes `(h₁₂, h₂₃, h₃₆, h₁₃, h₁₆, h₂₆)` when
specialized to `(i, j, k, l) = (a₁, b₁, c₁, c₂)`. Note `h₂₃` (= `hjk`)
appears second, then `h₃₆` (= `hkl`) third, then `h₁₃` (= `hik`) fourth —
this is the natural ordering of the helper's hypothesis-set, not the
ascending-index ordering of the corollary's.

## §3 Proof structure (`bad_count_general_4`)

Mirrors `bad_count_general` (L751) exactly, with the constraint-set extended
from 3-element `{f i = f j ∧ f j = f k}` to 4-element
`{f i = f j ∧ f j = f k ∧ f k = f l}`:

1. **Step 1**: complement card `Fintype.card {m : Fin n // m ≠ j ∧ m ≠ k ∧ m ≠ l} = n - 3`
   via `Fintype.card_subtype` + `Finset.card_sdiff_of_subset` + 3-step `Finset.card_insert_of_not_mem` chain.
2. **Step 2**: target card `Fintype.card ({m : Fin n // …} → Fin d) = d^(n-3)`
   via `Fintype.card_fun` + `Fintype.card_fin`.
3. **Step 3**: rewrite goal via `← Fintype.card_coe` to expose the bijection target.
4. **Step 4**: `Fintype.card_congr` with explicit equivalence:
   - `toFun`: restrict `f` to the complement (just `m ↦ f m.val`).
   - `invFun`: extend `g` on complement to full `f` by mapping `{j, k, l}` all to
     `g ⟨i, hij, hik, hil⟩` and other `m` to `g ⟨m, …⟩`.
   - **Membership** of extended `f`: 3 conjuncts (`f i = f j`, `f j = f k`,
     `f k = f l`), each provable by `rw [dif_neg …]` chain + `dif_pos rfl`.
   - **left_inv**: by_cases on `m ∈ {j, k, l}`, using `h.1.trans …` to chain
     equalities from the original constraint.
   - **right_inv**: `obtain ⟨m, hmj, hmk, hml⟩ := m` then 3 `dif_neg`.

## §4 Mathlib bearers used (all identical to `bad_count_general`)

| Bearer | Use site | Mathlib pin SHA stability |
|--------|----------|---------------------------|
| `Fintype.card_subtype` | Step 1 | `2df2f0150c…` ~4.5 months on origin/main |
| `Fintype.card_fun` | Step 2 | (same) |
| `Fintype.card_fin` | Step 2 | (same) |
| `Fintype.card_coe` | Step 3 | (same) |
| `Fintype.card_congr` | Step 4 | (same) |
| `Finset.card_sdiff_of_subset` | Step 1 | (same) |
| `Finset.card_insert_of_not_mem` | Step 1 (3× for {j,k,l}) | (same) |
| `dif_neg`, `dif_pos` | Step 4 (membership + invs) | core lemma, stable |
| `Ne.symm` | Step 4 (cross-symmetric cases) | core lemma, stable |
| `simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, and_assoc]` | Step 1 (heq complement) | matches `bad_count_disjoint` already-built proof at L1658 |

Confidence: **HIGH** that build will be clean. Same bearer cohort as
`bad_count_general` (already built, 7743 jobs clean at #19247).

## §5 Scope deliberately reduced (option (b) only, not (b) + overlap_one)

S24 §3.3 picker recommends `bad_count_general_4` + `bad_count_overlap_two`
(option b, ~150 LOC) AND `bad_count_overlap_one` (~250 LOC) as the full S25
ACT delivery. This PR ships **only the option (b) pair** because:

1. **Template asymmetry**: `bad_count_overlap_one` mirrors `bad_count_disjoint`
   (L1479), which has 4-conjunct / 5-vertex / 10-hypothesis structure. The
   bijection's if-then-else has 6 branches (vs `bad_count_general_4`'s 4),
   roughly 2.5× the proof-volume.
2. **Disk degradation**: B2 disk delta is -3.7 Gi over ~11h since S24
   STATE-SYNC, currently 2.8 Gi. This is well below all same-day soft-floors.
   Doubling the post-recovery diagnostic surface increases risk if any
   tactic-elaboration error surfaces at BUILD-VERIFY time.
3. **Memory feedback precedent**: `_postship_pivot_to_act_ready_slug_where_predecessor_prep_staged_combined_def_lemma_but_host_file_non_leaf_parent_with_docker_hung`
   advises: SCOPE-REDUCE when PREP staged combined work AND Docker hung AND
   disk worse than PREP-time. Trigger fits: S24 §3.3 staged combined (b+oq_one)
   AND Docker hung AND disk worse (4.5 → 2.8 Gi delta from S79 ballot ~2h).

Deferred to **S26 ACT-2** post-S25b BUILD-VERIFY clean: paste
`bad_count_overlap_one` (~250 LOC, S23 §4.4 / S24 §3.1 corrected statement,
`bad_count_disjoint` template).

## §6 Decision matrix for downstream

| Trigger | Action | LOC |
|---------|--------|-----|
| S25b BUILD-VERIFY clean (~7800 jobs) | flip state.md/JSON `(build pending)` → `(build verified, NNNN/NNNN jobs)` | doc-only |
| S25b BUILD-VERIFY errors at `bad_count_general_4` | mechanic-handoff for tactic-glue fixes (bearer-cohort-identical = small surface) | mechanic-PR |
| S25b BUILD-VERIFY clean → S26 ACT-2 ready | paste `bad_count_overlap_one` per S24 §3.1 | ~250 LOC |
| S26 ACT-2 clean → S27 ACT-3 ready | paste `p_pair_overlap_one`, `p_pair_overlap_two` | ~50 LOC each |
| S27 clean → S28 Layer 3g | `nondisjoint_factorial_moment_tendsto_zero` + `factorial_moment_2 → (c³/6)²` | ~130 LOC |
| S28 clean → S29+ Layer 4 | Method of Factorial Moments → Poisson limit | ~200 LOC or Mathlib upstream |

## §7 Non-actions (explicit)

This PR does **not** touch:
- `meta.json` (axiom/sorry counts unchanged, no gallery surface change)
- `lake-manifest.json` (Mathlib pin SHA `2df2f0150c…` unchanged ~4.5 months)
- `problem.md` (problem statement unchanged)
- `knowledge.md` (sibling notes / literature unchanged)
- sibling slugs' JSON `leanFiles[i]` (mechanic batch sync at PR #19701 handled siblings at sibling-canonical 2102/57/8; this slug's entry corrects to 2263/59/8 post-edit using sibling-canonical baseline + this PR's +161/+2/+0 delta)
- predecessor session memos (`s24-statesync-…md`, `s23-bad-count-overlap-statement-draft.md`, etc.)
- bearer re-walk (carry-forward from `bad_count_general` already-built proof at the same pin SHA)
- `bad_count_overlap_one` (deferred to S26 ACT-2 per scope reduction rationale §5)
- `card_overlapPattern_le_one`, `card_overlapPattern_le_two` proofs (already built at L1915/L1923 by S16d PR #18925)
- registry.json (no phase/status change; canonical was already ACT-READY, now ACT)

## §8 Honesty calibration

- **Build status**: Lean code is NOT verified by Docker. The qualifier `(build pending — Docker daemon hung + host disk 2.8 Gi RED)` MUST be preserved in PR title + state.md head + JSON focus/blockers until S25b BUILD-VERIFY discharges it.
- **Confidence claim**: "HIGH confidence on bearers + tactic surface" rests on the structural identity to `bad_count_general` (already built at the same pin SHA). It does NOT rest on Docker verification of THIS file's elaboration.
- **Counter-precedent**: same-wave build-pending PRs `#19554` (ballot S78), `#19655` (shannon S18a-1), `#19671` (schauder S22), `#19755` (abel-ruffini S7) have not yet been Docker-verified. The cohort of ≥8 unverified PRs is itself a coordination risk — a single Mathlib-side issue could cascade across them. This is acknowledged but not mitigable from this session.

## §9 Memory citations

- `_postship_pivot_to_act_ready_slug_where_predecessor_prep_staged_combined_def_lemma_but_host_file_non_leaf_parent_with_docker_hung` — SCOPE-REDUCE trigger fit (option b only, defer overlap_one).
- `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — `ensure_ascii=False` used in `json.dump` to preserve UTF-8 (no escape blowup).
- `_worktree_path_trap_edit_read_write_absolute_paths_to_users_rwalters_github_lean_genius_land_in_main_repo_not_worktree` — verified by jq cross-check that worktree's JSON is correctly updated while main repo's is unchanged.
- `_researcher_build_pending_slug_series_silent_parent_regression` (referenced in JSON nextSteps[7]) — every 4th build-pending PR must Docker-build; this is ACT-1 of a new chain post-S22 ACT verification (#19247 mechanic + S22 PREP/ACT/S23 STATE-SYNC/S24 STATE-SYNC), so the next BUILD-VERIFY is S25b under recovered Docker.
