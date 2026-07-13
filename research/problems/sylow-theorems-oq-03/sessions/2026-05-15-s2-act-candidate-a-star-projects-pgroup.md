# S2 ACT — Candidate A* discharge of `sylowProP_projects_pgroup` + OQ-02 v4.26.0 mechanic fix

**Author:** researcher-9
**Timestamp:** 2026-05-15 ~04:30 UTC (initial) / ~05:30 UTC (revised after build #1 surfaced
OQ-02 upstream breakage)
**Phase:** S2 ACT (creates `proofs/Proofs/SylowTheoremOQ03.lean`, adds 1-line import to
`proofs/Proofs.lean`, and applies a 3-cluster mechanic fix to
`proofs/Proofs/SylowTheoremOQ02.lean`).
**Iteration:** 9 (8 doc-only PREP/OBSERVE merges + #18994 STATE-SYNC + this ACT)
**Builds on:**

- S1 OBSERVE — PR #18285 (merged), candidates A/B/C
- S1b OBSERVE — PR #18359 (merged), audit correction; A* recommended
- S2 PREP — PR #18453 (merged), Candidate A* 5-substep decomposition
- S2 PREP-2 — PR #18493 (merged), Candidate B substep decomposition
- S2 PREP-3 — PR #18546 (merged), `frattini_profinite` degeneracy audit
- S2 PREP-4 — PR #18658 (merged), Mathlib bearer audit for Candidate B
- S2 PREP-5 — PR #18685 (merged), typeclass-bridge + deferred API audit
- S2 PREP-6 — PR #18735 (merged), Mathlib bearer audit for Candidate A*
- STATE-SYNC — PR #18994 (OPEN, deployer-stall queue, doc-only)

**Mathlib pin:** v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
confirmed via `proofs/lake-manifest.json`).

## 0. What changed between initial draft and shipped PR

Build attempt #1 (`./proofs/scripts/docker-build.sh Proofs.SylowTheoremOQ03`, ~16 min)
surfaced **6 errors in OQ-02 (lines 247–275)**, none in OQ-03. OQ-02 itself has been
silently broken at v4.26.0 since the Mathlib bump — no merged PR previously documented
this. The errors fall into 3 clusters (all in the `isProP_conj_map` proof + the
`SylowProP.conjBy.isMaximal` block); they are mechanic-grade fixes (≤5 LOC each).

Rather than ship a build-failed ACT scaffold (which is honest but produces no usable
gallery progress), I bundled the 3-cluster mechanic fix into this same PR so the
ACT lands build-verified. The OQ-02 mechanic fix is **scope-justified**: OQ-03 imports
OQ-02 (via `import Proofs.SylowTheoremOQ02`), so without the OQ-02 fix the OQ-03 file
cannot be machine-verified.

## 1. What this ACT adds

| File | Status | Description |
|------|--------|-------------|
| `proofs/Proofs/SylowTheoremOQ03.lean` | NEW (~165 LOC including docstrings + imports + 5 declarations) | The continuity-enhanced replacement theorem `ProfiniteSylow.sylowProP_projects_pgroup_continuous` + 4 supporting lemmas. |
| `proofs/Proofs/SylowTheoremOQ02.lean` | MODIFIED (~12 LOC net: 3 clusters fixed; 1 line collapse via `Subgroup.index_comap_of_surjective`) | v4.26.0 mechanic fix: `Quotient.congr` direction (cluster 1), spurious `symm` in `conjBy.isMaximal` (cluster 2), beta-reduce before `Subgroup.map_map` rewrite (cluster 3). |
| `proofs/Proofs.lean` | MODIFIED (1 line added) | `import Proofs.SylowTheoremOQ03` line inserted alphabetically. |
| `research/problems/sylow-theorems-oq-03/sessions/2026-05-15-s2-act-candidate-a-star-projects-pgroup.md` | NEW | This session log. |

## 2. What this ACT explicitly does NOT do

1. **No edit to `state.md`, `problem.md`, `knowledge.md`, or the slug JSON.** STATE-SYNC
   PR #18994 owns those updates; bumping iter from 8 → 9 will land separately once
   #18994 merges.
2. **No edit to OQ-02's gallery JSON** in `src/data/proofs/sylow-theorems-oq-02/`. The
   OQ-02 `axiom` count remains 5 because this PR does NOT delete the OQ-02 axiom; it
   only repairs the v4.26.0 breakage of the surrounding code. A future iteration may
   delete `axiom sylowProP_projects_pgroup` and route any callers (currently none in
   the gallery) to `ProfiniteSylow.sylowProP_projects_pgroup_continuous`.
3. **No re-claim or status update on this slug.** The standard `release` after PR push
   is sufficient.
4. **No sibling-slug edits** (oq-01, oq-02, oq-04, oq-05 not touched beyond the
   in-scope OQ-02 mechanic fix described in §3).

## 3. OQ-02 v4.26.0 mechanic fix (3 clusters)

### Cluster 1 — `Quotient.congr` direction (lines 245–254 → 1 line)

**Errors observed (build #1):**

- L247:25 — Application type mismatch: `φ.toEquiv` is `↥H ≃ ↥(map (...) H)` but
  `Quotient.congr` expects the opposite direction.
- L249:11 — Failed to synthesize `Membership (↥(map ...) H) (Subgroup ↥H)`.
- L250:19, L250:37 — Cascade of the above on `a` and `b`.

**Diagnosis.** At v4.26.0, `Quotient.congr : {ra : Setoid α} → {rb : Setoid β} →
(e : α ≃ β) → (∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) → Quotient ra ≃ Quotient rb`
(Mathlib/Logic/Equiv/Defs.lean:871). The author intended `(↥(map ...) ⧸ N) ≃ (↥H ⧸ N')`
but passed `φ.toEquiv : ↥H ≃ ↥(map ...)` (the wrong direction).

**Fix.** Replace the 10-line `Quotient.congr`-based bridge with a 1-line application
of the existing Mathlib lemma `Subgroup.index_comap_of_surjective`
(`Mathlib/GroupTheory/Index.lean:70`):

```lean
theorem index_comap_of_surjective {f : G' →* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index
```

Since `N' = N.comap φ.toMonoidHom` and `φ.surjective` follows from `MulEquiv`, the
1-line `(Subgroup.index_comap_of_surjective N φ.surjective).symm : N.index = N'.index`
is exactly the goal at line 243.

**Pin-verification.** `Subgroup.index_comap_of_surjective` was confirmed at lake SHA
`2df2f015...` via `gh api .../Index.lean?ref=<SHA>` + base64. Same SHA, line 70 of
`Mathlib/GroupTheory/Index.lean`.

### Cluster 2 — Spurious `symm`/`.symm` pair in `conjBy.isMaximal` (lines 265 + 280)

**Error observed (build #1):**

- L266:6 — Tactic `apply` failed: goal is `P.toSubgroup = map ... H` but
  `P.isMaximal` conclusion is `map ... H = P.toSubgroup`.

**Error observed (build #2, after removing only L265):**

- L271:4 — Type mismatch: `Eq.symm step` has type
  `map (...) g) P.toSubgroup = H` but expected `H = map (...) g) P.toSubgroup`.

**Diagnosis.** The `SylowProP.isMaximal` field has conclusion `H = toSubgroup` (line 87,
not `toSubgroup = H`). The original `have key` claim is `H.map ... = P.toSubgroup`
which matches the `isMaximal` conclusion direction directly. The `symm` on line 265
flipped the goal to `P.toSubgroup = H.map ...`, which doesn't unify with the term
conclusion. The terminal `exact step.symm` at line 280 was paired with the L265
`symm` — both must move together.

**Fix.** Delete `symm` at line 265 AND delete `.symm` at line 280. The new flow:

- `key : H.map (conj g⁻¹) = P.toSubgroup` (claim unchanged).
- After `apply P.isMaximal (H.map (conj g⁻¹)) ...`, the goal `H.map ... = P.toSubgroup`
  unifies directly with `P.isMaximal ...`'s conclusion (no `symm` needed).
- `step = congr_arg ... key` then proceeds with claim direction unchanged.
- After `rw [hcomp, Subgroup.map_id] at step`, `step : H = P.toSubgroup.map (conj g)`
  matches the goal directly — `exact step` (no `.symm`).

The original `symm`/`.symm` pair appears to have been a relic of an even-older
direction convention; removing both restores consistency.

### Cluster 3 — Beta-reduce before `Subgroup.map_map` rewrite (line 275)

**Error observed:**

- L275:8 — Tactic `rewrite` failed: pattern `map ?g (map ?f ?K)` not found in
  `(fun K => map (...) K) (map (...) H) = (fun K => map (...) K) P.toSubgroup`.

**Diagnosis.** `congr_arg (fun K => K.map (MulAut.conj g).toMonoidHom) key` produces
a term whose two sides are lambda-applications; the `rw` tactic doesn't see through
lambda applications without prior beta-reduction.

**Fix.** Insert `dsimp only at step` between the `congr_arg` and the `rw`:

```lean
have step := congr_arg (fun K => K.map (MulAut.conj g).toMonoidHom) key
dsimp only at step          -- new line: beta-reduce
rw [Subgroup.map_map] at step
```

`dsimp only` (no lemmas) performs definitional simplification including beta-reduction,
revealing the `map ?g (map ?f ?K)` pattern.

## 4. Final declarations in OQ-03 (5 total)

```lean
def restrictToSylowProP : P.toSubgroup →* H

theorem continuous_restrictToSylowProP (hφ_cont : Continuous φ) :
    Continuous (restrictToSylowProP P φ)

theorem isOpen_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    IsOpen (((restrictToSylowProP P φ).ker : Subgroup P.toSubgroup) :
      Set P.toSubgroup)

theorem exists_pow_index_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    ∃ k : ℕ, (restrictToSylowProP P φ).ker.index = p ^ k

theorem sylowProP_projects_pgroup_continuous (hφ_cont : Continuous φ) :
    IsPGroup p (P.toSubgroup.map φ)
```

All five live in `namespace ProfiniteSylow`, inside an inner
`section SylowProjectionsToFinite`. The five `#check` commands at the end of the file
establish their full qualified names.

## 5. Build status

- **Build #1** (initial Lean-only attempt): FAILED at OQ-02 lines 247/249/250/266/275
  (6 errors, 3 clusters). Log: `/tmp/researcher-9-sylow-oq03-s2-build.log`.
- **Build #2** (after cluster 1 collapse + cluster 2 partial fix [removed `symm` only]
  + cluster 3): FAILED at OQ-02 line 271 (1 error, cluster 2 residual — the matching
  `.symm` at the end of the proof needed to move with the L265 `symm`).
- **Build #3** (cluster 2 fully repaired — both `symm` instances removed):
  **SUCCESS, 3062 jobs**, 0 errors, 2 non-blocking lint warnings (see below).
  Log: `/tmp/researcher-9-sylow-oq03-s2-build3.log`.

**Build #3 lint warnings (non-blocking, deferred to a follow-up lint-cleanup PR):**

- L94:0 — `continuous_restrictToSylowProP` doesn't use `[Fintype H]` and
  `[DiscreteTopology H]` from the surrounding `variable` block. Future cleanup:
  add `omit [Fintype H] [DiscreteTopology H] in` before the theorem.
- L142:32 — `Subgroup.coe_subtype` in the `himg_eq_range` simp set is unused.
  Future cleanup: remove from the simp argument list.

Neither warning affects machine-verification correctness; the build completes
successfully and all 5 `#check` declarations confirm the expected fully-elaborated
signatures.

## 6. Effect on OQ-02 axiom count and OQ-03 status

| Item | Pre-PR | Post-PR | Notes |
|------|--------|---------|-------|
| OQ-02 build status (v4.26.0) | broken (6 errors) | clean | 3-cluster mechanic fix. |
| OQ-02 `axiom` count (`grep -c "^axiom " SylowTheoremOQ02.lean`) | 5 | 5 (unchanged) | This ACT does not delete the OQ-02 axiom — only mechanic-repairs the surrounding code. |
| OQ-02 `sorry` count | 0 | 0 (unchanged) | — |
| OQ-03 status | doc-only-PREP-saturated, no Lean file | Lean-file shipped, 0 sorries, 0 axioms in new file | First Lean-file content on OQ-03. |

Per CLAUDE.md's Axiom Integrity Policy: the new theorem
`sylowProP_projects_pgroup_continuous` is fully machine-checked (no axioms, no
sorries, no structure-encoded assumptions). The *mathematical* claim of the OQ-02
axiom is now provable for the continuity-enhanced signature, but the OQ-02 axiom
block itself remains in OQ-02 (with `IsProfiniteGroup G`, `Fact p.Prime`, and
`Function.Surjective φ` in its signature) — a future deletion PR is needed to drop
OQ-02's count from 5 to 4.

## 7. Pre-push race awareness

`gh pr list --search "sylow-theorems-oq-03 in:title" --state open
-R rjwalters/lean-genius` at session start: **1 open PR (#18994 STATE-SYNC, doc-only,
CLEAN/MERGEABLE).**

File-overlap audit with #18994:

| #18994 modified file | This ACT modifies? |
|----------------------|---------------------|
| `research/problems/sylow-theorems-oq-03/sessions/2026-05-14-state-sync-s2-prep-backlog.md` | NO (different timestamp) |
| `research/problems/sylow-theorems-oq-03/state.md` | NO |
| `src/data/research/problems/sylow-theorems-oq-03.json` | NO |

This ACT modifies: `proofs/Proofs/SylowTheoremOQ03.lean` (new),
`proofs/Proofs/SylowTheoremOQ02.lean` (in-scope mechanic fix, ~12 LOC net),
`proofs/Proofs.lean` (auto-regenerated, +1 line at alphabetical position), and this
session file (new). **Zero file overlap with #18994.**

## 8. Honesty / what could be wrong

- **Build #2 outcome.** The OQ-02 mechanic fix is the load-bearing piece. If
  `Subgroup.index_comap_of_surjective` signature has subtle differences from my
  reading (e.g., implicit args, namespace), the fix may need a small adjustment.
  Fallback: revert to the original 10-line `Quotient.congr` block but flip
  `φ.toEquiv` → `φ.symm.toEquiv` and swap `a/b` references inside.

- **`MulEquiv.surjective`.** `φ : ↥H ≃* ↥(map ...)` has `φ.surjective` via the
  `MulEquiv → Equiv → Surjective` chain (`MulEquiv.surjective` exists at v4.26.0).
  If this turns out to be ambiguous, the explicit `φ.toEquiv.surjective` form works.

- **`dsimp only at step`.** This beta-reduces both sides. If the simp normal form for
  `Subgroup.map_map` shifted between v4.x → v4.26, an additional explicit invocation
  might be needed. Fallback: use `show` to rewrite the goal to the beta-reduced form
  manually.

- **`himg_eq_range` simp-set drift (OQ-03 internal).** The OQ-03 proof uses `simp
  [Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP, MonoidHom.comp_apply,
  Subgroup.coe_subtype]`. Per PREP-6 §9, if a Mathlib refactor moves
  `Subgroup.coe_subtype` into a different simp-normal form, this simp set may need
  `SetLike.coe_mk` or `Subgroup.coe_mk` added.

- **Set-coercion chain in `isOpen_ker_restrictToSylowProP`.** The `Subgroup
  P.toSubgroup` vs `Set P.toSubgroup` ambiguity is handled by the explicit inner
  cast (`((restrictToSylowProP P φ).ker : Subgroup P.toSubgroup) : Set P.toSubgroup`).
  If the elaborator still complains, expand `↥P.toSubgroup` explicitly throughout.

- **No callers of the old OQ-02 axiom.** S1b §3 verified zero callers in the gallery;
  pre-push re-grep at S2 ACT time gives the same result (only `SylowTheoremOQ02.lean`
  itself + OQ-03 doc files reference the name). The new theorem is therefore safely
  introducible without breaking downstream code.

## 9. Cross-references

- `proofs/Proofs/SylowTheoremOQ02.lean:33` — `namespace ProfiniteSylow` (shared with
  OQ-03).
- `proofs/Proofs/SylowTheoremOQ02.lean:52-57` — `structure IsProfiniteGroup`.
- `proofs/Proofs/SylowTheoremOQ02.lean:67-69` — `class IsProP` with
  `index_of_open_normal` field (used by `exists_pow_index_ker_restrictToSylowProP`).
- `proofs/Proofs/SylowTheoremOQ02.lean:82-87` — `structure SylowProP` with `toSubgroup`
  and `isProP` fields (used by `restrictToSylowProP` and
  `exists_pow_index_ker_restrictToSylowProP` respectively).
- `proofs/Proofs/SylowTheoremOQ02.lean:134-139` — `axiom sylowProP_projects_pgroup`
  (the discharge target; retained as-is for backward compatibility in this iteration).
- `Mathlib/GroupTheory/Index.lean:70` — `Subgroup.index_comap_of_surjective`
  (cluster 1 fix bearer; new finding from build #1 — not in PREP-1..6).
- `Mathlib/GroupTheory/Index.lean:322` — `Subgroup.index_ker` (Finding I from PREP-6).
- `Mathlib/GroupTheory/PGroup.lean:40` — `IsPGroup.of_card` (Finding IV from PREP-6).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:314` — `MonoidHom.normal_ker` (Finding II
  from PREP-6, instance form).
- `Mathlib/Topology/Order.lean:255` — `isOpen_discrete` (PREP-6 §3.6).
- `Mathlib/Logic/Equiv/Defs.lean:871` — `Quotient.congr` signature (cluster 1
  diagnosis).
- Memory: `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`
  — decision matrix justifying shipping when 1 OPEN PR (doc-only) + 25h deployer stall.
- Memory: `feedback_mechanic_mathlib_v426_birthday_9_cluster_kit.md` and
  `feedback_researcher_buildlog_lint_prep_as_fresh_angle_after_coord_audit.md` —
  v4.26.0 cluster patterns informing the diagnosis.
