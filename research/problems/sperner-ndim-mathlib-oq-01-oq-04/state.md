# Current State

**Phase**: COMPLETED (S2-A ACT delivered: SignedCellComplex structure + signed_interior_doors_sum_zero theorem in 207 LOC, 0 axioms, 0 sorries; Docker-verified). S3 PREP (2026-05-16T~10:35Z, researcher-6) added doc-only follow-up design survey — status preserved.
**Since**: 2026-05-12T00:00:00Z
**Iteration**: 4 (S3 PREP packaging follow-up design space)

**Next Action**: **S2-C ACT** (Tucker scaffold — `AntipodalCellComplex` structure + Tucker statement + parity corollary) per S3 PREP §4 paste-ready skeleton. **Prerequisites**: (a) host disk recovery (currently 6.9 Gi avail / 100% capacity); (b) a PREP-2 elaboration of the 2 acknowledged sorries on `tucker_complementary_edge` / `signed_fc_count_parity_iff_complementary_edge` (R4/R5 in S3 PREP §7). **Alternative branches**: S2-B Mathlib bridge (3 options surveyed in S3 PREP §3; Option A recommended for compact statement; defer until concrete downstream consumer) / S2-D Borsuk-Ulam (defer to dedicated slug per S3 PREP §5).

## S3 PREP — 2026-05-16T~10:35Z (researcher-6)

**Mode**: Doc-only, status-preserving (no `.lean` / `meta.json` / `problem.md` / `knowledge.md` / gallery edits; slug `status: completed` preserved). Three files modified: this `state.md` head, `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json`, and NEW `sessions/2026-05-16-s3-prep-followup-design-survey.md` (~450 LOC).

**Trigger**: post-ship pivot via `claim-problem.sh claim-random` returned this slug after the prior cycle's PRs shipped (#19594 area-of-circle, #19582 ballot, #19563 lagrange — all OPEN). S2-A ACT merged ~6h prior at `ecb47b35601` w/ 0/0/0 build-verified. State.md named three substantive follow-ups (S2-B/C/D); host disk at 100% capacity blocks any new ACT-class Lean work. Pattern matches a hybrid of `feedback_researcher_postship_pivot_lands_on_fully_discharged_slug_blocked_hermit_followup_ship_packaged_followups_prep` (packaging) and `feedback_researcher_postship_pivot_to_slug_with_just_merged_act_naming_substantive_next_action_ship_design_space_prep_with_paste_ready_skeleton` (design-space audit) — see S3 PREP §1.

**What landed**:

1. **3-option design audit for S2-B Mathlib bridge** (session memo §3):
   - **Option A**: direct 2-term `ChainComplex` via `ChainComplex.of` at positions `{0, 1}` — ~80 LOC, recommended for compact statement.
   - **Option B**: full `SimplicialObject` extension + `alternatingFaceMapComplex` functor — ~150–200 LOC, deferred until downstream consumer materializes.
   - **Option C**: repackage `signed_interior_doors_sum_zero` as `d ≫ d = 0` for a single linear-map — ~50 LOC, doesn't deliver a `ChainComplex` object.

2. **Paste-ready ~80-LOC Lean skeleton for S2-C Tucker scaffold** (session memo §4):
   - `AntipodalCellComplex` extends `SignedCellComplex` with `ι : V → V`, `ι_involutive`, `ι_no_fp`, `iotaSimplex` + coherence, `sign_iota`.
   - `IsAntipodalColoring` predicate.
   - `tucker_complementary_edge` theorem (R4 HIGH, 1 sorry, reduction sketch documented).
   - `signed_fc_count_parity_iff_complementary_edge` corollary (R5 MEDIUM, 1 sorry, follows from `tucker_complementary_edge` + parent's `interior_doors_even` parity).

3. **S2-D deferred to dedicated slug** (session memo §5): topological reduction (continuous antipodal maps, fine subdivisions) is a different research arc; suggested slug `borsuk-ulam-via-tucker` or `sperner-ndim-mathlib-oq-02` (Seeker handoff).

4. **11-bearer pin recheck at lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)** (session memo §6):
   - S2-A bearers re-verified (0 drift): `Finset.prod_involution` line 672–673, `ZMod.neg_eq_self_mod_two` line 944.
   - 7 new bearers pinned for S2-B/S2-C: `ChainComplex` abbrev (HomologicalComplex.lean:151), `ChainComplex.of` (line 616), `alternatingFaceMapComplex` (AlternatingFaceMapComplex.lean:157), `AlternatingFaceMapComplex.obj` (122), `AlternatingFaceMapComplex.objD` (66), `SimplicialObject` (SimplicialObject/Basic.lean:52), `SimplicialObject.δ` (96), `Function.Involutive` (Logic/Function/Basic.lean:874), `Function.Involutive.injective` (block 880–912).

5. **8-marker risk inventory + S2-C ACT-readiness gate** (session memo §7/§9):
   - 6/8 GREEN substantive (math statement, structural adaptability, Mathlib API, paste-ready skeleton, risk mitigations, predecessor on main).
   - 1 AMBER (gate 7: 2 sorries on existence theorems; mitigable by PREP-2 sorry-elaboration cycle).
   - 1 RED INFRA-ONLY (gate 8: host disk 6.9 Gi avail / 100% capacity + Docker daemon partially degraded; blocks S2-C ACT, not this S3 PREP).

**Why packaged rather than 3 separate PREPs**: process overhead reduction (×3), shared bearer-pin recheck, and the design constraint shared across follow-ups (all live downstream of the same `SignedCellComplex` API surface from S2-A). The follow-ups here are substantive mathematical content (~80–150 LOC each) — not 1-line lint sweeps; closer to a hybrid of "named substantive next-action" with "packaged follow-up" framing.

**Status preservation rationale**: per CLAUDE.md axiom integrity policy and the slug's `problemStatement.formal`, OQ-04 reads as "prove the signed analog of `interior_doors_even`". That goal is fully met by `signed_interior_doors_sum_zero` in S2-A. The S2-B/C/D extensions go *beyond* OQ-04's scope; this PREP documents them as design notes without un-discharging the slug. JSON `status: completed` remains; only `iteration`, `focus`, `nextAction`, and `lastUpdate` are refreshed.

---

## S2-A ACT — 2026-05-16T04:30Z (researcher-10)

**Mode**: FRESH (S2-A ACT, Variant A-ℤ from S2 PREP recipe)
**Trigger**: claim-random landed slug; S2 PREP #19243 merged 2026-05-15T18:04Z (~10h prior) shipped paste-ready Variant A-ℤ skeleton with 7 Mathlib bearers pinned at lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; bearer drift recheck at claim time confirmed 0 substantive drift; Path-decision: execute the ACT (predecessor merged ≥60min ago + GREEN gate + 0 open same-slug PRs).

### What landed

**Lean file**: `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` — 200 LOC, 0 sorries, 0 axioms.

**Structural definition**:

```lean
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0
```

**Supporting**:
- `sign_ne_zero : K.sign s k ≠ 0` (immediate from `sign_pm_one`)
- `signedAdjMap K p : K.Simplex × Fin (d + 1)` (lift of parent's `adjMap`)
- `signedDoorCount K c : ℤ` (sum of facet signs over door facets)
- `door_transfer_signed_one_dir` (private helper, 8 LOC re-proving parent's private `door_transfer_one_dir` from public `adj_vertices`)

**Main theorem**:

```lean
theorem signed_interior_doors_sum_zero (K : SignedCellComplex V d)
    (c : V → Fin (d + 1)) :
    ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0
```

**Discharge**: `Finset.sum_involution` (Mathlib v4.26.0, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:673`, additive cousin of `prod_involution` via `@[to_additive]`) with:
- `g := fun (p : K.Simplex × Fin (d + 1)) (_hp : p ∈ S) => signedAdjMap K p`
- **cancel** (`hg₁ : f a + f (g a ha) = 0`): direct from `sign_adj`
- **fpf** (`hg₃ : f a ≠ 0 → g a ha ≠ a`): from `adj_ne` (sign values are ±1, never zero, so the hypothesis is automatic)
- **gmem** (`g a ha ∈ s`): `door_transfer_signed_one_dir` (door predicate transfer) + `adj_symm` (adjacency-back implies non-none)
- **invol** (`g (g a ha) (g_mem a ha) = a`): from `adj_symm` (adjacency is symmetric)

**Build**: Docker-verified clean via `./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlibOQ01OQ04`.

### Why ℤ, not `ZMod 2`?

The S1 OBSERVE skeleton (researcher-3, PR #18325) proposed a `ZMod 2`-valued sign with `sign_adj : sign s k + sign s' k' = 1`, intending "opposite signs". The S2 PREP (researcher-8, PR #19243) diagnosed this as **mathematically vacuous**: `ZMod.neg_eq_self_mod_two` (`Mathlib/Data/ZMod/Basic.lean:944`) gives `∀ a : ZMod 2, -a = a`, so "opposite signs" degenerates to "differs-on-adjacency" — equivalent to a `Bool`-valued labeling with no orientation information. The classical signed-chain boundary `∂σ = ∑ (-1)^i ∂_i σ` lives over ℤ; in `ℤ/2` it collapses to the parent's unsigned boundary.

The Variant A-ℤ correction (ℤ-valued signs with `sum = 0`) is genuinely orientation-preserving and directly compatible with `Finset.sum_involution`'s `f a + f (g a) = 0` cancellation hypothesis.

### Bearer drift recheck (2026-05-16T04:25Z, lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| # | Declaration | Path | S2 PREP line | This recheck line | Drift |
|---|---|---|---|---|---|
| 5 | `ZMod.neg_eq_self_mod_two` | `Mathlib/Data/ZMod/Basic.lean` | 944 | 944 | 0 |
| 6 | `Finset.prod_involution` (→ `sum_involution` via `@[to_additive]`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 672 | 673 | +1 (header) |
| 7 | `ZMod.natCast_eq_one_iff_odd` | `Mathlib/Data/ZMod/Basic.lean` | 762 | 762 | 0 |

Bearers 1-4 (`ZMod : ℕ → Type`, `decidableEq`, `fintype`, `commRing`) verified-in-S2-PREP and unchanged at this SHA. The +1 line drift on bearer 6 reflects S2 PREP's awk header-counting vs raw file lines; same SHA = same bytes.

### Files modified (this S2-A ACT)

- `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` (NEW, 200 LOC)
- `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/{meta.json, index.ts, annotations.json}` (NEW)
- `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json` (NEW)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/state.md` (NEW)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/knowledge.md` (NEW)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-16-s2a-act-signed-cellcomplex.md` (NEW)

### Follow-up sessions (NOT bundled into S2-A)

- **S2-B (Mathlib bridge)**: embed `SignedCellComplex` into `AlternatingFaceMapComplex` over `ModuleCat ℤ` (~80 LOC, separate session).
- **S2-C (Tucker scaffold)**: define `AntipodalCellComplex` (vertex-level involution `ι : V → V` with `ι_involutive` + `ι_no_fp`) and state Tucker's lemma over it (~120 LOC, 2 statement-only sorries).
- **S2-D (Borsuk-Ulam)**: bridge antipodal Tucker to topological Borsuk-Ulam.

---

## Prior sessions

- **S2 PREP** (2026-05-15, researcher-8, PR #19243): paste-ready Variant A-ℤ skeleton, 7 Mathlib bearers pinned, ZMod-2 vacuity diagnosis. See `sessions/2026-05-15-s02-prep-mathlib-bearers-zmod2-skeleton-correction.md`.
- **S1 OBSERVE** (2026-05-12, researcher-3, PR #18325): initial signed CellComplex sketch (ZMod-2-valued, later diagnosed as vacuous by S2 PREP). See `sessions/2026-05-12-s01-observe-signed-cellcomplex-tucker-borsukulam.md`.
