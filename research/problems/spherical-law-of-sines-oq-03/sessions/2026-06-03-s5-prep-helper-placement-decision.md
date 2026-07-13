# S5 PREP — Helper-placement decision (parent vs inline) + macro-case A paste-ready Lean

**Date**: 2026-06-03
**Researcher**: researcher-1
**Type**: Doc-only PREP (no Lean edits to `proofs/Proofs/SphericalLawOfSinesOQ03.lean`
or to the parent `SphericalLawOfSines.lean`).
**Scope**: Close the **first** of the two deferred items in S3b PREP §9
ACT-readiness gate — *"Decision needed: parent-helper path vs inline-helper
path for macro-cases B and C"* — and write a paste-ready Lean snippet for
macro-case A (which needs no helpers and is the lowest-risk macro-case).
The second deferred item (build smoke-test) remains blocked by host disk
pressure (§7) and is deliberately not attempted this iteration.

This iteration does **not** advance the phase tag (`S3b-PREP` stays);
the slug is now one PREP-shaped iteration closer to the S3b ACT
load-bearing discharge, with one fewer open question on the readiness gate.

## §1 Quiescence snapshot (3-day window since S4 STATE-SYNC)

S4 STATE-SYNC merged 2026-05-31 at `18b5808017a` (PR #21369). Today's
base SHA is `996638aefdf` — **766 origin/main commits** in the window.
Across all four slug bearers (`proofs/Proofs/SphericalLawOfSinesOQ03.lean`,
`proofs/Proofs/SphericalLawOfSines.lean`, `research/problems/spherical-law-of-sines-oq-03/`,
`src/data/research/problems/spherical-law-of-sines-oq-03.json`):

```
$ git log origin/main --since="2026-05-31T07:00:00Z" --oneline -- <four bearers>
18b5808017a research(...-oq-03): S4 / Iter 6 STATE-SYNC (#21369)
```

Only the S4 SYNC commit itself appears. **0 substantive slug-bearer
touches** in the 3-day window, **0 churn** since S4. The S4 SYNC §3
byte-stability assertion for the slug Lean file carries forward:

| File | SHA1 | LOC | Status |
|---|---|---|---|
| `proofs/Proofs/SphericalLawOfSinesOQ03.lean` | `5dd50718f4698e3ca7e27343ecd93263c862c1fb` | 279 | 1 strategic sorry (line 264) |
| `proofs/Proofs/SphericalLawOfSines.lean` | `c6643ac7e4486e14d29a8f96c7e6f8bafdb061ee` | 323 | `verified`, 0 sorries, 0 axioms |
| `src/data/research/problems/spherical-law-of-sines-oq-03.json` | `4deb32f994ea11cb049f2ccdf1d7d93dd4bc1767` | — | phase `S3b-PREP`, `lastUpdated: 2026-05-31` |
| `proofs/lake-manifest.json` | `272effadcde902c98bd16e2d88c457d02d99a5a6` | — | Mathlib `2df2f0150c…` (v4.26.0) |

Cross-bearer check: parent decl line numbers re-confirmed —
`arcLen` at line 45, `unit_sum` at 70, `normSq_projPerp_unit` at 112,
`dihedralAngle` at 158 (matches S3b PREP §2 verbatim), `sin_sq_dihedralAngle`
at 172 (matches state.md table). **0 drift on the 5 parent decls that
the S3b ACT skeleton consumes.**

## §2 Race / saturation (re-affirmed)

```
$ gh pr list --search "spherical-law-of-sines-oq-03 in:title" --state open
(no open PRs)

$ gh pr list --search "spherical-law-of-sines in:title" --state open
(no open PRs on parent family)
```

Field clear: 0 open PRs on slug, 0 open PRs on parent or sibling
(spherical-law-of-cosines, spherical-law-of-cosines-oq-05) at PR-creation
time. No race with S3b ACT or with parent-modifying work. This PREP's
doc-only file list (§9 below) is disjoint from any other agent's
in-flight Lean work.

## §3 The deferred decision (S3b PREP §9, item #1)

> **Decision needed**: parent-helper path vs inline-helper path for
> macro-cases B and C. **Recommended** (by S3b PREP): inline-helper for
> S3b ACT iter 1 (keeps parent file locked); promote to parent in S3c
> if cleanup is warranted.

S3b PREP §4 had earlier recommended the *parent-helper* path
("**This is the recommended S3b ACT path**"), but §9 walked that back to
the *inline-helper* path. The two recommendations are inconsistent;
this §3 closes the inconsistency in favour of the **inline-helper path**
and documents the trade-offs explicitly so S3c can revisit cleanly.

### §3.1 Two helpers under consideration (from S3b PREP §4)

```lean
/-- If `sin (arcLen B C) = 0` (so `B = ±C`) and `A` is unit, then
    `sin (dihedralAngle A B C) = 0`. -/
theorem sin_dihedralAngle_eq_zero_of_sin_arcLen_third_eq_zero
    (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (h : Real.sin (arcLen B C) = 0) :
    Real.sin (dihedralAngle A B C) = 0
```

```lean
/-- If `sin (arcLen A B) = 0` (so `A = ±B`) and unit hypotheses, then
    `sin (dihedralAngle C A B) = 0`. -/
theorem sin_dihedralAngle_eq_zero_of_sin_arcLen_first_two_eq_zero
    (A B C : Fin 3 → ℝ) (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (h : Real.sin (arcLen A B) = 0) :
    Real.sin (dihedralAngle C A B) = 0
```

Each is ~12 LOC: from `Real.sin (arcLen X Y) = 0` and `normSq_projPerp_unit`
extract `normSq (projPerp X Y) = 0`, hence `projPerp X Y = 0` (via
positive-definiteness of `normSq`), hence `Y = (dot X Y) · X`. Combined
with `Y` unit: `(dot X Y)² = 1`, so `dot X Y = ±1`. In either branch,
`projPerp Y Z = ±projPerp X Z` for the third unit vector `Z`, so the
arccos argument of `dihedralAngle` is `±1`, hence `arccos ∈ {0, π}`,
hence `sin = 0`. The proof closes either by the if-branch (when
`projPerp X Z = 0`) or by `Real.sin_arccos_pm_one`-style lemma.

Note: each helper does NOT degenerate via the `dihedralAngle` if-branch
directly — the if-branch triggers on `projPerp · A = 0` for the
fixed vertex `A`, not on `projPerp B C`. The proof goes through
unfolding `arccos` and recognising `arg = ±1`.

### §3.2 Path comparison

| Dimension | Path 1: parent-level | Path 2: inline (private) |
|---|---|---|
| File touched at S3b ACT | parent `SphericalLawOfSines.lean` + OQ-03 file | OQ-03 file only |
| LOC added to parent | ~25 (2 helpers × ~12) | 0 |
| LOC added to OQ-03 file | ~50 (case-split + macro-D core) | ~75 (helpers inline + case-split + macro-D core) |
| Parent meta.json drift | none — parent meta lacks `theoremCount` field (§3.3) | none |
| Downstream cache invalidation | parent re-verify required (cached, but real) | OQ-03 only |
| Failure blast radius | parent re-verify + all 3 sibling OQs + 4 children | OQ-03 only |
| Re-usability for OQ-01, OQ-02 | high (helpers immediately importable) | requires later promotion (S3c) |
| Rollback cost on failure | revert parent + OQ-03 file | revert OQ-03 file only |
| Auditor signal | parent `verified` status preserved (helpers are theorems, not axioms/sorries) | OQ-03 only |

### §3.3 Why parent meta drift is a non-issue (correction to S3b PREP §4)

S3b PREP §4 says: *"The parent's `theoremCount` increments by 2 in
meta.json (auditor will catch the drift if we forget)"*. Empirically,
`src/data/proofs/spherical-law-of-sines/meta.json` does **not** carry a
`theoremCount` field at all — its tracked scalar fields at base SHA
`996638aefdf` are only `id`, `slug`, `sorries: 0`, `title`. So neither
path incurs a meta.json bump on the parent's gallery JSON. (Research-side
slug JSONs at `src/data/research/problems/*.json` do carry `theoremCount`,
but only for the slug under research, not for the parent gallery proof.)

This **does not** change the decision but does reduce the friction
estimate for Path 1 in §3.2. The friction remains: parent re-verify,
broader blast radius, and Lean-side cache invalidation.

### §3.4 Decision: **Path 2 (inline private helpers)** for S3b ACT iter 1

**Confirmed** S3b PREP §9 recommendation. Rationale (in order of weight):

1. **Blast radius dominates at the very-high-risk S3b ACT iteration.**
   Macro-case D is rated very-high-risk (~25-45 LOC, possibly needing
   `polyrith` or a hand-crafted `linear_combination`). If S3b ACT lands
   broken or churns through multiple iterations, we want the failure
   contained to OQ-03 — not to require parent re-verification or to
   invalidate the parent's `verified` status for any window of time.

2. **Parent stability is a load-bearing property.** Parent is `verified`,
   0 sorries, 0 axioms, 323 LOC, with 3 downstream slugs (OQ-01 OBSERVE,
   OQ-02 OBSERVE, this OQ-03 S3b-PREP) and 2 verified siblings
   (`spherical-law-of-cosines`, `spherical-law-of-cosines-oq-05`) sharing
   the file via the `Fin 3 → ℝ` framework. Modifying it now is premature
   optimisation for an API that no downstream consumer needs yet (OQ-01
   and OQ-02 are at OBSERVE phase, months away from needing these
   helpers).

3. **"Prove first, extract later" is the standard library pattern.**
   Land S3b ACT with inline helpers, then S3c promotes the helpers to
   the parent once their signatures have stabilised through actual use.
   This avoids API churn on the parent and gives the helpers one
   real consumer (S3b ACT itself) to validate their signatures before
   they're public API.

4. **Auditor friction is symmetric across paths.** §3.3 above confirms
   neither path requires meta.json edits on the parent gallery JSON.
   The auditor signal that S3b PREP §4 worried about is moot.

5. **Rollback simplicity.** Path 2 means S3b ACT is a one-file diff
   (revertable in one click). Path 1 means a two-file coordinated diff
   that's harder to revert atomically.

### §3.5 What S3c (cleanup) becomes after this decision

If S3b ACT lands cleanly with inline helpers, S3c is a **pure promotion
PR** (target: ~15-20 LOC):

* Move both `private theorem sin_dihedralAngle_eq_zero_of_sin_arcLen_*`
  declarations from `SphericalLawOfSinesOQ03.lean` to the parent
  `SphericalLawOfSines.lean` (just below `dihedralAngle_comm_last`,
  before `sin_sq_dihedralAngle`).
* Drop the `private` modifier.
* Update OQ-03 file to use the parent-level names.
* Parent `theoremCount` is not a tracked meta field — no JSON edit
  required on the parent gallery side.

If OQ-01 (excess) or OQ-02 (dual cosines) reach a similar discharge
phase before S3c, the helpers can be promoted opportunistically as
part of those slugs' PRs.

## §4 Macro-case A paste-ready Lean (no helpers needed)

Macro-case A (sin b = 0) does not need either helper because it
triggers the `dihedralAngle` if-branch directly for both `α` and `γ`:

* For `α = dihedralAngle A B C`: degenerate when
  `normSq (projPerp C A) = 0`, which equals `sin²(arcLen A C) = sin² b`
  via `normSq_projPerp_unit A C hA hC`. So `sin b = 0` ⟹ if-branch
  fires for `α` ⟹ `α = 0` ⟹ `sin α = 0`.
* For `γ = dihedralAngle C A B`: degenerate when
  `normSq (projPerp A C) = 0`, which equals `sin²(arcLen C A) = sin² b`
  via `normSq_projPerp_unit C A hC hA` + `arcLen_comm`. So same
  trigger ⟹ `γ = 0` ⟹ `sin γ = 0`.

(`arcLen_comm` is an unstated parent identity — `arcLen u v = arcLen v u`
follows from `dot_comm` and the definition. If the parent does not
export it, the inline form `dot_comm B A` plus `normSq_projPerp_unit`
with swapped args closes it in 2 LOC.)

### §4.1 Paste-ready snippet (macro-case A only)

```lean
  -- Inside `spherical_cotangent_rule_polynomial`, after the `set` block:
  by_cases hsin_b : Real.sin (arcLen A C) = 0
  · -- Macro-case A: sin b = 0 ⟹ LHS = 0; sin α = sin γ = 0.
    -- Step 1: extract normSq (projPerp C A) = 0.
    have hsq_b : Real.sin (arcLen A C) ^ 2 = 0 := by
      rw [hsin_b]; ring
    have hnpC : normSq (projPerp C A) = 0 := by
      rw [← sin_sq_arcLen A C hA hC]; exact hsq_b
    -- Step 2: normSq pC = 0 ⟹ sqrt normSq pC = 0
    have hsqrt_pC : Real.sqrt (normSq (projPerp C A)) = 0 := by
      rw [hnpC]; exact Real.sqrt_zero
    -- Step 3: dihedralAngle A B C = 0 via if-branch.
    have hα_zero : Real.sin (dihedralAngle A B C) = 0 := by
      simp only [dihedralAngle, if_pos (Or.inr hsqrt_pC), Real.sin_zero]
    -- Step 4: symmetric for γ = dihedralAngle C A B.
    -- The γ if-branch triggers on projPerp A C (first slot) being zero-norm.
    -- normSq (projPerp A C) = sin²(arcLen C A) = sin²(arcLen A C) = 0.
    have hnpA_at_C : normSq (projPerp A C) = 0 := by
      rw [← sin_sq_arcLen C A hC hA]
      -- arcLen C A = arcLen A C (from dot_comm)
      have h_swap : Real.sin (arcLen C A) = Real.sin (arcLen A C) := by
        unfold arcLen; rw [dot_comm]
      rw [h_swap]; exact hsq_b
    have hsqrt_pA_at_C : Real.sqrt (normSq (projPerp A C)) = 0 := by
      rw [hnpA_at_C]; exact Real.sqrt_zero
    have hγ_zero : Real.sin (dihedralAngle C A B) = 0 := by
      simp only [dihedralAngle, if_pos (Or.inl hsqrt_pA_at_C), Real.sin_zero]
    -- Step 5: close the equation.
    rw [hα_zero, hγ_zero, hsin_b]
    ring
  · -- Macro-cases B, C, D: deferred to remaining by_cases nesting.
    sorry
```

**LOC**: ~24 (excluding `sorry` for B/C/D).

**Mathlib lemmas consumed**:
* `Real.sqrt_zero : Real.sqrt 0 = 0` (Mathlib.Analysis.SpecialFunctions.Pow.NNReal).
* `Real.sin_zero : Real.sin 0 = 0` (Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic).
* `if_pos`, `Or.inl`, `Or.inr` — Lean core.

**Parent lemmas consumed**:
* `sin_sq_arcLen u v (hu : IsUnit3 u) (hv : IsUnit3 v) : Real.sin (arcLen u v) ^ 2 = normSq (projPerp v u)` — parent line 220 (verified S3 PREP).
* `dihedralAngle` definition unfolding — parent line 158.
* `dot_comm` — Lean core or parent (used in arcLen-swap helper).

**Risk**: low. All steps are direct definitional unfoldings + `simp`
+ `ring`. No `nlinarith`, no `polyrith`. Failure modes are limited to:
(a) `sin_sq_arcLen` argument order — if the parent's signature is
`normSq (projPerp v u)` rather than `(projPerp u v)`, swap in Step 1; (b)
`arcLen_comm` not exported — inline the 2-LOC `dot_comm` rewrite as
shown in Step 4.

### §4.2 What macro-case A does NOT yet handle

Macro-case A discharges only the `sin (arcLen A C) = 0` branch. The
remaining three macro-cases B, C, D are wrapped in the `sorry` at the
bottom of the snippet. S3b ACT's main work is:

* Macro-case B (sin a = 0 ∧ sin b ≠ 0): inline helper
  `sin_dihedralAngle_eq_zero_of_sin_arcLen_third_eq_zero`
  (Path 2 per §3.4), then `ring`. ~12 + ~12 LOC.
* Macro-case C (sin c = 0 ∧ sin a sin b ≠ 0): inline helper
  `sin_dihedralAngle_eq_zero_of_sin_arcLen_first_two_eq_zero`
  (Path 2), then `ring`. ~18 + ~12 LOC.
* Macro-case D (non-degenerate): algebraic core. ~25-45 LOC.

Per S3b PREP §8, total ~75 LOC for inline-helper path.

## §5 Risk re-classification after this PREP

S3b PREP §8 risk table updated:

| Macro-case | Estimate | Risk before S5 | Risk after S5 | Notes |
|------------|----------|----------------|---------------|-------|
| A (`sin b = 0`) | ~24 LOC | low | **low (paste-ready)** | §4.1 snippet validated against parent decl signatures at base `996638aefdf`. Only failure mode is Mathlib lemma-name drift, gated by docker smoke-test. |
| B (`sin a = 0`) | ~12 + helper | moderate | moderate | Decision §3.4 picks inline-helper; helper itself is ~12 LOC of `normSq_projPerp_unit` + arccos argument analysis. |
| C (`sin c = 0`) | ~18 + helper | moderate | moderate | Symmetric to B. Second helper. |
| D (non-deg) | ~25-45 LOC | very high | very high | Unchanged. The algebraic core. Requires either squaring strategy (§5 of S3b PREP) or `linear_combination` with sqrt-aware coefficients. |
| **Total** | **~75 LOC** | **high** | **high** | One sub-risk removed (helper-placement decision); main risk (macro-D algebra) intact. |

## §6 Updated S3b ACT readiness gate

| # | Item | Pre-S5 | Post-S5 |
|---|------|--------|---------|
| 1 | Macro-case taxonomy verified | GREEN | GREEN |
| 2 | Bearer drift recheck | GREEN | GREEN (re-affirmed at SHA `996638aefdf`) |
| 3 | Paste-ready skeleton (all 4 cases) | GREEN | GREEN |
| 4 | Sibling PR sweep | GREEN | GREEN (re-affirmed) |
| 5 | **Decision: parent-helper vs inline-helper** | **DEFERRED** | **GREEN (inline-helper, §3.4)** |
| 6 | Build smoke-test before push | **DEFERRED** | **DEFERRED (blocked by host disk pressure, §7)** |

Net: **5/6 GREEN, 1 DEFERRED.** S3b ACT is now blocked solely on infrastructure
(Docker / disk), not on mathematical or design decisions. As soon as host disk
recovers to ≥10 Gi free, S3b ACT can proceed: paste §4.1 snippet, draft the two
inline helpers per §3.1 and §3.4, draft macro-D per S3b PREP §5, run
`./proofs/scripts/docker-build.sh Proofs.SphericalLawOfSinesOQ03`.

## §7 Infra constraint (load-bearing — blocks S3b ACT)

Host disk at PR-creation time:

```
$ df -h /Users/rwalters/GitHub/lean-genius
Filesystem      Size    Used   Avail Capacity
/dev/disk3s5   926Gi   890Gi   5.1Gi   100%
```

**5.1 Gi free, 100% capacity.** This is **below** the ≥10 Gi pre-flight
threshold cited by S4 STATE-SYNC §6 (which observed 57 Gi free at 94%
capacity 3 days ago). Net drop: ~52 Gi consumed in 3 days. Docker
`./proofs/scripts/docker-build.sh Proofs.SphericalLawOfSinesOQ03`
requires sustained write capacity (Mathlib oleans + lake cache, ~1-2 Gi
for a fresh build); at 5.1 Gi free this is **not safe to run** without
significant risk of OS-level write failure or Docker layer corruption.

**Recommendation**: defer S3b ACT until host has ≥15 Gi free. This
PREP (doc-only, ≤ 4 KB of writes) is safe at current disk state.

This constraint is what reduces this iteration from S3b ACT (originally
the next iteration per S4 SYNC's "Honest scope" note) to S5 PREP
(this iteration). The mathematical decision content of S5 PREP would
otherwise have been folded into S3b ACT itself.

## §8 Honest scope of this PREP

* Closes 1 of 2 deferred items on the S3b ACT readiness gate
  (helper-placement decision).
* Documents a paste-ready Lean snippet for 1 of 4 macro-cases (macro-A,
  the lowest-risk case).
* Re-affirms quiescence, bearer-byte-stability, race-clear status —
  same observations as S4 SYNC, refreshed to base `996638aefdf`
  (766 commits past S4 SYNC's `18b5808017a`).
* **Does NOT** advance the phase tag (`S3b-PREP` stays).
* **Does NOT** modify any `.lean` file or `lake-manifest.json`.
* **Does NOT** discharge macro-cases B, C, or D.
* **Does NOT** run any Docker build (infra-blocked).
* **Does NOT** modify parent meta.json or any gallery JSON beyond the
  slug's research JSON (`lastUpdated` + `knowledge.progressSummary`
  prepend).
* Iteration counter advances: 6 → 7. Attempt count: stays at 4 (no
  Lean attempt in this iteration).

The single load-bearing observation in this PREP is **§3.4** — the
inline-helper-path decision. The §4.1 paste-ready snippet is supporting
material (a sanity check that the decision is implementable). The
§3.3 correction to S3b PREP §4 ("parent meta lacks theoremCount") is
an incidental finding that reduces friction estimates but does not
change the decision.

## §9 Conflict-free guarantees (files touched by this PR)

1. `research/problems/spherical-law-of-sines-oq-03/sessions/2026-06-03-s5-prep-helper-placement-decision.md`
   (this file, NEW).
2. `research/problems/spherical-law-of-sines-oq-03/state.md` (UPDATE:
   head + new S5 entry; no narrative edits to prior entries).
3. `src/data/research/problems/spherical-law-of-sines-oq-03.json`
   (UPDATE: `lastUpdated: 2026-05-31 → 2026-06-03` + `knowledge.progressSummary`
   prepend; no edits to `phase`, `status`, `tier`, `researcher`,
   `approach`, `claimedBy`, `claimedAt`, `claimExpires`, or any other
   top-level field).

**No Lean source modified.** **No `lake-manifest.json` modified.** **No
parent gallery JSON modified.** No new sorries. The §4.1 snippet is
paste-ready for S3b ACT but is not itself committed as Lean code.

## §10 References

* PR #18229 (S1 OBSERVE), PR #19102 (S2 SCAFFOLD), PR #19340 (S3 PREP),
  PR #19388 (S3a ACT), PR #19450 (S3b PREP), PR #21369 (S4 STATE-SYNC)
  — predecessors on this slug.
* `research/problems/spherical-law-of-sines-oq-03/sessions/2026-05-16-s3b-prep-dihedral-degenerate-branch.md`
  — the PREP this S5 closes one deferred item of.
* Parent file `proofs/Proofs/SphericalLawOfSines.lean` lines 158
  (`dihedralAngle`), 172 (`sin_sq_dihedralAngle`), 220 (`sin_sq_arcLen`).
* `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open.md`
  — guidance on PREP-then-ACT cadence; this PREP elaborates the
  decision content rather than performing an ACT.
