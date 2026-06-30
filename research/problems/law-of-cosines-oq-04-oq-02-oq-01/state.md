# State: `law-of-cosines-oq-04-oq-02-oq-01`

**Tier**: B (Significance 6 / Tractability 5)
**Phase**: BLOCKED (S7) — near-done but Docker-gated. One real sorry remains (`angle_bisector_ratio_from_geometry`, line 165); discharging it is a multi-step inner-product/Cauchy-Schwarz ACT (skeleton Steps 1-6) requiring a Docker build to verify, and build infra is down (blackout 2026-06-13).
**Last update**: 2026-06-13 (researcher-1) — S7 BLOCKED flag. origin/main `LawOfCosinesOQ04OQ02OQ01.lean` = 194 LOC, 6 lemmas/theorems, exactly 1 real proof sorry at line 165 (the line-50 `sorry` is docstring prose). All four helper lemmas (`bisector_param_exists`, `bisector_dist_BD/DC`, `cos_BAD_eq_cos_DAC_inner_form`) are in place; remaining work is the algebraic factorization + strict-CS exclusion in the main theorem. After 7 sessions (3 ACT / 2 PREP / 1 STATE-SYNC) the only path forward is build-gated ACT — flag blocked rather than churn more PREP.
**Prior phase chain**: OBSERVE (S1) → PREP (S2-prep) → ACT (S2-skeleton) → ACT (S3 partial, build verified) → PREP (S4-prep, S5-statesync+audit-ext) → ACT (S6a Step-b helper) → BLOCKED (S7)

## Iteration History

| Iter | Session | Mode | Date | PR | Author | Net |
|---|---|---|---|---|---|---|
| 1 | S1 | OBSERVE | 2026-05-11 | #17833 | researcher-8 | +3 docs (problem.md, knowledge.md, JSON) |
| 2 | S2 PREP | PREP | 2026-05-13 | #18908 | researcher-4 | +1 doc (s2-prep-bearer-audit.md) |
| 3 | S2 ACT skeleton | ACT (build pending) | 2026-05-13 | #18924 | researcher-10 | +1 Lean (145 LOC, 4 sorries) |
| 4 | S3 ACT | ACT (build verified, 7745 jobs) | 2026-05-14 | #18963 | researcher-9 | +30 LOC Lean (4→1 sorries) + parent stewarts_theorem fix |
| 5 | S4 PREP | PREP | 2026-05-15 | #19032 | researcher-12 | +1 doc (s4-prep-step-b-and-e-bearer-audit.md) |
| 6 | S5 STATE-SYNC + audit-ext | STATE-SYNC + PREP-2 | 2026-05-16 | (merged) | researcher-9 | +1 doc (s5-statesync-audit-extension.md), state.md catchup, JSON catchup |
| 7 | S6a ACT Step-b helper | ACT (Step b discharged) | 2026-06-09 | #19462-era | researcher-7 | +25 LOC Lean (1→1 sorries; new helper lemma; main theorem skeleton updated) |
| 8 | S7 BLOCKED flag | STATE-SYNC (doc-only) | 2026-06-13 | this PR | researcher-1 | flagged blocked: 1 real sorry (line 165) needs build-gated multi-step ACT, Docker down; verified origin/main inventory (194 LOC, 1 real sorry, line-50 sorry is prose) |

## Session N=6 — S6a ACT Step (b) helper (2026-06-09, researcher-7)

**Mode**: ACT (scoped — discharge Step (b) only as a helper lemma; main theorem still has 1 sorry).

**Outcome**: added `cos_BAD_eq_cos_DAC_inner_form` (~8 LOC body) implementing
Step (b) of the Path-A strategy. The lemma takes the angle equality
`hbis : ∠ B A D = ∠ D A C` and produces the inner-product cosine equation
`⟪B-ᵥA, D-ᵥA⟫ / (‖B-ᵥA‖·‖D-ᵥA‖) = ⟪D-ᵥA, C-ᵥA⟫ / (‖D-ᵥA‖·‖C-ᵥA‖)`.

Proof body (3 tactic lines):
* `congrArg Real.cos hbis` — apply cosine to both sides of the angle equality.
* `unfold EuclideanGeometry.angle at hcos` — exposes
  `InnerProductGeometry.angle` on `vsub`-vectors (per the def at `Affine.lean:42`).
* `rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle]` — rewrites
  both sides to the inner-product / norm ratio form.
* `exact hcos` — close the goal (after the rewrites the LHS/RHS match the
  lemma statement exactly).

This is the **`congrArg Real.cos` route** preferred by `s4-prep-step-b-and-e-bearer-audit.md` § 2.3
over the `Real.arccos_inj` alternative, which would require explicit
`[-1, 1]` bounds.

**Net diff this session**:
* `LawOfCosinesOQ04OQ02OQ01.lean`: +25 LOC (164 → 193, 4 → 5 declarations,
  1 → 1 sorries, 0 → 0 axioms). New helper `cos_BAD_eq_cos_DAC_inner_form`
  before the main theorem; main theorem proof-skeleton docstring updated
  to point at S5 §§ 4-7 + identify Step (b) as discharged.
* `state.md`: Iteration History row 7 + this Session N=6 entry + header
  refresh.
* JSON `currentState.{since,iteration,focus,nextAction}` refreshed;
  `knowledge.progressSummary` prepended.

**Sorry / axiom delta**:
* `LawOfCosinesOQ04OQ02OQ01.lean`: **1 → 1 sorries** (helper has no sorry;
  main theorem still does), **0 → 0 axioms**, **4 → 5 declarations**.
* Parent `LawOfCosinesOQ04OQ02.lean`: **0 → 0 sorries, 0 → 0 axioms**.

**Build verification**: `./proofs/scripts/docker-build.sh Proofs.LawOfCosinesOQ04OQ02OQ01`
launched at session start; result attached in PR description. The helper
proof body is short and uses bearers re-verified by S5 audit-extension
(`Affine.lean:42` for the `EuclideanGeometry.angle` definition,
`Basic.lean:65` for `InnerProductGeometry.cos_angle`).

**Why scoped S6a vs full S6 ACT**: full S6 ACT discharges ~80-120 LOC across
Steps (b)–(f). The recipe is paste-ready per S5 § 8.1's 9/9 GREEN gate,
but each sub-step has its own subtleties (Step c's `inner_smul_left`
star-conjugate handling; Step d's `linear_combination` sign; Step e's
disjunct-selection error in the corrected version; Step f's `field_simp`
extraction of `s = c/(b+c)`). Shipping Step (b) first (a) creates a
build-verified landmark for sibling tactic-pattern callers, (b) makes
the next session's ACT scope smaller (~70-100 LOC instead of 80-120),
(c) reduces compound bearer-drift risk: any drift in Step (b)'s `cos_angle`
chain would also affect Steps (c)-(e) since they all live in the same
file, so verifying Step (b) builds is a sentinel for the broader recipe.

**Worktree-path-trap incident** (informational): initial Edit/Read calls
were accidentally routed to the main repo path
`/Users/rwalters/GitHub/lean-genius/proofs/...` rather than the worktree
path `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-7/proofs/...`.
Caught during git status (working tree clean). Main repo file reverted
via Edit-undo (no `git` operations needed since the main repo had an
`index.lock` from a concurrent process). Worktree edits then applied
to the correct path. No data loss; memory `feedback_worktree_path_trap.md`
applied.

**Next-action**: S6b — discharge Steps (c)/(d) (inner-product expansion +
factorization, ~40-55 LOC combined). Can use `cos_BAD_eq_cos_DAC_inner_form`
output as the starting point. Optionally S6b+c+d+e+f combined in one
PR if the next researcher is willing to take on ~70-100 LOC under
build-verify; OR three separate scoped PRs (S6b Step c-d, S6c Step e, S6d
Step f) for sentinel-style staging.

---

## Session N=5 — S5 STATE-SYNC + audit-extension (2026-05-16, researcher-9)

**Mode**: STATE-SYNC + PREP-extension (doc-only; absorbs S4 PREP into state.md/JSON, plus completes the Step (c)/(d)/(e)/(f) bearer audit).

**Outcome**: 3 files, all doc-only.

(a) **STATE-SYNC** (state.md + JSON):
* state.md head updated; Iteration History table prepended; Session N=5
  entry (this one); Next-action rewritten to point at the S6 ACT main
  theorem discharge.
* JSON `currentState.{since,iteration,focus,nextAction,attemptCounts.
  total}` refreshed; `knowledge.{progressSummary,nextSteps}` cleaned
  (drop S1-era "S2: Implement Path A" residue); `knowledge.mathlibGaps[2]`
  refined now that the strict-Cauchy-Schwarz bearer chain is identified
  locally; `lastUpdate` bumped. **`leanFiles[]` NOT self-edited** —
  mechanic territory; ready-to-paste snippet provided in memo § 8.2.

(b) **Audit-extension** (new memo `s5-statesync-audit-extension.md`,
    ~320 LOC, 10 sections):
* § 3 — three deferred bearers from S4 PREP § 3.2 spot-checked at SHA
  `2df2f01`; one returns a **materially corrected statement**
  (`inner_eq_norm_mul_iff_real` is `↔ ‖y‖•x = ‖x‖•y`, **not**
  `↔ ∃ r ≥ 0, y = r•x`; the explicit-scalar form is the separate
  `real_inner_div_norm_mul_norm_eq_one_iff` at Basic.lean:771).
* § 4 — refined Step (e) proof-fragment that resolves S4 PREP § 3.3's
  `...` placeholders **and** fixes a latent **disjunct-selection error**:
  S4 PREP wrote `right; right; right` (selecting `∠ = π`, cos = -1)
  but the narrative argued angle = 0, cos = 1 — should have been
  `right; right; left`. Plus the set literal would have needed
  `Set.insert_comm` permutation. Refined route via
  `cos_eq_one_iff_angle_eq_zero` (Basic.lean:310) + `angle_eq_zero_iff_
  ne_and_wbtw` (Affine.lean:349) + `Wbtw.collinear` (Between.lean:1020)
  sidesteps the entire disjunct dance.
* § 5 — Step (c) inner-product expansion bearer chain (`inner_add_left/
  right`, `inner_sub_left/right`, `inner_smul_left/right`,
  `real_inner_self_eq_norm_mul_norm`).
* § 6 — Step (d) algebraic factorization via `linear_combination` with
  hand-witness sign tracking.
* § 7 — Step (f) final conclusion chain extracting `s = c/(b+c)` and
  substituting into `bisector_dist_BD/DC` outputs.
* § 8 — S6 ACT readiness gate (9/9 substantive GREEN).

**Net diff this session**:
* `state.md`: this Session N=5 entry + Iteration History table + header
  refresh.
* `s5-statesync-audit-extension.md`: NEW (~320 LOC).
* `src/data/research/problems/law-of-cosines-oq-04-oq-02-oq-01.json`:
  field refresh (no leanFiles touch).

**Sorry / axiom delta**: Lean files unchanged.
`LawOfCosinesOQ04OQ02OQ01.lean`: **1 → 1 sorries, 0 → 0 axioms**.
Parent `LawOfCosinesOQ04OQ02.lean`: **0 → 0 sorries, 0 → 0 axioms**.

**Why not S5 ACT directly**: Docker daemon hung this session
(`docker info` returns empty `Server:`), so no `docker-build`
verification possible. Memory same-wave precedent allows build-pending
ACT under qualifier when (a) leaf-only adds, (b) recent BUILD-VERIFY,
(c) bearer 0-drift — all three met. **However**, the S4 PREP § 3.3
sketch had a disjunct-selection error and `...` placeholders, plus
three deferred-bearer line numbers were unverified — a build-pending
S5 ACT pasted from S4 PREP § 3.3 as-is would have failed to compile.
The audit-extension makes S6 ACT genuinely paste-ready.

**Consecutive doc-only count**: 2 (S4 PREP #19032 + this S5). Within
4+ threshold. S6 ACT is the next-action.

---

## Session N=4 — S3 partial ACT (2026-05-14, researcher-9)

**Mode**: ACT (lemma discharges; `docker-build` verified, 7745/7745 jobs).

**Outcome**: discharged Steps 1–2 of the Path-A plan inside
`proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean`. Net sorry count `4 → 1`.

* `bisector_param_exists` (Step 1, ~10 LOC body): proved via
  `Sbtw.mem_image_Ioo` → `lineMap`-unpack → `vadd_vsub_assoc` →
  `vsub_sub_vsub_cancel_right` → `smul_sub` + `sub_smul` + `abel`.
* `bisector_dist_BD` (Step 2a, ~9 LOC body, calc-block): standard
  `dist_comm` → `dist_eq_norm_vsub` → `norm_smul` →
  `Real.norm_of_nonneg` (using `0 < s` from `hs.1`).
* `bisector_dist_DC` (Step 2b, ~9 LOC body, calc-block): symmetric form
  with `0 ≤ 1 - s` derived from `hs.2 : s < 1` via `linarith`.

**Pre-existing parent build failure fixed (build unblocker)**.

`proofs/Proofs/LawOfCosinesOQ04.lean:97` (`stewarts_theorem`) failed to build
at the lake-pinned Mathlib SHA — `linarith` could not bridge a nonlinear
substitution. The hypothesis chain was

* `this : b^2 * m + c^2 * n = (m + n) * (d^2 + m*n)` (from `stewarts_from_cosines`),
* `ha : m + n = a`,
* goal: `b^2 * m + c^2 * n = a * (d^2 + m*n)`.

`linarith` would have to "multiply" `ha` through the nonlinear factor — not
its job. The fix is a one-line `rw [ha] at h; exact h` direct substitution.
This file was on origin/main with the broken proof; my dep chain failed at
job 7743/7745 until I patched it. Fix isolated to one theorem; rest of file
unchanged. 1 unused-variable warning at `median_length_formula:110:45 (ha)`
remains (was already present, untouched by this PR).

**Net diff this session**:
* `LawOfCosinesOQ04OQ02OQ01.lean`: +30 LOC (4 sorries → 1).
* `LawOfCosinesOQ04.lean`: +2/-1 LOC (parent build unblocker).
* state.md (this session entry).
* JSON cursor update.

**Build status**: ✅ `Build completed successfully (7745 jobs)` via
`./proofs/scripts/docker-build.sh Proofs.LawOfCosinesOQ04OQ02OQ01`. Only the
target sorry warning remains: the main theorem at
`LawOfCosinesOQ04OQ02OQ01.lean:132 (angle_bisector_ratio_from_geometry)`.

**Risks resolved this session**:

* `Sbtw.mem_image_Ioo` unpacking — `obtain ⟨s, hs, hlm⟩ := hD.mem_image_Ioo`
  yielded exactly the `Set.image` destructuring expected; `hlm : lineMap B C s = D`.
* `AffineMap.lineMap_apply` form — confirmed `lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀`
  at the pinned SHA; the `vadd_vsub_assoc` rewrite cleanly produces
  `s • (C -ᵥ B) + (B -ᵥ A)` for the subsequent algebra.
* `Real.norm_of_nonneg` was the correct bearer for `‖s‖ = s` when `0 ≤ s`
  (the `abs_of_nonneg` family doesn't unify with `‖·‖` on `ℝ` without an
  intermediate `Real.norm_eq_abs`).

**Risks remaining (for `angle_bisector_ratio_from_geometry`)**:

* `Real.arccos_inj` requires explicit `[-1, 1]` bounds on both cosines (derivable
  from `abs_real_inner_le_norm` + non-zero norms).
* Inner-product expansion may blow up `ring`; fallback to `linear_combination` or
  hand-factored `nlinarith` per the original risk register row.
* Non-collinearity-to-strict-Cauchy-Schwarz: `abs_real_inner_le_norm` plus the
  `Or.elim` over `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`.

---

## Session N=3 — S2 ACT skeleton (2026-05-13, researcher-10)

**Mode**: ACT (skeleton/scaffold; build pending — no `docker-build` this session).

**Outcome**: created `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean` (145 LOC), establishing
the Path A scaffold per `knowledge.md §8`'s seven-lemma plan:

* Module header with strategy summary, bearer references (using S2-PREP audit's
  re-grounded paths/line numbers at SHA `2df2f01`), and explicit "Build: pending" note.
* Namespace `LawOfCosinesOQ04OQ02OQ01` with standard
  `InnerProductSpace ℝ V` + `NormedAddTorsor V P` variable block.
* `bisector_param_exists`: stated — Sbtw → `s ∈ Ioo 0 1` with affine combination.
  Proof: `sorry` (S3 will discharge via `Sbtw.mem_image_Ioo` + `AffineMap.lineMap_apply`
  + vsub rewriting, ~20-30 LOC per audit doc §4).
* `bisector_dist_BD` and `bisector_dist_DC`: stated — segment-length lemmas
  parametric in `s`. Proofs: `sorry` (S3, ~10-15 LOC each via `dist_eq_norm_vsub`
  + `norm_smul` + `abs_of_pos`).
* `angle_bisector_ratio_from_geometry`: stated — the OQ's main theorem, with full
  geometric hypotheses (`Sbtw ℝ B D C`, `∠ B A D = ∠ D A C`,
  `¬ Collinear ℝ ({A,B,C} : Set P)`). Proof: `sorry` with explicit 6-step skeleton
  in docstring (S3 will discharge via Path A steps 2-5, ~150-200 LOC).
* Tail comment block sketches the S4 chained statement `angle_bisector_length_geometric`
  (target: re-state parent's `angle_bisector_length` purely in geometric terms,
  closing the OQ).

**Net diff this session**:
* +1 Lean file (`LawOfCosinesOQ04OQ02OQ01.lean`, 145 LOC, **4 sorries**, 0 axioms).
* state.md update (this session entry + Next-action update).
* JSON cursor update (`currentState.phase` → ACT, `progressSummary` append, `lastUpdate`).

**Build status**: pending. Per CLAUDE.md never-run-`lake build`-directly rule, this is a
"build pending" PR; downstream verification (S3 first lemma discharge OR docker-build run)
will confirm Mathlib bearers resolve and namespace/imports are clean. The file is small
(145 LOC, mostly comments + signatures) and all bearers are re-grounded to the pinned
SHA `2df2f01` via the S2-PREP audit, so build risk is concentrated at the imports
line and namespace opens — not at the proof body.

**Why ACT-skeleton vs full ACT**: per `knowledge.md §8`, full Path A is ~250-350 LOC
across 7 lemmas. Discharging all 7 in one session without local `docker-build` verification
would compound bearer/syntax risk. Shipping the scaffold first (a) creates a stable
file landmark in `proofs/Proofs/` so S3 can iterate per-lemma against actual `lake build`
output, (b) locks in the namespace/imports/variable block (the lowest-confidence parts
for a researcher-only-iteration session), (c) makes the theorem statements citable from
sibling work (e.g. `CevasTheoremOQ02OQ01OQ03.lean` for the parallel geometric Ceva OQ).

**Risks deferred to S3**:
* `Sbtw.mem_image_Ioo` unpacking gives `D = lineMap B C s` not `D -ᵥ A = (1-s)•u + s•v`
  directly; rewriting via `AffineMap.lineMap_apply` (`lineMap a b t = a + t • (b -ᵥ a)`)
  + `vsub_sub_vsub_cancel_right` is the path. ~10 LOC.
* `Real.arccos_inj` requires explicit `[-1, 1]` bounds on both cosines; derivable from
  `abs_real_inner_le_norm` + non-zero `‖u‖`, `‖v‖`, `‖D -ᵥ A‖`.
* `inner_smul_left` returns `r† * ⟪x, y⟫` (general 𝕜); for ℝ the conjugate is identity,
  but `simp` may need `RCLike.star_def` / `Complex.conj_ofReal` hints. Confirmed by audit.

---

## Session N=2 — S2-PREP (2026-05-13, researcher-4)

**Mode**: PREP (doc-only; companion to S1 OBSERVE's `knowledge.md`).

**Outcome**: produced `s2-prep-bearer-audit.md` — re-grounds the S1 OBSERVE
`knowledge.md §4` Mathlib API survey against the lake-pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`). Findings:

(a) **Wrong file path detected.** `InnerProductGeometry.angle` (def) and
    `InnerProductGeometry.cos_angle` cited in `knowledge.md §4.2` as living in
    `Mathlib/Analysis/InnerProductSpace/Basic.lean` actually live in
    **`Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean`** (at L40 and L65).
    A naive `gh api .../contents/<wrong-path>` lookup would have failed silently.

(b) **Substantial line drift** in `Convex/Between.lean`. The cluster
    `Sbtw.mem_image_Ioo`, `Sbtw.ne_left/left_ne/ne_right/right_ne` cited at L203-215
    actually sits at L341-353 (+138-line drift). Names + signatures stable; only
    line numbers moved. The S2 implementer would have been mis-guided by
    `knowledge.md`'s line citations alone.

(c) **Smaller drift** in `Geometry/Euclidean/Angle/Unoriented/Affine.lean`:
    `angle_eq_pi_iff_sbtw` L278→L281, `angle_add_angle_eq_pi_of_angle_eq_pi` L172→L175,
    `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` L376→L378. Names/sigs
    stable.

(d) **Path A Step 1 sketch added** (§4 of new doc): 15-25 LOC of cosine-equality
    conversion using `unfold EuclideanGeometry.angle` → `rw [InnerProductGeometry.cos_angle]`
    → `Real.arccos_inj` (Inverse.lean L336, preferred over `arccos_injOn` at L333 since
    the two-sided iff form is cleaner given explicit `[-1, 1]` bounds).

(e) **Refined risk register** (§3 of new doc): six rows of `knowledge.md §5`
    re-graded against audit evidence. Of those, two are **confirmed** (the
    `Sbtw.mem_image_Ioo` signature surprise + the `arccos`-injectivity bound
    derivability), one is **promoted in priority** (the `inner_smul_left` returning
    `r† * ⟪x, y⟫` for general `𝕜` may surface `starRingEnd ℝ` artefacts; check during S2),
    and one is **mostly nullified** (Mathlib version drift — names stable, only line
    numbers move, audit fixes that).

**Why PREP-only this session**: S2-implement is ~250-350 LOC of new Lean (per
`knowledge.md §8`) in a file (`LawOfCosinesOQ04OQ02OQ01.lean`) that doesn't yet exist.
Per `CLAUDE.md`'s "never run `lake build` directly" policy, transcribing 250+ LOC
without local verification carries non-trivial build risk. Bearer audit + cosine-equality
sketch (15-25 LOC) de-risks the largest Mathlib-interface uncertainty BEFORE S2-implement
starts. The remaining inner-product factorization (Steps 2-4 of `knowledge.md §3.A`)
will benefit from the corrected file paths and line numbers.

**Net diff this session**: +1 markdown file (`s2-prep-bearer-audit.md`, ~210 lines),
state.md update, JSON cursor update. Zero Lean changes. Parent file
`LawOfCosinesOQ04OQ02.lean` unchanged (still 174 LOC, 9 theorems, 0 axioms, 0 sorries).

---

## Summary (S1 OBSERVE, 2026-05-11, researcher-8)

S1 OBSERVE for `law-of-cosines-oq-04-oq-02-oq-01` is complete. The OQ — deriving the
algebraic angle-bisector identity `m · b = n · c` from a geometric premise — has been
reformulated as a clean inner-product factorization in Mathlib's `EuclideanGeometry`
framework, no missing primitives identified, and the S2 implementation has been
scoped at ~250-350 lines.

Doc-only iteration. Three files created in this worktree:

* `research/problems/law-of-cosines-oq-04-oq-02-oq-01/problem.md` — formal statement,
  classification, approach menu, related-proofs table.
* `research/problems/law-of-cosines-oq-04-oq-02-oq-01/knowledge.md` — full survey:
  §1 target, §2 vector reformulation, §3 three approach paths with hand
  derivation for the recommended Path A, §4 Mathlib API survey (5 sub-sections),
  §5 risk register, §6 sibling-proof lessons, §7 S1 outcome, §8 next-action menu.
* `src/data/research/problems/law-of-cosines-oq-04-oq-02-oq-01.json` — phase
  updated from `NEW` to `OBSERVE`, problem-statement / knownResults / knowledge
  fields populated, next-action set to S2 Path A.

No Lean changes in S1. Parent file `LawOfCosinesOQ04OQ02.lean` build status
unchanged (0 axioms, 0 sorries, 7 theorems).

## Path Decision

**S2 will implement Path A** (inner-product factorization). See
`knowledge.md §3.A` for the hand derivation and `knowledge.md §8` for the
seven-lemma S2 outline.

The key insight is that `Sbtw ℝ B D C` extracts a barycentric parameter
`s ∈ Ioo 0 1` with `D -ᵥ A = (1 - s) • u + s • v` (where `u := B -ᵥ A`,
`v := C -ᵥ A`), and the bisector hypothesis `∠ B A D = ∠ D A C` collapses (after
arccos injectivity + cancellation of the common `1 / ‖D -ᵥ A‖`) to the
algebraic equation

```
((1 - s) · c - s · b) · (b · c - ⟪u, v⟫) = 0
```

The second factor is excluded by `¬ Collinear ℝ ({A, B, C} : Set P)` (strict
Cauchy-Schwarz), forcing `s = c / (b + c)`. From `m = s · a` and `n = (1 - s) · a`
the identity `m · b = n · c` follows immediately.

## Session N=1 — S1 (2026-05-11, researcher-8)

* **Goal**: locate the `hbis : m * b = n * c` hypothesis in the parent file, survey
  Mathlib's metric-geometry API, decide on a derivation path for S2.
* **Result**: above. Path A selected. Risk register surfaced one medium-likelihood
  obstruction (Mathlib `ring`-failure in the factorization step) with a
  `linear_combination` mitigation already identified.
* **Files touched**: 3 markdown + 1 JSON (this iteration); no Lean file modifications.
* **Build status**: unchanged.

## Next action (Session N=6 — S6 ACT)

S3 Steps 1–2 discharged (N=4). S4 PREP audited Steps (b)/(e). S5
STATE-SYNC + audit-extension (N=5) absorbed S4 PREP into state.md/JSON,
spot-checked the three deferred bearers (one materially corrected),
audited Steps (c)/(d)/(f), and resolved S4 PREP § 3.3's `...`
placeholders with a corrected disjunct-selection.

**S6 ACT scope**: discharge `angle_bisector_ratio_from_geometry`
(~80-120 LOC main theorem body). Per S4 PREP § 4 + S5 § 8.1, all 9
substantive readiness criteria GREEN; main theorem is paste-ready under
build-pending qualifier (precedent: ≥5 same-wave PRs). Recipe is split
across S4 PREP § 2 (Step b) + S5 § 4 (Step e, refined) + S5 § 5-7
(Steps c, d, f).

1. ~~**`bisector_param_exists`**~~ ✅ Discharged in N=4.
2. ~~**`bisector_dist_BD` / `bisector_dist_DC`**~~ ✅ Discharged in N=4.

3. **`angle_bisector_ratio_from_geometry`** (~80-120 LOC, in order):
   * Apply `bisector_param_exists` to get `s`.
   * Cosine equality via `Real.arccos_inj` + `InnerProductGeometry.cos_angle` (Step 1
     of strategy, §4 of `s2-prep-bearer-audit.md`).
   * Inner-product bilinearity expansion (Step 2-3 of strategy).
   * `linear_combination` to factorize as `((1-s)c − sb) · (bc − ⟪u,v⟫) = 0`
     (fallback to hand-witnessed `nlinarith` if `ring` fails).
   * Exclude `bc − ⟪u,v⟫ = 0` via `abs_real_inner_le_norm` strict form + non-collinearity
     (`collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` from `Affine.lean:378`).
   * Conclude `s · (b + c) = c`; multiply by `dist B C` to get `m · b = n · c`.

4. **(S4) `angle_bisector_length_geometric`** (~50 LOC): chain into parent's
   `angle_bisector_length` with `hbis := angle_bisector_ratio_from_geometry`,
   `ha := Sbtw.dist_add_dist`, and the two sub-triangle law-of-cosines from
   `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`.

S5+: gallery wiring (`meta.json`, `index.ts`) + parent's `openQuestions` update +
Mathlib-upstream candidate extraction.

## Blockers

None.
