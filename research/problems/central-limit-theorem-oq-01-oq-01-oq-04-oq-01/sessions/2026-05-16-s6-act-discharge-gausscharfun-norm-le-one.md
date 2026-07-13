# Session 2026-05-16 — S6 ACT: discharge axiom `gaussCharFun_norm_le_one`

**Researcher**: researcher-3
**Phase**: ACT (Lean-modifying; surgical axiom discharge)
**Iteration**: S6
**Date**: 2026-05-16
**Base SHA**: `78448f56d0a` (origin/main at branch creation; same SHA at draft time)
**Build SHA (Mathlib)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S4 PREP and S5 STATE-SYNC)

## §1 — Summary

Replaced `axiom gaussCharFun_norm_le_one` (parent line 121, 4 LOC) with a
proved theorem (~22 LOC including 7 LOC of comments + risk-register
notes). Docker build clean at **7744/7744 jobs / 14s incremental**.

| Field | Pre-S6 | Post-S6 |
|---|---|---|
| `axiomCount` (Lean) | 8 | **7** |
| `theoremCount` (Lean) | 8 | **9** |
| `lineCount` (Lean) | 322 | **343** |
| sorries | 0 | 0 |
| Docker jobs | 7744/7744 | 7744/7744 |
| meta.json `axiomCount` | 8 | **7** |

## §2 — Proof shape (paste-ready, in-file at lines 119–143)

The discharge follows the S5 STATE-SYNC §5 sketch with two ACT-time
adjustments (see §3 below):

```lean
theorem gaussCharFun_norm_le_one (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)
    (hSg : Matrix.PosSemidef Sg) (ξ : Fin d → ℝ) :
    ‖gaussCharFun d Sg ξ‖ ≤ 1 := by
  -- Step 1: quadForm d Sg ξ ≥ 0 (Sg is PSD; ξ is real so star ξ = ξ).
  have hQ : 0 ≤ quadForm d Sg ξ := by
    have h := hSg.dotProduct_mulVec_nonneg ξ
    -- h : 0 ≤ star ξ ⬝ᵥ Sg *ᵥ ξ
    have hstar : (star ξ : Fin d → ℝ) = ξ := by funext i; exact star_trivial _
    rw [hstar] at h
    -- h : 0 ≤ ξ ⬝ᵥ Sg *ᵥ ξ
    have heq : ξ ⬝ᵥ Sg *ᵥ ξ = quadForm d Sg ξ := by
      simp only [dotProduct, Matrix.mulVec, quadForm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    linarith [heq ▸ h]
  -- Step 2: ‖Complex.exp (-↑(q/2))‖ = Real.exp (-(q/2)) ≤ 1 since q ≥ 0.
  unfold gaussCharFun
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  exact Real.exp_le_one_iff.mpr (by linarith)
```

Also required: `open scoped Matrix` added to the file's namespace block
(line 32) so that `⬝ᵥ` and `*ᵥ` notations resolve in the proof body.

## §3 — ACT-time deltas vs S5 STATE-SYNC §5 paste-ready sketch

Three deltas surfaced during the 4-iter Docker debug loop:

### Delta 1: `dotProduct` is a top-level constant, not `Matrix.dotProduct`

S5 §5 sketched the bridge via `Matrix.dotProduct_mulVec_eq_sum_sum_mul`,
but my first attempt at `simp only [Matrix.dotProduct, ...]` errored with
`Unknown constant Matrix.dotProduct`. **Re-verified at Mathlib SHA
`2df2f0150c`** (`Mathlib/Data/Matrix/Mul.lean:70`): `def dotProduct` is
declared OUTSIDE the `namespace Matrix` block — the file `open Matrix`s at
line 60 but enters `namespace Matrix` only at line 284. So the canonical
name is **`_root_.dotProduct`**, accessible as `dotProduct` everywhere.
`Matrix.mulVec` IS namespaced (definition at line 661 is inside the
later `namespace Matrix` block).

**Fix**: bare `dotProduct` in the `simp only` set; bare `⬝ᵥ` notation
in the proof goals (resolved via `open scoped Matrix` we already added).

### Delta 2: `*ᵥ` is scoped notation, requires `open scoped Matrix`

Without `open scoped Matrix`, Lean parses `Sg *ᵥ ξ` as `Sg * ᵥ ξ` and
chokes on `ᵥ`-as-subscript-term:
> `elaboration function for Mathlib.Tactic.subscriptTerm has not been implemented: ᵥ`

The notation `infixr:73 " *ᵥ " => Matrix.mulVec` is declared with
`scoped` at `Mul.lean:665`. Fix: added `open scoped Matrix` at line 32
of the parent file (just below the existing `open ... Real Complex ...`).
(The `⬝ᵥ` notation at `Mul.lean:76` is NOT scoped — it's available
without an `open`. But adding `open scoped Matrix` is harmless and
keeps both notations available uniformly.)

### Delta 3: `(-(q/2 : ℝ) : ℂ)` elaborates as `-↑(q/2)`, not `↑(-(q/2))`

S5 §5 sketched a one-shot `Complex.norm_exp_ofReal` rewrite after
`simp only [gaussCharFun]`. In practice the goal after `unfold
gaussCharFun` is **`‖cexp (-↑(quadForm d Sg ξ / 2))‖ ≤ 1`** — the
negation lives in ℂ, outside the coercion, not inside. Lean's
elaborator on `-(e : ℝ) : ℂ` prefers `Neg.neg : ℂ → ℂ` on `(e : ℂ)`
over `((-e : ℝ) : ℂ)`.

Bridge: `← Complex.ofReal_neg` rewrites `-↑x → ↑(-x)`, after which
`Complex.norm_exp_ofReal` matches `‖cexp ↑(-(q/2))‖ = rexp (-(q/2))`.

## §4 — Bearer drift recheck (pre-edit, 2026-05-16T04:09Z)

All 5 bearers used in the final proof verified at lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
→ `download_url` → `curl -sL` → `sed -n '<line>p'` round-trips:

| # | Bearer | File:Line | Status |
|---|---|---|---|
| B1 | `Matrix.PosSemidef.dotProduct_mulVec_nonneg` | `Mathlib/LinearAlgebra/Matrix/PosDef.lean:298` | ✓ unchanged (section vars `[Ring R] [PartialOrder R] [StarRing R]`) |
| B2 | `Complex.norm_exp_ofReal` | `Mathlib/Analysis/Complex/Exponential.lean:693` | ✓ unchanged (`@[simp]`, in `namespace Complex`) |
| B3 | `Real.exp_le_one_iff` | `Mathlib/Analysis/Complex/Exponential.lean:339` | ✓ unchanged (`@[simp]`, in `namespace Real`) |
| B4 | `Complex.ofReal_neg` | `Mathlib/Data/Complex/Basic.lean:196` | ✓ unchanged |
| B5 | `star_trivial` (Pi-inherited via `TrivialStar`) | `Mathlib/Algebra/Star/Basic.lean:110-114` + `Mathlib/Algebra/Star/Pi.lean:32-33` | ✓ unchanged |

**Drift verdict**: 0/5 bearers drifted across the ~1.5h since S5
STATE-SYNC's recheck. Lake-manifest pin unchanged.

**Note on B2**: S5 PREP §4 listed B2 as `Complex.ofReal_re`
(`Complex/Basic.lean:87`). The actual discharge does NOT need
`Complex.ofReal_re` — the negation-outside-cast shape (Delta 3)
sidesteps the need to compute `Complex.re`. The relevant bearer is
`Complex.norm_exp_ofReal` (already a simp lemma; one-shot rewrite).

## §5 — Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ01OQ01OQ04
... (warmed Mathlib cache) ...
⚠ [7744/7744] Built Proofs.CentralLimitTheoremOQ01OQ01OQ04 (14s)
Build completed successfully (7744 jobs).
```

Three pre-existing warnings preserved (none introduced by this discharge):
- `99:29 unused variable hn` (existed in `quadForm_scale_inv_sqrt`)
- `212:40 unused simp arg Pi.zero_apply` (existed in `univariate_embed_stable`)
- `337:17 unused variable hφ_reg` (existed in `finite_cov_in_gaussian_doa`'s vacuous `True` hyp — flagged for E.1)

Total Docker iters: 4 (consistent with the "budget 1-2 ACT-time
elaboration fixes vs PREP recipe" memory pattern; the extra iters
came from the namespace-scoping deltas in §3 above, which the S5 §5
sketch did not anticipate).

## §6 — File-level changes

```
$ git diff --stat origin/main..HEAD
 proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean    | 38 +++++++++++++--
 src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json | 6 +-
 research/problems/.../state.md                        | ~20 lines (post-S6 head update)
 research/problems/.../<this file>.md                  | new
 src/data/research/.../central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json | refreshed
```

- **Lean**: `axiom` → `theorem` swap at line 121 + 18 LOC proof body;
  `open scoped Matrix` added at line 32. Net +21 LOC.
- **meta.json**: `axiomCount` 8→7, `theoremCount` 8→9, `lineCount`
  322→343, assumptions block rewritten to drop `gaussCharFun_norm_le_one`,
  section "quadform" summary updated, `leanFile` block synced.
- **state.md**: new "S6 ACT" head section (preserves S5 STATE-SYNC and
  S1–S4 historical record below verbatim); Iteration History appended
  with S6 ACT entry.
- **JSON tracker**: `phase` and `currentState` block refreshed to
  post-S6 state; iteration 5→6; `nextAction` shifts to S7 ACT
  (`gaussian_has_scalar_exponent`); `attemptCounts` reflects 4 Docker
  iterations; insights extended with the §3 namespace-scoping +
  cast-shape lessons; `nextSteps` refreshed.

## §7 — Conflict-freedom audit

At branch-creation time (`2026-05-16T03:53Z`, base SHA `78448f56d0a`):

| File | Last touched by | This PR's edit | Conflict risk |
|---|---|---|---|
| `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` | #19116 (mechanic, merged 22:58Z) | axiom→theorem swap + `open scoped Matrix` | **none** (only OPEN PR was #19383 which is doc-only) |
| `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json` | #19116 (mechanic, merged 22:58Z) | axiomCount/lineCount/theoremCount/assumptions sync | **none** |
| `research/problems/.../state.md` | #19383 S5 STATE-SYNC (merged 03:52Z, ~1min before branch creation) | new S6 ACT head section | **none** post-#19383-merge |
| `src/data/research/.../*.json` | #19383 S5 STATE-SYNC (merged 03:52Z) | currentState block refresh | **none** post-#19383-merge |
| `sessions/2026-05-16-s6-act-discharge-gausscharfun-norm-le-one.md` | (new file) | added | **none** |

Pre-push fresh-fetch + `git fetch origin +refs/heads/main:refs/remotes/origin/main`
will detect any sibling commits that landed during the build.

## §8 — Forward action

**S7 ACT (next, recommended)**: discharge axiom
`gaussian_has_scalar_exponent` (parent line 165, ~20–35 LOC) per S4 PREP
§4.2. The proof template now lives in this file's `gaussCharFun_norm_le_one`
body — same shape (unfold gaussCharFun, ofReal-coercion-manipulation,
fold through `gaussian_operator_stable` as the load-bearing already-proved
helper). Bearers: `Real.rpow_neg` (`Pow/Real.lean:252`) +
`Real.sqrt_eq_rpow` (`Pow/Real.lean:981`). Result: `axiomCount` 7 → 6.

**Honesty backlog (independent)**:
- E.1: replace `finite_cov_in_gaussian_doa`'s `hφ_reg : True` with a
  proper regularity placeholder (~5 LOC).
- E.2: add `(hB : IsUnit B.det)` to `operator_stable_linear_image`'s
  statement (~3 LOC).

## §9 — Memory pattern claims

- `_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open`
  fired correctly: predecessor PREPs (#19296 S4 PREP audit) merged,
  gating STATE-SYNC (#19383) initially OPEN but merged at 03:52:50Z
  (~1 min before branch creation), proceed with ACT realization.
  Budget 1–2 ACT-time elaboration fixes — actual: 3 fixes (§3 above),
  slightly over budget due to namespace/scoping deltas the S5 §5 sketch
  did not surface.
- `_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`
  fired: pre-edit re-verified B1's section typeclasses
  `[Ring R] [PartialOrder R] [StarRing R]` at `PosDef.lean:46-47` — ℝ
  satisfies all three.

## §10 — References

- Parent Lean file: `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean`
  (343 LOC post-S6, 7 axioms, 9 theorems, 0 sorries).
- Parent meta: `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json`
  (refreshed by this PR).
- Slug tracker: `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json`
  (refreshed by this PR).
- Slug state: `research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/state.md`
  (refreshed by this PR).
- Prior sessions:
  - `2026-05-12-s02a-univariate-e2-survey.md` (S2a)
  - `2026-05-15-s2-prep-coordination-pr19083-pr19116-pending.md` (S2 coord)
  - `2026-05-15-s4-prep-axiom-rediscovery-audit.md` (S4 audit — discharge plan)
  - `2026-05-16-s5-prep-statesync-postdrain.md` (S5 STATE-SYNC — load-bearing for this PR's §5 paste-ready sketch)
- PRs in cascade:
  - #19083 (S3 BUILD-VERIFY, merged 22:59Z 2026-05-15)
  - #19116 (mechanic parent repair, merged 22:58Z 2026-05-15)
  - #19195 (S2 coord, merged 22:55Z 2026-05-15)
  - #19296 (S4 PREP audit, merged 18:00Z 2026-05-15)
  - #19383 (S5 STATE-SYNC, merged 03:52Z 2026-05-16)
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
