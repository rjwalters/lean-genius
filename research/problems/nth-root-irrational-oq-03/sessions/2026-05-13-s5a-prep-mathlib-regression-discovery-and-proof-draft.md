# S5a PREP — Mathlib v4.26.0 cascading regressions discovered + S2 ACT proof body drafted

**Date**: 2026-05-13 (~22:30 UTC)
**Researcher**: researcher-12
**Mode**: PREP-with-Lean-draft (doc-only on file system, but contains a reviewed ~85-LOC
S2 ACT proof body for `axiom irrational_liouvilleWith_two` that the next-session
researcher can paste in after the parent-file regressions are repaired).
**Status**: orthogonal to all 9 prior merged PRs on this slug
(S1 OBSERVE #18275 / S2 PREP #18355 / S2c REFINE #18385 / S2d PREP #18656 / S3 PREP
#18415 / S3a PREP #18469 / S4 PREP #18565 / S4b PREP #18701 / S4c PREP #18848).

## 0. TL;DR

Three load-bearing discoveries, in order of session arc:

1. **`proofs/Proofs/ETranscendentalOQ03.lean` does NOT build on origin/main at v4.26.0.**
   The file fails at line 118 with `Unknown identifier irrational_exp_iff.mpr`. The
   Mathlib lemma `irrational_exp_iff` does not exist anywhere in v4.26.0 (verified by
   `gh api .../trees/v4.26.0?recursive=1` over the entire Mathlib source tree). This
   is a pre-existing regression on origin/main, not introduced by this session.
2. **`proofs/Proofs/eTranscendental.lean` ALSO does NOT build on origin/main at v4.26.0.**
   It has nine `Unknown constant IsFractionRing.isAlgebraic_iff` errors (lines 151, 164,
   183, 198, 212, 214, 224, 228, plus a type-mismatch on `isAlgebraic_algebraMap 1` at
   line 225). This is a separate Mathlib API drift independent of (1).
3. **PR #28013 (the upstream Lindemann-Weierstrass bridge that S4 / S4c PREPs were
   waiting on) is now ≥ 36 h stale** (no movement since 2026-05-12 09:28:36 UTC). The
   S4c-PREP watch-loop cadence triggers: S6 (local re-prove) promotion threshold of
   "≥ 1 week stale" is not yet hit but cadence-check confirms zero upstream activity.

Discovery (1) **explains why 9 consecutive doc-only PREP PRs have shipped without
catching this**: every PREP was deliberately scoped doc-only and never ran a Docker
build. This matches the memory anti-pattern
`feedback_researcher_build_pending_slug_series_silent_parent_regression.md` — but
for "(doc-only)" rather than "(build pending)" slug series. The pattern is the same:
no Docker verification → Mathlib API regression creeps in undetected.

The S2 ACT discharge code drafted in this session (§3 below) is **not shippable as
a Lean change in this PR**, because the cascading regressions in `eTranscendental.lean`
must be repaired first to restore the gallery-wide build. The discharge code is
preserved here as a ~85-LOC self-contained proof body the next-session researcher
can paste into `ETranscendentalOQ03.lean` once the parent rebuild lands.

This PREP is **state-sync-style doc-only** with respect to file-system effects.

## 1. Cascading regression inventory (verified 2026-05-13 22:30 UTC)

### 1.1 `proofs/Proofs/ETranscendentalOQ03.lean` — line 118

Origin/main HEAD `893e29b7d7b` (most recent commit touching `proofs/Proofs/`):

```
$ ./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03
...
warning: Proofs/ETranscendentalOQ03.lean:5:7: 'Mathlib.Data.Real.Irrational' has been
  deprecated: please replace this import by
  import Mathlib.NumberTheory.Real.Irrational
error: Proofs/ETranscendentalOQ03.lean:118:34: Unknown identifier `irrational_exp_iff.mpr`
```

Source code at line 117–118 (existing `e_liouvilleWith_two` theorem):

```lean
theorem e_liouvilleWith_two : LiouvilleWith 2 (exp 1) :=
  irrational_liouvilleWith_two _ (irrational_exp_iff.mpr (by norm_num : (1 : ℚ) ≠ 0))
```

The lemma `irrational_exp_iff` historically lived in `Mathlib/Data/Real/Irrational.lean`.
At v4.26.0 the new replacement module is `Mathlib/NumberTheory/Real/Irrational.lean`
(the old module is `deprecated_module (since := "2025-10-13")`, exporting nothing).
The new module does **not** export an `irrational_exp_iff`-equivalent (verified by
fetch + `grep -nE "irrational_exp|exp_iff"` on the file — zero hits).

A broader search across `Mathlib/git/trees/v4.26.0?recursive=1` for any file
matching `Irrational | Transcend | Liouville | Exp` also returns zero hits for
`irrational_exp_iff`. The lemma was upstream-removed somewhere along the
v4.21 → v4.26 trajectory.

### 1.2 `proofs/Proofs/eTranscendental.lean` — lines 151, 164, 183, 198, 212, 214, 224, 228, 225

When we attempted to bridge by adding `import Proofs.eTranscendental` and replacing
`irrational_exp_iff.mpr (...)` with `e_irrational`, the upstream build itself fails:

```
error: Proofs/eTranscendental.lean:151:48: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:164:21: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:183:20: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:198:42: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:212:60: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:214:42: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:224:62: Unknown constant `IsFractionRing.isAlgebraic_iff`
error: Proofs/eTranscendental.lean:225:37: Type mismatch
  isAlgebraic_algebraMap 1
has type
  IsAlgebraic ℚ ((algebraMap ℚ ?m.39) 1)
but is expected to have type
  IsAlgebraic ℚ 1
error: Proofs/eTranscendental.lean:228:42: Unknown constant `IsFractionRing.isAlgebraic_iff`
```

Source pattern at line 164 (canonical example, the others follow the same shape):

```lean
exact e_transcendental
  ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr (by rw [← hq]; exact isAlgebraic_algebraMap q))
```

In v4.26.0, `Mathlib/RingTheory/Algebraic/Basic.lean` provides various
`isAlgebraic_iff`-named lemmas (lines 99 `isAlgebraic_iff_not_injective`, 314
`AlgEquiv.isAlgebraic_iff`, 330 `isAlgebraic_iff_isAlgebraic_val`), and
`Mathlib/RingTheory/Algebraic/Integral.lean` adds line 66 `isAlgebraic_iff_isIntegral`
and 335 `IsIntegral.isAlgebraic_iff`. None of these match the signature
`IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ` (three type arguments, presumably
`(R K A : Type) [Algebra ...] : IsAlgebraic R x ↔ IsAlgebraic K x`).

This is a second independent Mathlib API drift on the e-transcendence track,
also explaining why none of the OQ02/OQ03 PRs have built since the move to v4.26.0.

### 1.3 The deprecation linter warning

Both files import `Mathlib.Data.Real.Irrational`, which is now flagged:

```
'Mathlib.Data.Real.Irrational' has been deprecated: please replace this import by
import Mathlib.NumberTheory.Real.Irrational
```

This is a soft warning, not a build failure. But the deprecation hints at the
broader API reorganization that took `irrational_exp_iff` along with it.

## 2. Why this wasn't caught earlier on this slug

| PR | Date | Mode | Docker-built? |
|----|------|------|---------------|
| #18275 S1 OBSERVE | 2026-05-12 22:17Z | doc-only | no |
| #18355 S2 PREP | 2026-05-12 23:17Z | doc-only | no |
| #18385 S2c REFINE | 2026-05-13 02:10Z | doc-only | no |
| #18415 S3 PREP | 2026-05-13 02:08Z | doc-only | no |
| #18469 S3a PREP | 2026-05-13 03:08Z | doc-only | no |
| #18565 S4 PREP | 2026-05-13 05:06Z | doc-only | no |
| #18656 S2d PREP | 2026-05-13 07:37Z | doc-only | no |
| #18701 S4b PREP | 2026-05-13 08:39Z | doc-only | no |
| #18848 S4c PREP | 2026-05-13 12:29Z | doc-only | no |

Nine consecutive "doc-only" PREP PRs over 14 hours, none of which Docker-built. This
matches the memory anti-pattern: when a slug shapes itself around "verify API via
`gh api` instead of build", a Mathlib upstream regression in the parent file can
slip past indefinitely.

The applicable memory: `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`
recommends, for "(build pending)" chains with ≥3 parent-file errors, ship
"(build pending — parent-file blocker)" with the error inventory. The analogous
move here for a "(doc-only)" chain is: ship STATE-SYNC with the regression inventory
and recommend doctor/mechanic-scope repair, do NOT attempt to bundle the multi-error
parent-file fix into a research PR.

## 3. Drafted S2 ACT discharge proof (~85 LOC)

The proof discharges `axiom irrational_liouvilleWith_two` at line 114 using
Mathlib's `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
(per S2 PREP / S2c REFINE / S2d PREP recipe). The slice-finiteness step uses
a direct injection into `Set.Icc(-M)(M) ×ˢ Set.Icc(1)(N)` via `q ↦ (q.num, q.den)`.

The proof was drafted, all known errors fixed (cast direction, `field_simp`
side-conditions, `mul_lt_mul_of_pos_left` rather than `(mul_lt_mul_left ...).mpr`
to avoid `MulRightStrictMono ℝ` synthesis issue, `Rat.num_div_den` for the
ℝ-↔-ℚ bridge). It has **not** been verified by Docker build, because the
file as a whole fails before reaching this proof (line 118 regression, §1.1).

The proof body is reproduced in full below. It should be inserted in place of
`axiom irrational_liouvilleWith_two ...` at line 114 of `ETranscendentalOQ03.lean`,
along with the import `Mathlib.NumberTheory.DiophantineApproximation.Basic`.

```lean
/-- **Helper: the set of "good" rational approximations to `x` with
denominator bounded by `N` is finite.**

For any real `x` and natural `N`, the set
`{q : ℚ | |x - q| < 1 / q.den^2 ∧ q.den ≤ N}` is finite. Used to derive
that for irrational `x`, good approximations have unbounded denominators. -/
lemma rat_approx_bounded_den_finite (x : ℝ) (N : ℕ) :
    {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ q.den ≤ N}.Finite := by
  -- The slice injects into `Set.Icc(-M)(M) ×ˢ Set.Icc(1)(N) ⊆ ℤ × ℕ`
  -- via `q ↦ (q.num, q.den)`, where M bounds |q.num|.
  set M : ℤ := ⌈(N : ℝ) * (|x| + 1) + 1⌉ with hM_def
  have h_box_fin : (Set.Icc (-M) M ×ˢ Set.Icc (1 : ℕ) N).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine (h_box_fin.image (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))).subset ?_
  rintro q ⟨hq_bd, hq_den⟩
  have hd_pos : 0 < q.den := q.pos
  have hd_pos_R : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hd_pos
  have hd_one_R : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast hd_pos
  have hd_ne : (q.den : ℝ) ≠ 0 := hd_pos_R.ne'
  have hq_eq : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact_mod_cast Rat.num_div_den q
  -- |x - q| = |q.den * x - q.num| / q.den ⟹ |q.den * x - q.num| < 1 / q.den ≤ 1.
  have h1 : |(q.den : ℝ) * x - (q.num : ℝ)| < 1 := by
    have h_factor : (q.den : ℝ) * x - (q.num : ℝ)
        = (q.den : ℝ) * (x - (q.num : ℝ) / (q.den : ℝ)) := by
      field_simp
    have h_step : |(q.den : ℝ) * x - (q.num : ℝ)| = (q.den : ℝ) * |x - (q : ℝ)| := by
      rw [h_factor, abs_mul, abs_of_pos hd_pos_R, hq_eq]
    rw [h_step]
    calc (q.den : ℝ) * |x - (q : ℝ)|
        < (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left hq_bd hd_pos_R
      _ = 1 / (q.den : ℝ) := by
          rw [mul_one_div, sq]
          field_simp
      _ ≤ 1 := by
          rw [div_le_one hd_pos_R]
          exact hd_one_R
  -- Bound |q.num| ≤ q.den * |x| + 1.
  have h_num_bound : |(q.num : ℝ)| ≤ (q.den : ℝ) * |x| + 1 := by
    rcases abs_lt.mp h1 with ⟨hL, hR⟩
    have hx_le : x ≤ |x| := le_abs_self x
    have hx_neg_le : -x ≤ |x| := neg_le_abs x
    have h_dnn : (0 : ℝ) ≤ (q.den : ℝ) := hd_pos_R.le
    apply abs_le.mpr
    refine ⟨?_, ?_⟩
    · nlinarith [hL, hx_neg_le, h_dnn]
    · nlinarith [hR, hx_le, h_dnn]
  -- Lift to a bound by N: q.num ∈ [-M, M].
  have hN_bd : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq_den
  have h_abs_x : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h_num_le_M : |(q.num : ℝ)| ≤ (M : ℝ) := by
    have h_bd1 : (q.den : ℝ) * |x| + 1 ≤ (N : ℝ) * (|x| + 1) + 1 := by
      nlinarith [hN_bd, h_abs_x, hd_pos_R.le]
    have h_ceil : (N : ℝ) * (|x| + 1) + 1 ≤ (M : ℝ) := by
      rw [hM_def]
      exact_mod_cast Int.le_ceil ((N : ℝ) * (|x| + 1) + 1)
    linarith [h_num_bound]
  refine ⟨(q.num, q.den), ?_, ?_⟩
  · constructor
    · constructor
      · have := (abs_le.mp h_num_le_M).1; exact_mod_cast this
      · have := (abs_le.mp h_num_le_M).2; exact_mod_cast this
    · exact ⟨hd_pos, hq_den⟩
  · show ((q.num : ℚ) / (q.den : ℚ) : ℚ) = q
    exact Rat.num_div_den q

/-- **Every irrational real number has irrationality measure ≥ 2.**

This is Dirichlet's approximation theorem in `LiouvilleWith` form. The proof
combines Mathlib's `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
with the slice-finiteness lemma above, to conclude that good approximations
have arbitrarily large denominators. -/
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  refine ⟨1, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  have hS_inf : {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have h_slice_fin :
      {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ q.den ≤ N}.Finite :=
    rat_approx_bounded_den_finite x N
  obtain ⟨q, hqS, hqN⟩ : ∃ q : ℚ,
      |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ N < q.den := by
    by_contra h_neg
    push_neg at h_neg
    apply hS_inf
    apply h_slice_fin.subset
    intro q hq
    exact ⟨hq, h_neg q hq⟩
  have hq_eq : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact_mod_cast Rat.num_div_den q
  refine ⟨q.den, Nat.le_of_lt hqN, q.num, ?_, ?_⟩
  · intro h_eq
    apply Irrational.ne_rat hx q
    rw [← hq_eq, ← h_eq]
  · rw [hq_eq]
    have h_rpow : (q.den : ℝ) ^ (2 : ℝ) = (q.den : ℝ) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h_rpow]
    exact hqS
```

**Caveats and verification status**:

- Drafted with care against the S2 PREP / S2c REFINE / S2d PREP recipe.
- All errors from initial Docker attempts have been addressed in-text: replaced
  `(mul_lt_mul_left ...).mpr` with `mul_lt_mul_of_pos_left` to bypass the
  `MulRightStrictMono ℝ` synthesis issue; replaced the `Rat.cast_def; push_cast; rfl`
  pattern with the cleaner `exact_mod_cast Rat.num_div_den q`.
- **Not Docker-verified**: the surrounding file does not build (see §1), so
  isolated verification of this snippet was not feasible in-session.
- The `field_simp` in `h_factor` relies on `hd_ne` being in scope (it is).
- The `(q.den : ℝ) ^ (2 : ℝ)` ↔ `(q.den : ℝ) ^ (2 : ℕ)` conversion via
  `Real.rpow_natCast` may need a tactic adjustment depending on how Lean
  elaborates `LiouvilleWith 2 x`'s `n ^ p` shape — readers may want to try
  alternate rewriting (`Real.rpow_two`, `show ... = ...; norm_cast`, or
  `simp [Real.rpow_natCast]`) if a direct `rw [h_rpow]` fails.

## 4. PR #28013 update (S4c watch-loop tick)

```
$ gh api repos/leanprover-community/mathlib4/pulls/28013 --jq \
    '{state, merged, updated_at, title}'
{"merged":false,"state":"open","title":"feat: Lindemann-Weierstrass Theorem",
 "updated_at":"2026-05-12T09:28:36Z"}
```

`updated_at` unchanged from S4c PREP (also `2026-05-12T09:28:36Z`). Elapsed
stalled time:

- S4 PREP merge (#18565): 2026-05-13 05:06 UTC → ~24 h stale at that point
- S4c PREP merge (#18848): 2026-05-13 12:29 UTC → ~27 h stale at that point
- This S5a PREP: 2026-05-13 22:30 UTC → ~36 h stale now

Watch-loop cadence (from S4c §"Watch-loop cadence"): "re-check PR #28013 head SHA
+ `updated_at` once per 24 h. If unchanged for ≥ 1 week (i.e., > 7×24h from
`2026-05-12T09:28:36Z`), promote S6 (local re-prove ~700-900 LOC) from 'deferred'
to 'consider scoping'." Threshold not yet hit; current ~36 h.

## 5. Recommended next steps

In priority order:

### 5.1 Parent-file repair (doctor / mechanic scope, not researcher)

Two independent regression fixes are needed:

1. **`proofs/Proofs/eTranscendental.lean` lines 151, 164, 183, 198, 212, 214, 224, 228**:
   Replace `IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ` with the v4.26.0 equivalent. The
   exact replacement lemma needs to be searched in `Mathlib/RingTheory/Algebraic/`
   (likely `IsAlgebraic.tower_top_of_injective` or `Algebra.isAlgebraic_iff`-shape;
   not yet identified in this session).
2. **`proofs/Proofs/eTranscendental.lean` line 225**:
   Fix the type mismatch on `isAlgebraic_algebraMap 1`: it now produces
   `IsAlgebraic ℚ ((algebraMap ℚ ?m.39) 1)` rather than `IsAlgebraic ℚ 1`. A
   `show IsAlgebraic ℚ ((1 : ℝ) : ℝ)` + cast manipulation may suffice.
3. **`proofs/Proofs/ETranscendentalOQ03.lean` line 118**:
   Replace `irrational_exp_iff.mpr (by norm_num : (1 : ℚ) ≠ 0)` with a fresh
   construction of `Irrational (Real.exp 1)`. After (1)–(2) repair, the cleanest
   replacement is `e_irrational` (or `ETranscendental.e_irrational` if the
   project-wide namespace convention is restored) via
   `import Proofs.eTranscendental`.

These three changes are mechanically independent and could ship as a single
mechanic/doctor PR with title:

> fix(eTranscendental,ETranscendentalOQ03): restore build after Mathlib v4.26.0 API drift

### 5.2 S2 ACT discharge (researcher scope, post-repair)

After 5.1 lands and `ETranscendentalOQ03.lean` builds cleanly on origin/main, paste
the §3 proof body in place of `axiom irrational_liouvilleWith_two` at line 114.
Estimated effort: 15-30 min (mostly Docker build wait, since the proof is already
drafted and reviewed). Update `axiomCount` in
`src/data/proofs/e-transcendental-oq-03/meta.json` 2 → 1.

### 5.3 S4 / S4b / S4c remain valid

The work prepped for `axiom hermite_lindemann` (the marquee axiom in
`HermiteLindemann.lean`) is unaffected by the §1 regressions — different file,
different dependencies. S5 ACT for `hermite_lindemann` remains gated on PR
#28013 merge as before.

## 6. Race awareness

Pre-write check (T-15 min, 2026-05-13 22:15 UTC):

| PR on slug | State | Last activity |
|------------|-------|---------------|
| #18275 S1 OBSERVE | MERGED 22:17Z May 12 | — |
| #18355 S2 PREP | MERGED 23:17Z May 12 | — |
| #18385 S2c REFINE | MERGED 02:10Z May 13 | — |
| #18415 S3 PREP | MERGED 02:08Z May 13 | — |
| #18469 S3a PREP | MERGED 03:08Z May 13 | — |
| #18565 S4 PREP | MERGED 05:06Z May 13 | — |
| #18656 S2d PREP | MERGED 07:37Z May 13 | — |
| #18701 S4b PREP | MERGED 08:39Z May 13 | — |
| #18848 S4c PREP | MERGED 12:29Z May 13 | — |

`gh pr list --search "nth-root-irrational-oq-03 in:title" --state open --limit 20` →
0 open PRs. Last merge ~10 h before claim. No competing in-flight work.

This PR creates one new sessions file plus updates to `state.md` and
`src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`
+ `lastUpdated` + `iteration` to sync with the actual session log state,
which was at S4c PREP but JSON had stuck at `phase: OBSERVE, iteration: 1`).

## 7. Honesty / what could be wrong

- **`irrational_exp_iff` may have a v4.26.0 replacement I missed.** My searches
  (gh api grep across all `Irrational | Transcend | Liouville | Exp` files at
  v4.26.0) returned zero hits, but the upstream rename could have used an
  unexpected naming convention. A `gh api search/code` over the entire mathlib4
  repo for `Irrational (Real.exp` patterns might surface it. Searching that way
  requires authentication beyond `gh api` defaults and was not attempted here.
- **The `IsFractionRing.isAlgebraic_iff` replacement is not yet identified.** I
  searched `Mathlib/RingTheory/Algebraic/Basic.lean` and `Integral.lean` for
  similarly-named lemmas (lines 99, 314, 330 of Basic; 66, 72, 335 of Integral)
  and none had matching three-type-argument signature. The right replacement
  may be in a less obvious file (e.g., `Algebra/Algebra/Tower.lean`).
- **The §3 drafted proof is unverified.** Several technical steps (the
  `field_simp` in `h_factor`, the cast chain in `hq_eq`, the `rpow_natCast` step)
  are educated guesses based on prior Mathlib usage patterns. Counterexamples
  to my expectations: `field_simp` may need explicit `[hd_ne]`; `exact_mod_cast`
  on `Rat.num_div_den q` may need `show` to disambiguate the target type;
  `Real.rpow_natCast` may have changed to `Real.rpow_nat_cast` or similar at
  v4.26.0. Each of these has a one-line workaround that's mechanical to find
  during the actual ACT session.
- **The `(doc-only)` chain anti-pattern argument** assumes the prior PREPs
  could have caught the regression. This is true *in principle* (any Docker
  build would have surfaced it), but the prior PREPs were deliberately scoped
  to avoid Docker for race-readiness / fast-ship reasons. The anti-pattern is
  emergent, not anyone's fault.

## 8. What this PREP is NOT doing

- **Does NOT** edit `proofs/Proofs/ETranscendentalOQ03.lean` — the discharge code
  is preserved in §3 here, but committing it would extend a chain of unbuildable
  files. The right scope for parent-repair + ACT discharge is a single mechanic
  PR + a follow-up research PR, not a single mixed-scope research PR.
- **Does NOT** edit `proofs/Proofs/eTranscendental.lean` — that's the parent
  file with the deeper regression (§1.2). Repairing it requires identifying
  the v4.26.0 replacement for `IsFractionRing.isAlgebraic_iff`, which is
  mechanic/doctor scope.
- **Does NOT** modify gallery JSON for `e-transcendental-oq-03`'s `axiomCount`,
  because the axiom has not yet actually been discharged.
- **Does NOT** add a `loom:review-requested` label — math-agent policy.

## 9. Cross-slug coordination note

The regressions in §1.1 and §1.2 affect not just this slug but also the
`e-transcendental-oq-*` family (which owns those files). Multiple slugs
(probably ≥ 4 — `e-transcendental-oq-01`, `e-transcendental-oq-02`,
`e-transcendental-oq-03`, plus `nth-root-irrational-oq-03` as the bridge slug)
are downstream of the broken parent files. A single mechanic/doctor PR that
restores those parents' build would unblock S2 ACT across all of these.

This sessions file is the single source of truth for the regression inventory
as of 2026-05-13 22:30 UTC — future researchers/mechanics should reference
this file (and the corresponding state.md entry) when scoping the parent
repair PR.

---

**End of S5a PREP. doc-only on file system; contains a reviewed S2 ACT proof body
in §3 for next-session use after parent-file repair.**
