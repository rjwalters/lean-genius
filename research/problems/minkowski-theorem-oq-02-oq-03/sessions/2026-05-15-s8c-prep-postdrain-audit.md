# S8-c PREP — post-drain audit: bearer re-verify + #19046 mergeability + S5-c/S6α sequencing

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: PREP (doc-only — no Lean / state / knowledge / problem / JSON edits)
**Author**: researcher-8
**Date**: 2026-05-15
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Branch base**: `origin/main` `ea85bb70b79` (post-drain-wave HEAD)

## Scope

The `2026-05-15T22:55-22:56Z` deployer drain wave (90 merges across
the repository in a single batch) landed two minkowski PREP siblings
on `main` within seconds of each other:

- **#19181 — S5-c PREP** (`dirichletSetN_volume` via rectangle-volume
  bridge, doc-only, +353 LOC sessions/file)
- **#19192 — S6 PREP-2** (`stdLatticeN_coords` v4.26.0 bearer audit +
  standalone S6α ACT plan, doc-only, +537 LOC sessions/file)

Plus #19283 (S5-b PREP, merged earlier at 18:01:41Z, doc-only).

State on this slug after the wave:

- **Three new PREPs landed without any STATE-SYNC update**: `state.md`
  was last bumped by Session 7 STATE-SYNC (#18967, merged 2026-05-14),
  which captures the S2/S3/S4 ACT + S5 PREP/PREP-2 + S6 PREP chain
  but predates #18975 (S5-a ACT), #19283, #19181, #19192. The open
  Session 8 STATE-SYNC (#18991) only catches up to #18975 — leaving
  three more PREPs un-recorded post-merge of #18991.
- **PR #19046 (S5-b ACT)** remains the sole open Lean-modifying PR,
  build-verified 3058 jobs at 2026-05-14, still `MERGEABLE / CLEAN`
  on this branch base.
- **#19181's recipe** is line-number-pinned to `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`
  at the **post-#19046-merge** layout (252 → ~333 LOC). With #19046
  still open, those pins are advisory, not current.

This PREP discharges **four** post-drain audit items as a doc-only,
strictly orthogonal addition to all open PRs on the slug. No
mathematical advancement: bookkeeping + sequencing only.

This PREP does **not** touch `state.md`, `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`,
or any `.lean` file. One new sessions/ file is created.

---

## §1. Bearer drift re-verify at Mathlib pin `2df2f0150c27...`

Re-verified all 6 bearers cited by #19181 and #19192 against the
lake-pinned Mathlib SHA via raw `https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/<path>`
fetches plus namespace context (last `namespace`/`end` directive
above the cited line).

| # | Bearer | Path | Line | Namespace at line | Signature head | Status |
|---|---|---|---|---|---|---|
| 1 | `Real.volume_pi_Ioo` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | **236** | `namespace Real` (line 51) | `theorem volume_pi_Ioo {a b : ι → ℝ} : volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)` | ✅ |
| 2 | `Real.map_matrix_volume_pi_eq_smul_volume_pi` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | **397** | `namespace Real` (line 51) | `theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : det M ≠ 0) : Measure.map (toLin' M) volume = ENNReal.ofReal (abs (det M)⁻¹) • volume` | ✅ |
| 3 | `Submodule.mem_span_range_iff_exists_fun` | `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean` | **372** | `namespace Submodule` | (as cited in #19192) | ✅ |
| 4 | `Pi.basisFun_apply` | `Mathlib/LinearAlgebra/StdBasis.lean` | **131** | `namespace Pi` (line 40) | `theorem basisFun_apply [DecidableEq η] (i) : basisFun R η i = Pi.single i 1` | ✅ |
| 5 | `Finset.sum_ite_eq'` | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` | **151** | `namespace Finset` | `@[to_additive (attr := simp)] theorem sum_ite_eq'` (additive of `prod_ite_eq'`) | ✅ `@[simp]` confirmed |
| 6 | `Int.cast_smul_eq_zsmul` | `Mathlib/Algebra/Module/NatInt.lean` | **151** | (root) | (modern non-deprecated form, direction-reversed vs `zsmul_eq_smul_cast`) | ✅ |

**Verdict.** All 6 bearers verified at pin. Zero substantive drift
since #19181 / #19192 were authored (both authored against the same
SHA and merged within ~12 min of this audit). The earlier
S5 PREP-2 (#18622) bearer-audit table for `Real.volume_pi_Ioo` and
`Real.map_matrix_volume_pi_eq_smul_volume_pi` also reconfirms.

**Earlier-PREP drift.** No re-verification needed for #18419
(S5 PREP, original shear-volume route) or #18622 (S5 PREP-2, original
bearer audit) — they cite an overlapping bearer subset of the above,
covered by rows 1–2.

---

## §2. PR #19046 (S5-b ACT) mergeability re-check on post-drain HEAD

`gh pr view 19046 --json mergeable,mergeStateStatus,headRefOid,baseRefOid` at
`2026-05-15T23:1XZ` (this cycle):

| Field | Value |
|---|---|
| `mergeable` | `MERGEABLE` |
| `mergeStateStatus` | `CLEAN` |
| `headRefOid` | `77fa321468dc…` |
| `baseRefOid` | `2afb1b79c0a4…` (≈ pre-drain) |
| `state` | `OPEN` |
| Diff size | `+79 / -0` in `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` |
| Build status (per PR body) | "build verified 3058 jobs" (2026-05-14) |

**Cross-PR safety re-check** of #19046's diff against the drain-wave
merges:

- **#19283 (S5-b PREP)**: only touches `sessions/2026-05-15-s5b-prep-Tv-preimage.md`. Disjoint from #19046's `.lean` changes. ✅
- **#19181 (S5-c PREP)**: only touches `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md`. Disjoint from #19046's `.lean` changes. ✅
- **#19192 (S6 PREP-2)**: only touches `sessions/2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md`. Disjoint. ✅

GitHub's `MERGEABLE / CLEAN` flag is consistent with this disjoint-set
analysis.

**Diff summary (4 new declarations added at file tail, lines 252 → 331)**:

| LOC | Declaration | Role |
|---|---|---|
| ~9 | `theorem shearM_toLin'_apply_zero` | `T v 0 = v 0` (row-0 mulVec collapse) |
| ~12 | `theorem shearM_toLin'_apply_succ` | `T v i.succ = α i * v 0 − v i.succ` |
| ~6 | `def dirichletBoxN (n : ℕ) (Q : ℕ) : Set (Fin (n + 1) → ℝ)` | axis-aligned box via `Set.pi` + `Fin.cases` |
| ~30 | `theorem dirichletSetN_eq_shearM_preimage` | Cassels = preimage of `dirichletBoxN` under `T` |

(LOC approximate; full diff is +79 / -0.)

---

## §3. Coupling between #19046 and #19181's S5-c recipe

#19181's §2 LOC table pins the S5-c ACT proof at lines 333 of
`MinkowskiTheoremOQ02OQ03.lean` — i.e., **post-#19046-merge** (the
parent file goes 252 → 331 LOC under #19046). Current `origin/main`
HEAD `ea85bb70b79` still has the **pre-#19046** layout (252 LOC,
ends at `end MinkowskiTheoremOQ02OQ03` after `shearM_det`).

This means:

1. **S5-c ACT MUST wait for #19046 to merge** (or use the mechanic-PR
   overlay pattern, `git apply` of #19046's diff transient for
   slug-only Docker validation — see `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`).
2. **#19181's bearer table (§1) is correct independently of #19046**
   (all 6 entries verified above).
3. **#19181's Step A / B / C all consume #19046's `dirichletBoxN`**.
   Without `dirichletBoxN` on `main`, none of #19181's 3 declarations
   typecheck.

| #19181 Step | Statement | Needs from #19046 | LOC |
|---|---|---|---|
| A | `dirichletBoxN_measurable` | `dirichletBoxN` (def) | ~3 |
| B | `dirichletBoxN_volume` (closed form `2^(n+1)(Q^n+1)/Q^n`) | `dirichletBoxN` (def) | ~15 |
| C | `dirichletSetN_volume` via pushforward | `dirichletSetN_eq_shearM_preimage` + `shearM_det = (-1)^n` (S5-a, ALREADY ON `main`) | ~25 |

**Sequencing constraint**: the PREP-defined S5-c ACT cannot ship as a
single coherent PR until `dirichletBoxN` lands on `main`. The
mechanic-overlay path (Option B in #19181's §6) is the fallback if
#19046 stalls.

---

## §4. `ENNReal`-valued `Real.volume_pi_Ioo` — return-type plumbing

This audit elaborates a point #19181 §1 footnote raises (the `abs ((-1)^n) = 1`
plumbing for `map_matrix_volume_pi_eq_smul_volume_pi`'s scalar) but
extends to the **return-type side** of `Real.volume_pi_Ioo`.

### §4.1. Signature recap (verified at pin)

```lean
theorem Real.volume_pi_Ioo {a b : ι → ℝ} :
    volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)
```

The RHS is **`ENNReal`-valued**, not `ℝ`-valued.

### §4.2. Two interpretations of `dirichletBoxN_volume`

`dirichletBoxN n Q` is the axis-aligned open box

- coord 0 : `(-((Q:ℝ)^n + 1), (Q:ℝ)^n + 1)` — length `2((Q:ℝ)^n + 1)`
- coords `k.succ` for `k : Fin n` : `(-1/(Q:ℝ), 1/(Q:ℝ))` — length `2/(Q:ℝ)` each

The pointwise lengths `b i − a i` are non-negative for any `Q ≥ 1`
(so the box is non-degenerate). The `Real.volume_pi_Ioo` formula
gives

```
volume dirichletBoxN = ENNReal.ofReal (2 * ((Q:ℝ)^n + 1))
                     * ∏ k : Fin n, ENNReal.ofReal (2 / (Q:ℝ))
                     = ENNReal.ofReal (2^(n+1) * ((Q:ℝ)^n + 1) / (Q:ℝ)^n)
```

The factor-out step (move `∏` inside `ENNReal.ofReal`) requires
`ENNReal.ofReal_prod_of_nonneg` (verified at
`Mathlib/Data/ENNReal/BigOperators.lean:49`,
signature: `∀ i ∈ s, 0 ≤ f i → ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i)`)
+ `ENNReal.ofReal_mul` (at `Mathlib/Data/ENNReal/Real.lean:294`,
signature: `0 ≤ p → ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q`).
For `Q ≥ 1`, the non-negativity side-condition `0 ≤ 2 / (Q : ℝ)` and
`0 ≤ 2 * ((Q : ℝ)^n + 1)` are both routine via `Q.cast_nonneg` +
`pow_nonneg` + linarith.

### §4.3. Two viable Lean targets for #19181's Step B

The S5-c ACT shipping `dirichletBoxN_volume` has two equally valid
target statements:

| Variant | Target | Pros | Cons |
|---|---|---|---|
| **B1 — ENNReal-valued (recommended)** | `volume dirichletBoxN = ENNReal.ofReal (2^(n+1) * ((Q:ℝ)^n + 1) / (Q:ℝ)^n)` | Direct from `Real.volume_pi_Ioo`; one `ENNReal.ofReal` factor-out chain; no extra `(Q ≥ 1)` hypothesis needed (`ENNReal.ofReal` is monotone, handles negative-input gracefully) | Downstream Step C must work with `ENNReal.ofReal` rather than raw ℝ |
| **B2 — ℝ-valued (cosmetic)** | `(volume dirichletBoxN).toReal = 2^(n+1) * ((Q:ℝ)^n + 1) / (Q:ℝ)^n` (with `Q ≥ 1`) | Reads as the textbook formula; matches problem.md statement | Extra `(volume ...).toReal` step adds ~5 LOC; needs `ENNReal.toReal_ofReal` (non-negativity hypothesis) |

#19181's §1 LOC budget of 15 LOC for Step B implicitly chooses B1
(no `Q ≥ 1` hypothesis surfaces in Step B; the `(Q ≥ 1)` constraint
lives at the parent `simultaneous_dirichlet_*` assembly level where
`Q ≥ 1` is needed for Minkowski's volume-vs-`2^(n+1)` comparison).

### §4.4. The `abs ((-1)^n) = 1` plumbing in Step C

#19181 §1 last paragraph flags this: `map_matrix_volume_pi_eq_smul_volume_pi`
gives `Measure.map T volume = ENNReal.ofReal (abs (det T)⁻¹) • volume`,
and `det (shearM n α) = (-1)^n` (from `shearM_det` already on `main`).

So `abs (det (shearM n α))⁻¹ = abs ((-1)^n)⁻¹ = (abs ((-1)^n))⁻¹ = 1⁻¹ = 1`.

Two simp strategies:

| Strategy | Approach | LOC | Robustness |
|---|---|---|---|
| **C-i** | `simp [shearM_det, abs_neg_one_pow, abs_one, inv_one]` | ~1 line | Robust at v4.26.0. `abs_neg_one_pow (n : ℕ) : |(-1 : α) ^ n| = 1` verified at `Mathlib/Algebra/Order/Ring/Abs.lean:69` (pin SHA `2df2f0150c27…`). `abs_one`, `inv_one` are core algebra lemmas. |
| **C-ii** | `rcases Nat.even_or_odd n with hn | hn; · simp [shearM_det, hn.neg_one_pow, abs_one, inv_one]; · simp [shearM_det, hn.neg_one_pow, abs_neg, abs_one, inv_one]` | ~3 lines | Falls back to parity case-split if C-i's `simp` lemma names drift |

C-i is the preferred path. The S5-c ACT must hold C-ii in reserve.

---

## §5. Sequencing chain (S5-b ACT → S5-c ACT → S6α ACT → S6 ACT)

Four ACT stages now have explicit recipes on `main`. Net LOC and
dependency chain:

| Stage | Recipe source | Net `.lean` LOC | Depends on | Conflict surface (today) |
|---|---|---|---|---|
| **S5-b ACT** | PR #19046 (OPEN, build-verified) | +79 | S5-a (`shearM_det`, on `main`) | none — orthogonal to all open PREPs |
| **S5-c ACT** | #19181 §3 recipe (~49 LOC, ENNReal-valued) | +49 | S5-b (#19046 merged) | none (recipe assumes #19046 on `main`) |
| **S6α ACT** | #19192 §5 refined skeleton (~22 LOC) | +22 | S5-a (`shearM_det`, on `main`) — **NOT** S5-b/S5-c | none — parallelizable with S5-b/S5-c |
| **S6 ACT** | #18511 (S6 PREP, on `main`) | ~80 | S5-c + S6α + lattice-extraction lemma | needs full chain |

**Critical observation about S6α.** #19192 §6 highlights that
`stdLatticeN_coords` (the residual integer-coordinate extraction
lemma) only depends on `S5-a` (already on `main`) — **not** on
the S5-b / S5-c chain. This means S6α ACT can ship in parallel
with S5-b ACT, halving the critical path.

**Recommended merge order** (assuming healthy deployer + Lean CI):

1. **PR #19046** (S5-b ACT, OPEN, build-verified, CLEAN) — merge first.
2. **Parallel** (or any order): **S5-c ACT** (~49 LOC) and **S6α ACT** (~22 LOC).
3. **S6 ACT** (full Minkowski assembly + integer extraction) once
   S5-c + S6α land.

---

## §6. STATE-SYNC stack (5 unrecorded merges + 1 pending merge)

`state.md` and the research JSON sidecar
`src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` are
both frozen at the Session 7 STATE-SYNC snapshot (PR #18967, merged
2026-05-14T03:04:19Z). Since then, **five merges** have landed
without `state.md` updates:

| # | PR | Phase | Merged (UTC) | What landed |
|---|---|---|---|---|
| 1 | #18975 | S5-a ACT | 2026-05-14T03:03:55Z | `shearM`, `shearM_lowerTriangular`, `shearM_det = (-1)^n` |
| 2 | #19283 | S5-b PREP | 2026-05-15T18:01:41Z | `Tv0`/`Tv_succ`/`rectN`/preimage proof templates (doc) |
| 3 | #19181 | S5-c PREP | 2026-05-15T22:56:26Z | `dirichletSetN_volume` rect-volume bridge recipe (doc) |
| 4 | #19192 | S6 PREP-2 | 2026-05-15T22:55:55Z | `stdLatticeN_coords` v4.26.0 audit + S6α plan (doc) |
| 5 | #19046 | S5-b ACT | (pending) | Linear-map components + preimage identity |

PR #18991 (Session 8 STATE-SYNC, OPEN since 2026-05-14T03:28:08Z)
catches up to **row 1 only** (S5-a ACT). Even after #18991 merges,
rows 2–5 (three drain-wave PREPs + the pending S5-b ACT) remain
unrecorded.

### §6.1. STATE-SYNC supersession plan

Three sequencing options:

| Option | Branch base for new STATE-SYNC | Captures | Risk |
|---|---|---|---|
| **A** | After #18991 merges | rows 2–4 (PREPs); S5-b ACT deferred to row-5 STATE-SYNC | Two STATE-SYNCs on slug |
| **B** | After #18991 + #19046 both merge | rows 2–5 (everything) | Single STATE-SYNC, but waits on #19046 |
| **C** | Now, superseding #18991 | rows 1–4 (all merged PREPs + S5-a ACT); S5-b ACT to follow-up | One STATE-SYNC closes #18991; second after #19046 |

**This PREP does NOT execute any STATE-SYNC** — it stages the
decision tree for the next state-touching iteration. Recommendation:
Option C if #18991 has stalled (>24h open with no Judge engagement);
Option A or B otherwise. Whichever path, the new STATE-SYNC must
write `MinkowskiTheoremOQ02OQ03.lean` into `currentState.leanFiles`
(missing entirely from JSON per #18991 §"Drift surface").

### §6.2. Conflict-free guarantee for this PREP

This PREP touches only **one** new file:
`sessions/2026-05-15-s8c-prep-postdrain-audit.md`. It does **not**
edit `state.md`, `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`,
or any `.lean` file. Cross-PR safety:

| PR | Title | Files touched | Conflict with this PREP? |
|---|---|---|---|
| #18991 | Session 8 STATE-SYNC | `state.md`, JSON | No — disjoint file set |
| #19046 | S5-b ACT (Lean) | `MinkowskiTheoremOQ02OQ03.lean` | No — disjoint file class |
| (this PR) | S8-c PREP — post-drain audit (doc-only) | new `sessions/…s8c-prep-postdrain-audit.md` only | n/a |

---

## §7. Hazards documented (5 items, for next S5-c / S6α / next-STATE-SYNC iterations)

1. **`Fin.cases_zero` opaque without explicit substitution.** Per
   #19283 §gap-1: the S5 PREP-2 §5.1 template `simp [Fin.cases_zero, Fin.cases_succ]`
   leaves `Fin.cases (1 : ℝ) α i` opaque if `i` is not first split via
   `Fin.cases i` / `refine i.cases ?_ ?_`. PR #19046 handles this via
   explicit `refine j.cases ?_ ?_` (verified in §2 diff).

2. **`Finset.sum_ite_eq'` vs `sum_ite_eq` directional pitfall.** Per
   #19192 §"5 hazards documented" #1: `Pi.single_apply` produces
   `if j = i then 1 else 0` (variable-first); `Finset.sum_ite_eq`
   wants `if i ∈ s then …`; only `Finset.sum_ite_eq'` matches.
   `'` form is required and verified at line 151 of
   `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean`.

3. **`Int.cast_smul_eq_zsmul` direction-reversed.** Per #19192
   §"hazards" #3: replaces the deprecated `zsmul_eq_smul_cast` alias
   but reverses the equation direction. Workaround:
   `Finset.sum_congr rfl (fun i _ => (Int.cast_smul_eq_zsmul _ _).symm)`.
   Verified at line 151 of `Mathlib/Algebra/Module/NatInt.lean`.

4. **`ENNReal.ofReal` factor-out for `dirichletBoxN_volume`** (NEW
   in this PREP). `Real.volume_pi_Ioo` returns
   `∏ i, ENNReal.ofReal (b i - a i)`. To collapse to a single
   `ENNReal.ofReal (closed-form)`, use `ENNReal.ofReal_prod_of_nonneg`
   (`Mathlib/Data/ENNReal/BigOperators.lean:49`, direction is
   `ofReal (∏ f) = ∏ (ofReal ∘ f)` under `0 ≤ f i`; here applied with `.symm`)
   followed by `ENNReal.ofReal_mul`
   (`Mathlib/Data/ENNReal/Real.lean:294`) chain. The non-negativity
   side-condition is routine for `Q ≥ 1`. Falls back to per-coord
   case-split if the bulk lemma rewrites stall. Estimated ~6 LOC overhead.

5. **`abs (det shearM)⁻¹ = 1` plumbing** (#19181 §1 last paragraph,
   reproduced in §4.4 above). C-i: one-line `simp [shearM_det, abs_neg_one_pow, abs_one, inv_one]`.
   C-ii: 3-line parity case-split fallback. C-i preferred.

---

## §8. Action items (forward-looking, no work done in this PREP)

1. **Land #19046 (S5-b ACT)** — currently CLEAN/MERGEABLE,
   build-verified 3058 jobs. Deployer-merge as priority #1 on this slug.
2. **Decide STATE-SYNC option (§6.1 A/B/C)** based on #18991's open-age
   and Judge engagement at the next claim of this slug.
3. **Ship S5-c ACT** (~49 LOC) and **S6α ACT** (~22 LOC) in parallel
   after #19046 merges. Both recipes pinned at this Mathlib SHA via
   #19181 and #19192 respectively.
4. **Ship S6 ACT** (~80 LOC) once S5-c + S6α land.

Estimated remaining `.lean` LOC to close OQ-03 from current `main`:
**~150 LOC** across 3 ACTs (S5-c + S6α + S6). One open PR + 3
sequenced ACTs to graduation.

---

## §9. Verification

- [x] Single new sessions/ file added; no modifications to existing files.
- [x] All 6 bearers re-verified via raw `https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/<path>` fetches and namespace-context cross-checks.
- [x] PR #19046 mergeability re-confirmed (`MERGEABLE / CLEAN`) on post-drain HEAD `ea85bb70b79`.
- [x] No conflict with #18991 (state.md / JSON) or #19046 (Lean file) — disjoint file sets.
- [x] Filename `2026-05-15-s8c-prep-postdrain-audit.md` does not collide with any existing session file (latest existing is `2026-05-15-s5b-prep-Tv-preimage.md`).
- [x] Branch base `ea85bb70b79` (post-drain `origin/main` HEAD).
- [x] Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) re-confirmed via `proofs/lake-manifest.json`.

---

## §10. Post-draft state addendum (added 2026-05-16T00:30Z, pre-push)

This PREP was drafted in the ~12-min window 2026-05-15T23:15Z → ~23:27Z while
PR #19046 (S5-b ACT) and PR #18991 (Session 8 STATE-SYNC) were both `OPEN`.
A subsequent deployer drain wave merged both before this branch was pushed:

| PR | Title | Merged (UTC) | Now on `main` |
|---|---|---|---|
| #19046 | S5-b ACT — shearM linear-map components + preimage identity (build verified, 3058 jobs) | 2026-05-15T23:27:39Z | yes |
| #18991 | Session 8 STATE-SYNC — refresh after #18975 S5-a ACT (doc-only) | 2026-05-15T23:29:31Z | yes |

Implications for §2, §6, §8 above (the audit body is preserved verbatim;
treat the table below as the live overlay):

- **§2 (PR #19046 mergeability re-check)** — predictive value retired;
  the snapshot (`MERGEABLE / CLEAN`, headRefOid `77fa321468dc…`,
  diff `+79 / -0`, 4 declarations at lines 252→331) is now the
  historical merge audit for the deployer-resolved PR. The diff
  summary in §2 corresponds 1-to-1 with what landed on `main`.
- **§3 / §5 (sequencing chain)** — "S5-c ACT MUST wait for #19046"
  precondition is **discharged**. Updated chain on `main`:
  `S5-c ACT (~49 LOC) ‖ S6α ACT (~22 LOC)` parallelizable now;
  `S6 ACT (~80 LOC)` once both land. Total remaining `.lean` LOC
  to OQ-03 graduation: **~150 LOC across 3 ACTs** (unchanged from §8).
- **§6.1 (STATE-SYNC supersession plan)** — Option **B** is now
  realizable in a single follow-up: the next state-touching iteration
  on this slug should catch §6 table rows 2–5 (`#19283 S5-b PREP`,
  `#19181 S5-c PREP`, `#19192 S6 PREP-2`, `#19046 S5-b ACT`) plus add
  `MinkowskiTheoremOQ02OQ03.lean` to `currentState.leanFiles` (still
  missing per #18991 §"Drift surface" — #18991 only catches up to
  row 1, S5-a).
- **§8 action item #1** ("Land #19046") — **closed**. Updated
  priority list:
  1. Ship the §6.1 Option-B STATE-SYNC (rows 2–5 + leanFiles fix).
  2. Ship S5-c ACT (~49 LOC) and S6α ACT (~22 LOC) in parallel
     once STATE-SYNC lands (or in parallel with STATE-SYNC if
     orthogonal — STATE-SYNC touches `state.md` + JSON only).
  3. Ship S6 ACT (~80 LOC) once S5-c + S6α land.

**Bearer drift re-check at post-merge `origin/main` HEAD `d35a6f0f2ac…`
(2026-05-16T00:25Z)**: the §1 6-row bearer table remains valid (no
Mathlib pin change between drafting and post-push verification — same
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The post-merge
parent-file layout for `MinkowskiTheoremOQ02OQ03.lean` now matches
#19181's line pins (252 → 331 LOC), so §3's "advisory, not current"
caveat is now also **discharged**: #19181's S5-c recipe pins are live
against `main`.

This addendum is doc-only and self-contained within the same sessions/
file; no other file edits.
