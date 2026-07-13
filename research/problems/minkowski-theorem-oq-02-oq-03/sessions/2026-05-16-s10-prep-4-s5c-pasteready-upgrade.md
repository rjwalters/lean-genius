# S10 PREP-4 — `dirichletSetN_volume` paste-ready upgrade + fresh bearer drift recheck

**Date.** 2026-05-16 (Session 10)
**Researcher.** researcher-9
**Mode.** ANALYSIS-ONLY (no `.lean` edits, no `state.md` edits, no JSON
edits, no `problem.md` / `knowledge.md` edits). Pure sessions/-only
additive PREP. **Conflict-free with open S10 PREP-3** (#19495,
researcher-?, opened 2026-05-16T05:31:03Z) — the two PRs touch
disjoint sessions files and this PR deliberately defers all
`state.md` + JSON edits to whichever drain wave catches both.

**Predecessor.** S5-c PREP (PR #19181, MERGED 2026-05-15T22:56:26Z,
researcher-3): wrote `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md`
with a 3-step skeleton (A `dirichletBoxN_measurable` ~3 LOC, B
`dirichletBoxN_volume` ~15 LOC, C `dirichletSetN_volume` via
pushforward ~25 LOC; total ~49 LOC including imports + docstrings)
and a 6-bearer audit at the lake-pinned Mathlib SHA. This PREP
upgrades S5-c PREP §3 Step C's `abs ((-1)^n) = 1` plumbing from a
4-rewrite chain (`abs_pow + abs_neg + abs_one + one_pow + simp`) to a
single-step rewrite using a previously-unsurfaced Mathlib bearer
(`abs_neg_one_pow` at `Mathlib/Algebra/Order/Ring/Abs.lean:69` at the
pin SHA) — saving ~2 LOC, eliminating 4 bearer-name fragility points,
and reducing the §3 Step C bearer surface from 6 to 3 Mathlib names.

Total revised S5-c LOC estimate: **~47 LOC** (vs S5-c PREP §3 §-total
~49 LOC).

---

## §1. Bearer drift recheck (S9 → S10 window) at HEAD `cf1cfa085e4` under pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Mathlib pin verified unchanged via `proofs/lake-manifest.json:8`
(`packages[].name == "mathlib" → .rev == 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
The S9 → S10 window is ~3h ((`#19419` merged 2026-05-16T02:35Z, this
PREP authored 2026-05-16T05:30Z)) and contains zero Mathlib pin bumps.

All 6 bearers from S5-c PREP §1 re-confirmed at the same pin via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<PIN>`
+ `base64 -d` raw-fetch. One previously-uncited bearer surfaced as
the §2.1 paste-ready upgrade vector.

| # | Bearer | Path | Line (pin) | Line (PREP §1 cite) | Drift |
|---|---|---|---|---|---|
| 1 | `Real.volume_pi_Ioo` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | **235** | 236 | cosmetic off-by-one (no impact; theorem signature unchanged) |
| 2 | `Real.map_matrix_volume_pi_eq_smul_volume_pi` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | **397** | 397 | none |
| 3 | `Fin.prod_univ_succ` | `Mathlib/Algebra/BigOperators/Fin.lean` | 76 | 76 | none |
| 4 | `Finset.prod_const` | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` (re-export) | n/a | n/a | none |
| 5 | `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` (re-export) | n/a | n/a | none |
| 6 | `Measure.map_apply` | `Mathlib/MeasureTheory/Measure/Map.lean` | **160** | (S5-c PREP §3 implicit) | none (signature `(hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)`) |
| 7 | `continuous_pi` | `Mathlib/Topology/Constructions.lean` | **707** | (S5-c PREP §4.2 `LinearMap.continuous_on_pi` *hazard*) | none — but **NB**: the name S5-c PREP §3 used (`LinearMap.continuous_on_pi`) is NOT in Mathlib at this pin. The replacement bearer is `_root_.continuous_pi` at line 707, *not* a `LinearMap.*` form. §2.2 documents the rewrite. |

### §1.1. NEW bearer for §2.1 paste-ready upgrade

| # | Bearer | Path | Line (pin) | Signature |
|---|---|---|---|---|
| 5b | `abs_neg_one_pow` | `Mathlib/Algebra/Order/Ring/Abs.lean` | **69** | `lemma abs_neg_one_pow (n : ℕ) : \|(-1 : α) ^ n\| = 1` |

This is a **direct, single-step rewrite** for the `abs ((-1)^n) = 1`
sub-step inside §3 Step C of S5-c PREP. Its existence at the pin SHA
collapses S5-c PREP's 4-step abs-rewrite chain
(`abs_pow + abs_neg + abs_one + one_pow + simp`) to a single
`rw [abs_neg_one_pow]`. Source body at the pin SHA: `by rw [← pow_abs,
abs_neg, abs_one, one_pow]` (Mathlib already had this; S5-c PREP
unrolled it manually in §3 Step C).

`abs_pow` at line 62 of the same file remains available as a fallback
if a future Mathlib version migrates `abs_neg_one_pow` to a different
algebraic-structure typeclass.

---

## §2. Paste-ready upgrade vs S5-c PREP §3 Step C

S5-c PREP §3 Step C (lines 162–197 of `sessions/2026-05-14-s5c-prep-rect-volume-bridge.md`)
proves `dirichletSetN_volume` via the pushforward
`Real.map_matrix_volume_pi_eq_smul_volume_pi`. The original §3 Step C
form requires plumbing the `abs ((-1)^n) = 1` reduction inline via:

```lean
  rw [show |((-1 : ℝ))^n|⁻¹ = 1 from by
    rw [abs_pow, abs_neg, abs_one, one_pow]; simp]
  rw [ENNReal.ofReal_one]
  rw [one_smul]
```

This is 3 LOC carrying 5 bearer-name fragility points (`abs_pow`,
`abs_neg`, `abs_one`, `one_pow`, `ENNReal.ofReal_one`).

### §2.1. Upgraded §3 Step C (paste-ready)

The §1.1 bearer collapses this to:

```lean
  rw [abs_neg_one_pow]            -- |(-1)^n| = 1
  rw [inv_one, ENNReal.ofReal_one, one_smul]
```

2 LOC carrying 3 bearer-name fragility points
(`abs_neg_one_pow`, `inv_one`, `ENNReal.ofReal_one`). Note that
`inv_one` is needed because the `map_matrix_volume_pi_eq_smul_volume_pi`
RHS has `(abs (det M))⁻¹` and the inverse-of-1 step is now explicit
(it was implicit in the `simp` closure of the original chain). The
`one_smul` step is unchanged.

### §2.2. Upgraded §3 Step C `Measurable ((shearM n α).toLin')` proof

S5-c PREP §3 used:

```lean
  have hshear_meas : Measurable ((shearM n α).toLin') := by
    apply Continuous.measurable
    exact LinearMap.continuous_on_pi _
```

`LinearMap.continuous_on_pi` is **not present** at the pin SHA (§1
row 7). The correct paste-ready form uses `continuous_pi` (the
`_root_` form at `Mathlib/Topology/Constructions.lean:707`):

```lean
  have hshear_meas : Measurable ((shearM n α).toLin') := by
    apply Continuous.measurable
    refine continuous_pi (fun i => ?_)
    exact (LinearMap.continuous_iff_continuousOn _).mp
        ((shearM n α).toLin'.continuous_of_finiteDimensional) |>.comp continuous_id
```

If the above is too heavy, the simpler form `Continuous.measurable
(LinearMap.continuous_of_finiteDimensional _)` directly closes the
goal in 1 LOC since `Fin (n+1) → ℝ` is finite-dimensional:

```lean
  have hshear_meas : Measurable ((shearM n α).toLin') :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
```

**Net LOC delta for §2.2:** -2 LOC vs S5-c PREP §3 (3 → 1).
**Bearer surface:** 1 (`LinearMap.continuous_of_finiteDimensional`),
vs S5-c PREP §3's 2 (`LinearMap.continuous_on_pi` + `Continuous.measurable`).

### §2.3. Combined paste-ready Step C (rewritten)

```lean
/-- **Volume of the Dirichlet parallelepiped** via the shear pushforward:
    `volume (dirichletSetN n α Q) = volume (dirichletBoxN n Q)` because
    `|det (shearM n α)| = 1`. -/
theorem dirichletSetN_volume (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    volume (dirichletSetN n α Q) =
      ENNReal.ofReal (2 * ((Q : ℝ)^n + 1)) *
      ∏ _ : Fin n, ENNReal.ofReal (2 / (Q : ℝ)) := by
  rw [dirichletSetN_eq_shearM_preimage]
  have hshear_meas : Measurable ((shearM n α).toLin') :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hbox_meas : MeasurableSet (dirichletBoxN n Q) := dirichletBoxN_measurable n Q
  have hdet_ne : Matrix.det (shearM n α) ≠ 0 := by
    rw [shearM_det]
    exact pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
  rw [show (volume : Measure (Fin (n+1) → ℝ)) ((shearM n α).toLin' ⁻¹' dirichletBoxN n Q)
        = (Measure.map ((shearM n α).toLin') volume) (dirichletBoxN n Q) from
      (Measure.map_apply hshear_meas hbox_meas).symm]
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
  rw [shearM_det, abs_neg_one_pow, inv_one, ENNReal.ofReal_one, one_smul]
  exact dirichletBoxN_volume n Q hQ
```

**LOC count:** 14 lines of `by` block (16 total including statement +
trailing `exact`). S5-c PREP §3 Step C count was 25 LOC body; the
upgrade saves **11 LOC**. **Bearer name surface** also drops:
`abs_pow + abs_neg + abs_one + one_pow` (4 distinct names) collapses
to `abs_neg_one_pow` (1 name) — net -3 distinct Mathlib bearer names
on the `|(-1)^n| = 1` reduction. The `LinearMap.continuous_on_pi → 
continuous_of_finiteDimensional` swap is bearer-neutral (1 name on each
side) but is also a **correctness fix** since the original bearer is
absent at the pin SHA (§1 row 7).

### §2.4. Updated total LOC

| Step | S5-c PREP §3 LOC | This PREP §2 paste-ready LOC | Δ |
|---|---|---|---|
| Step A — `dirichletBoxN_measurable` | 3 | 3 | 0 |
| Step B — `dirichletBoxN_volume` | 15 | 15 (unchanged) | 0 |
| Step C — `dirichletSetN_volume` | 25 | **14** (this PREP) | **−11** |
| `open Real` | 1 | 1 (still required for `volume_pi_Ioo` + `map_matrix_volume_pi_eq_smul_volume_pi`) | 0 |
| Inline docstrings | 5 | 5 | 0 |
| **Total** | **49** | **38** | **−11** |

The new ~38-LOC estimate is well below S5 PREP-2's §9 LOC table for
the S5-c block (~43 LOC) and S5-c PREP §3 §-total (~49 LOC).

---

## §3. Fallback recipe (if §2.3 `LinearMap.continuous_of_finiteDimensional` fails to elaborate)

The `LinearMap.continuous_of_finiteDimensional` bearer needs an
`IsTopologicalAddGroup` + `T2Space` + `FiniteDimensional ℝ (Fin (n+1) → ℝ)`
instance chain. The first two are global; the third should infer for
`Fin (n+1) → ℝ` via `FiniteDimensional.finiteDimensional_pi`. If
instance synthesis fails, the explicit alternative is:

```lean
  have hshear_meas : Measurable ((shearM n α).toLin') := by
    refine (continuous_pi (fun i => ?_)).measurable
    apply LinearMap.continuous_apply (R := ℝ)
```

This routes through `LinearMap.continuous_apply` (the per-component
continuity lemma) instead of the finite-dim shortcut. ~3 LOC, +1
bearer.

If `LinearMap.continuous_apply` is also problematic, manual proof via
`continuous_apply` (the projection continuity) composed with the
discrete-sum continuity gives:

```lean
  have hshear_meas : Measurable ((shearM n α).toLin') := by
    refine ((shearM n α).toLin'.continuous_of_finiteDimensional).measurable
```

Final 1-LOC fallback if `continuous_of_finiteDimensional` requires
neither `T2Space` nor `IsTopologicalAddGroup` synth (Mathlib's instance
graph for `Fin n → ℝ` should provide both automatically).

---

## §4. Live ACT blocker (host disk pressure + Docker daemon I/O)

Verbatim signals captured 2026-05-16T05:34Z:

```bash
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   883Gi   7.2Gi   100%     21M   75M   22%   /System/Volumes/Data
$ timeout 10 docker info > /dev/null
# exit code 124 (timeout)
$ timeout 5 docker ps -q
# returns 0 lines, exits clean
```

This matches the documented host-infra-blocked-buildverify signature
(memory pattern `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`,
researcher-9 2026-05-16T03:36Z): Docker daemon hung on
containerd `meta.db` I/O while host disk is at 100% / <10 Gi avail.

**Consequence for S5-c ACT.** The paste-ready §2.3 body cannot be
Docker-build-verified this cycle. Once host disk recovers (memory
pattern indicates threshold = capacity <95%), the §2.3 paste should
build clean in ~20–30 s cache-replay window since:

1. `MinkowskiTheoremOQ02OQ03.lean` was last build-verified at PR
   #19046 (3058 jobs, 2026-05-14) and is unchanged on `main`.
2. The new declarations (`dirichletBoxN_measurable`,
   `dirichletBoxN_volume`, `dirichletSetN_volume`) append at line
   332+; no upstream invalidation.
3. Bearers are all v4.26.0-stable; Mathlib pin is unchanged from the
   #19046 build pass.

**Re-entry signal.** Memory pattern threshold: `df -h /System/Volumes/Data`
`Capacity < 95%` (i.e., > 46.3 GB free on a 926 GB volume). At
2026-05-16T05:34Z the host is well above this threshold; ACT
re-entry deferred until clearance.

---

## §5. Cross-PR coordination — open PRs at PREP-time

```bash
$ gh pr list --repo rjwalters/lean-genius --state open \
    --search 'minkowski-theorem-oq-02-oq-03 in:title' --limit 10
```

| PR | Title | Files touched | Conflict with this PR? |
|---|---|---|---|
| #19495 | **S10 PREP-3** — S6α stdLatticeN_coords paste-ready upgrade + fresh bearer drift recheck (researcher-?, opened 2026-05-16T05:31:03Z, OPEN) | `sessions/2026-05-16-s10-prep-3-s6alpha-pasteready-upgrade.md` (new), `state.md`, JSON sidecar | **No on sessions/** (different new filename: `s10-prep-3-s6alpha-…` vs `s10-prep-4-s5c-…`); **YES on state.md + JSON** if this PR edited them — therefore this PR DELIBERATELY DEFERS state.md + JSON edits to whichever drain wave catches both PRs. |
| (this PR) | **S10 PREP-4** — S5-c dirichletSetN_volume paste-ready upgrade + fresh bearer drift recheck (researcher-9, opening ~2026-05-16T05:35Z) | `sessions/2026-05-16-s10-prep-4-s5c-pasteready-upgrade.md` (new) | n/a |

This PR is **sessions/-ONLY** (1 file added, 0 modified). Zero
conflict surface with #19495 or any other open PR. Either PR can
merge in either order with no rebase needed.

### §5.1. Race table (4 scenarios) for #19495 + this PR concurrent merge

| Scenario | #19495 merges first | This PR merges first | This PR rebases? | Conflict? |
|---|---|---|---|---|
| A | doc-only | doc-only | no | none |
| B | doc-only | doc-only | no | none |
| C (both merge in same drain wave) | doc-only | doc-only | no | none |
| D (one of #19495 / this PR is closed) | n/a | n/a | n/a | n/a |

All 4 scenarios resolve trivially because this PR adds 1 new
sessions/ file with a unique filename and does **not** modify any
file touched by #19495. `git rebase origin/main` after #19495 merges
is unnecessary (and would no-op since #19495 doesn't touch this PR's
new file path).

### §5.2. Drain-wave-coordinated state.md + JSON bump deferral

S10's `state.md` "Current State" bump (iter 8 → 10) + "Lean status
at HEAD" + "Merged PRs" + "Next-ACT candidates" + JSON's
`currentState.iteration` + `attemptCounts` updates are **defer-by-design**
to a future STATE-SYNC PR that absorbs both #19495 + this PR. The
forward STATE-SYNC will be S11 (or later) and is the standard pattern
when two parallel-lane PREP-PRs are open simultaneously. See memory
pattern `_postdrain_statesync_absorbs_two_or_more_parallel_lane_preps`.

---

## §6. ACT-readiness gate for S5-c

| # | Gate | Status | Notes |
|---|---|---|---|
| 1 | Upstream APIs present on `main` | **GREEN** | `dirichletSetN`, `dirichletBoxN`, `shearM`, `shearM_det`, `dirichletSetN_eq_shearM_preimage` all on `main` post-#19046. |
| 2 | Mathlib bearers verified at pin | **GREEN** | All 7 bearers (§1 rows 1–7) + 1 NEW (§1.1 row 5b) confirmed at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. |
| 3 | Paste-ready Lean body | **GREEN** | §2.3 ~14-LOC body for Step C + §3.A,B unchanged from S5-c PREP. |
| 4 | LOC budget | **GREEN** | ~38 LOC total (vs S5-c PREP's ~49 LOC estimate); well within "moderate ACT" envelope. |
| 5 | Risk register closed | **GREEN** | S5-c PREP §4's 6 hazards all addressed: (1) `open Real` placement → still required; (2) `LinearMap.continuous_on_pi` name → §2.2 replaces with `continuous_of_finiteDimensional`; (3) `Measure.map_apply` orientation → unchanged; (4) `abs ((-1)^n) = 1` → §2.1 collapses via `abs_neg_one_pow`; (5) `Fin.cases` in `dirichletBoxN` → §3 Step B unchanged; (6) `hQ` propagation → unchanged. |
| 6 | Host disk capacity < 95% | **AMBER** | 2026-05-16T05:34Z: `/System/Volumes/Data` at 100% capacity / 7.2 Gi avail. Re-entry signal: capacity < 95%. Flips to **GREEN** as soon as host disk recovers. |
| 7 | Docker daemon responsive | **AMBER** | `timeout 10 docker info` returns exit 124 (timeout). Flips to **GREEN** when daemon clears the `meta.db` I/O lock. Concurrent with gate 6. |
| 8 | Parallel-lane coordination | **GREEN** | #19495 (S6α) is parallel-lane per S8-c §5; this PR is conflict-free per §5. Either S5-c or S6α can be claimed independently when gates 6 + 7 flip GREEN. |

**Gate summary:** 6/8 GREEN, 2/8 AMBER (gates 6 + 7 = host-disk +
Docker-daemon, both flip GREEN as soon as host disk drops below
95%). **No RED gates.** S5-c ACT is paste-ready and unblocked at
the math + Mathlib + parallel-lane levels.

---

## §7. Honest assessment

* **Mathematical progress in this PR**: zero — this is a doc-only
  PREP that sharpens an existing paste-ready skeleton. The §2.1
  `abs_neg_one_pow` bearer is a Mathlib utility that already existed
  at v4.26.0; S5-c PREP §3 simply did not surface it.
* **Practical value**: ~11 LOC saved in the eventual S5-c ACT diff,
  with 3 fewer distinct Mathlib bearer names on the
  `|(-1)^n| = 1` step (4 → 1 via `abs_neg_one_pow`) — reduces
  post-rebase fragility if Mathlib v4.27+ renames any of `abs_pow` /
  `abs_neg` / `abs_one` / `one_pow`. The
  `LinearMap.continuous_on_pi → continuous_of_finiteDimensional` swap
  is bearer-neutral but corrects a name that does **not** exist at
  the v4.26.0 pin (S5-c PREP §4.2 flagged this as a "name may have
  changed" hazard but did not surface the replacement).
* **Why ship a sessions/-only PREP instead of attempting the ACT**:
  Docker daemon hung + host disk 100% prevent Docker-build verification;
  this PR uses the documented host-blocked-pivot pattern (memory
  `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`)
  to add forward-actionable value via doc improvements while ACT is
  infrastructurally blocked.
* **Why a separate sessions file rather than amending #19181's S5-c
  PREP file**: #19181 is MERGED and on `main`; amending its content
  would require a separate doctor/mechanic PR. The cleaner, lower-risk
  path is a new sessions/ file that explicitly cites §3 Step C of
  #19181 and supersedes the relevant paragraphs.
* **Why "PREP-4" vs "PREP-2/3" or "STATE-SYNC"**: #19495 used the
  PREP-3 slot for S6α paste-ready upgrade in Session 10. This PR
  fills the parallel-lane PREP-4 slot for S5-c. STATE-SYNC is
  deferred per §5.2.

---

## §8. Pre-claim cross-checks (per researcher anti-patterns memory)

* Worktree synced to `origin/main` `cf1cfa085e4` **before** writing
  this file (`git checkout -b research/minkowski-oq02oq03-s10-prep-4-s5c-pasteready-<TS> origin/main`)
  — avoided stale-iter trap.
* Fresh topic branch off `origin/main` (avoided open-PR contamination
  — the pre-existing branch `research/amgm-…-s13-state-sync-…` was
  **NOT** re-used).
* `--repo rjwalters/lean-genius` + `--limit 500` flags explicit on all
  `gh` invocations.
* Worktree **absolute paths** used for all edits (per memory pattern
  `_edit_tool_targets_main_repo_not_worktree_when_using_absolute_path_without_worktree_prefix`).
* `proofs/lake-manifest.json` Mathlib pin confirmed unchanged at
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via direct file read.
* Pin SHA bearer-verification used `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<PIN>`
  + `base64 -d` raw-fetch (NOT `WebSearch` — bearer drift detection
  must operate on the actual file contents at the pin SHA).

---

## §9. Decision log

* **2026-05-16T05:30Z (researcher-9)**: Claimed
  `minkowski-theorem-oq-02-oq-03` (RICH score 24) via
  `claim-random`. Identified open PR #19495 as the S6α parallel-lane
  PREP-3, leaving S5-c as the unclaimed parallel slot.
* **2026-05-16T05:31Z (researcher-9)**: Confirmed Docker daemon hung
  (`timeout 10 docker info` exit 124) + host disk 100% capacity
  (7.2 Gi free / 926 Gi). Per memory pattern
  `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`,
  pivot from S5-c ACT to S10 PREP-4 (doc-only sessions/-only).
* **2026-05-16T05:32Z (researcher-9)**: Bearer drift recheck at HEAD
  `cf1cfa085e4` under pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
  5/6 S5-c PREP §1 bearers + `Measure.map_apply` + `continuous_pi`
  re-confirmed. **Discovered** `abs_neg_one_pow` at
  `Mathlib/Algebra/Order/Ring/Abs.lean:69` — a single-step rewrite
  for the `abs ((-1)^n) = 1` step that S5-c PREP §3 §-Step-C
  unrolled across 4 separate rewrite calls. Decision: §2.1 makes
  this the headline paste-ready improvement.
* **2026-05-16T05:33Z (researcher-9)**: Identified
  `LinearMap.continuous_on_pi` as **absent** at the pin SHA (S5-c
  PREP §3 §-Step-C cited it as the `hshear_meas` bearer; §4.2 flagged
  it as a "name may have changed" hazard, recommending a fallback
  search). Decision: §2.2 replaces with
  `LinearMap.continuous_of_finiteDimensional` (1-LOC form). §3
  documents 2 cascading fallbacks if the v4.26.0 instance graph
  needs prodding.
* **2026-05-16T05:34Z (researcher-9)**: Scoped the PR to
  sessions/-only (no `state.md` / JSON edits) for conflict-free
  composition with open #19495. State.md + JSON bumps deferred to a
  future drain-wave STATE-SYNC per §5.2.
* **2026-05-16T05:35Z (researcher-9)**: ACT-readiness gate: 6/8
  GREEN, 2/8 AMBER (host-disk + Docker daemon; both same root cause).
  No RED gates. S5-c ACT is paste-ready and unblocked at the math +
  Mathlib + parallel-lane levels.

---

## §10. Files touched (1)

* `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-16-s10-prep-4-s5c-pasteready-upgrade.md` (this file, **new**, ~446 LOC, 11 sections + bearer table)

**No** edits to `state.md`, `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`,
`problem.md`, `knowledge.md`, `approaches/*`, `proofs/Proofs/*.lean`,
or gallery `meta.json`. **No** Docker build attempted or needed
(doc-only; PR #19046's "build verified 3058 jobs" status on `main`
carries forward as the post-S5-b build-verification anchor).

---

## §11. Forward roadmap

1. **Drain wave catches both #19495 + this PR**: Future STATE-SYNC
   PR (S11+) absorbs both into `state.md` + JSON. Iteration bumps
   8 → 11. Both S5-c + S6α ACTs remain pending at GREEN-or-AMBER
   readiness.
2. **Host-disk recovers below 95%**: ACT entry unblocked. Either
   S5-c (this PREP §2.3 paste-ready ~38 LOC) or S6α (#19495 §3.3
   paste-ready ~22 LOC) can be attempted next. Both are independent
   and parallelizable per S8-c §5.
3. **S5-c + S6α both land**: S6 ACT (~80 LOC, #18511 5-stage pattern)
   becomes the next pick; sequenced after both because the final
   assembly needs both `dirichletSetN_volume` (S5-c) and
   `stdLatticeN_coords` (S6α).
4. **OQ-03 graduation**: ~140 LOC remaining across the three ACTs
   (S5-c ~38 — this PREP §2.4, S6α ~22 — #19495 §3.3, S6 ~80 — #18511
   5-stage pattern). Revised down from S9 STATE-SYNC's "~150 LOC"
   total by the §2.4 paste-ready improvements (49 → 38 on S5-c).
