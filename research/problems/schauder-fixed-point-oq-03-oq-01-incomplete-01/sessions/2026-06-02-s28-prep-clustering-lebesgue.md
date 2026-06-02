# S28 PREP — clustering lemma bearer survey + obstacle decomposition

**Slug:** `schauder-fixed-point-oq-03-oq-01-incomplete-01`
**Researcher:** researcher-1
**Date:** 2026-06-02
**Phase:** PREP (doc-only; no Lean / JSON / meta.json edits beyond `state.md` STATE-SYNC absorption)
**Iteration:** S28 PREP (paired with S28 STATE-SYNC absorbing the merged S26+S27 ACT bundle)
**Predecessors:** S27 ACT (researcher-1, 2026-05-28, PR #20891 — `finsupport_combination_within_output_ball`); S26 ACT (researcher-1, 2026-05-28, same PR #20891 — input-ball clause propagation + `finsupport_center_within_input_ball` + `finsupport_nonempty`).
**Sister PRs:** none for this slug as of session start; mechanic PRs #21515 (lineCount 1284→1420) and #21718 (1420→1419, wc -l canonical) merged 2026-05-31 / 2026-06-01 absorbed the post-PR-#20891 lineCount drift but did not touch theoremCount.

---

## §0 TL;DR

S27 ACT reduced the output-side graph-bound conjunct
`dist (f x) (ysel i) < ε` to a **clustering** statement about the
selected values: for some chosen `i ∈ ρ.finsupport x`,

```
∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i) < ε
```

This PREP:

1. **Locates the Mathlib bearer** for the standard tool to attack
   clustering — `lebesgue_number_lemma_of_metric` —
   at the pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, file
   `Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`, signature
   reproduced in §2 below.

2. **Confirms two adjacent bearers** that fall out of the same Mathlib
   module: `lebesgue_number_lemma_of_metric_sUnion` (same file) and the
   `Mathlib/Topology/UniformSpace/Compact.lean` `lebesgue_number_lemma`
   variant. Either works for the use site; the `_of_metric` variant is
   the canonical one for metric spaces (`↥S` carries the subspace
   metric from `EuclideanSpace ℝ (Fin n)`).

3. **Documents the genuine obstacle** that even with the Lebesgue
   number lemma in hand, the clustering bound is **not** a direct
   corollary of UHC + the existing S18d thickening clause. The S18d
   clause runs `F z ⊆ thickening ε (F i)` for `z ∈ U i`, controlling
   `F x` (or any `F z`) in a neighborhood of `F i` — **not** the
   ambient distance between two *chosen* selector values
   `ysel j ∈ F j` and `ysel i ∈ F i`. The thickening witnesses are
   existential, while `ysel` is fixed once and for all by the global
   `choose` at S18e step 4a.

4. **Documents two candidate routes** (A: ε/3-scaling + uniform
   refinement; B: anchored-selector via S22's `exists_nearest_in_image_F`),
   identifies the subtle gap in each, and concludes that the next ACT
   iteration should not try to close clustering in one cycle but
   instead land the **`lebesgue_number_lemma_of_metric` invocation as
   a separate helper lemma** to isolate the bearer plumbing from the
   harder uniform-thickening step.

5. **Paste-ready Lean signature** for the proposed S28 ACT helper
   `exists_lebesgue_subcover_for_uhc` (§5 below) — analogous to
   S18c's `exists_finite_subcover_for_uhc` but augmented with a
   Lebesgue radius `δ > 0` such that every `δ`-ball in `↥S` lies in
   some `U i`. This is doc-only: no Lean is edited in this PR.

No Lean change, no build, no bearer re-walk beyond the one new bearer
(`lebesgue_number_lemma_of_metric`) confirmed in §2. `axiomCount` stays
at 2 (`brouwer_unit_ball`, `approx_selection_exists`); 0 functional
sorries.

---

## §1 Where S27 left off (anchor)

`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean:996` (post-#20891):

```lean
private lemma finsupport_combination_within_output_ball {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S))
    (x i : ↥S)
    (ysel : ↥S → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : ∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i) ≤ r) :
    dist (∑ j ∈ ρ.finsupport x, ρ j x • ysel j) (ysel i) ≤ r
```

The output-side graph-bound conjunct `dist (f x) (ysel i) < ε` reduces
to discharging the hypothesis `hr` with `r := ε`. The other two
conjuncts of `IsGraphApproxSelection F f ε`
(`SchauderFixedPointOQ03OQ01.lean:532`) are already discharged:

- `dist x x' < ε` (with `x' := i ∈ ρ.finsupport x`) by S26's
  `finsupport_center_within_input_ball` (file line ~960) + S26's
  `finsupport_nonempty` (file line ~940).
- `y' ∈ F x'` (with `y' := ysel i`) by S18e's `hysel_in_F`.

So the **sole remaining obstacle** is:

> **Clustering (`Goal-S29`).** For the chosen `i₀ ∈ ρ.finsupport x`,
> `∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i₀) < ε`.

---

## §2 Mathlib bearer — `lebesgue_number_lemma_of_metric`

Confirmed at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c…/
Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`:

```lean
theorem lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*}
    {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by
  simpa only [ball, UniformSpace.ball, preimage_setOf_eq, dist_comm]
    using uniformity_basis_dist.lebesgue_number_lemma hs hc₁ hc₂
```

Specialization to our context: `α := ↥S`, `s := (Set.univ : Set ↥S)`
(which is compact under `[CompactSpace ↥S]`, recovered from
`isCompact_iff_compactSpace.mp hS_compact` exactly as S18c/d/e
already do at lines 641/744/829), `ι := ↥S`, `c := U`.

Hypotheses become:
- `hs : IsCompact (Set.univ : Set ↥S)` — `isCompact_univ` under
  `[CompactSpace ↥S]`.
- `hc₁ : ∀ i, IsOpen (U i)` — the `hU_open` clause already produced
  by S18c.
- `hc₂ : Set.univ ⊆ ⋃ i, U i` — same one-liner as S18d
  (`exists_partition_subordinate_to_uhc_cover`, file line ~767):
  `intro x _; exact Set.mem_iUnion.mpr ⟨x, hU_mem x⟩`.

Conclusion: `∃ δ > 0, ∀ x : ↥S, ∃ i : ↥S, Metric.ball x δ ⊆ U i`.

**Two adjacent bearers also confirmed** (same file, same SHA):
- `lebesgue_number_lemma_of_metric_sUnion` — variant for `c : Set (Set α)`
  with `s ⊆ ⋃₀ c`. Not needed for our indexed-family setup.
- `lebesgue_number_lemma` (`Mathlib/Topology/UniformSpace/Compact.lean`)
  — uniformity-basis form. Strictly more general; we use the metric
  variant for the cleaner ball syntax.

No new import is required: the file already imports
`Mathlib.Topology.MetricSpace.Basic` (line 35) which transitively
pulls in `MetricSpace/Pseudo/Lemmas.lean` through the standard
metric-space dependency chain.

---

## §3 Why Lebesgue alone is insufficient — the genuine obstacle

The Lebesgue number lemma gives a **uniform input-side radius** `δ`:
any `δ`-ball in `↥S` lies entirely in some single cover element `U i`.
This is genuinely useful — it lets us cluster the *centers* (any
`i, j ∈ ρ.finsupport x` are within distance `O(ε)` once `δ` ≤ ε).
But it does **not** by itself produce the clustering bound

```
dist (ysel j) (ysel i₀) < ε
```

between the **selected values** in `↥S`. Two reasons:

### §3.1 The thickening direction is wrong

The S18d clause `∀ x z, z ∈ U x → F z ⊆ thickening ε (F x)` controls
`F z` *as a set* in a neighborhood of `F x` *as a set*. Concretely,
for `j ∈ ρ.finsupport x` we have `x ∈ U j`, which gives
`F x ⊆ thickening ε (F j)` — i.e., for any `y ∈ F x` there is *some*
`z ∈ F j` with `dist y z < ε`. The bound is **existential in `z`**;
the specific `ysel j` chosen by S18e's `choose ysel` step has no a
priori relationship to that `z`.

### §3.2 `ysel` is fixed globally before the clustering goal

S18e step 4a (`SchauderFixedPointOQ03OQ01.lean:848`):

```lean
choose ysel hysel_in_F using hF_ne
```

This commits a global `ysel : ↥S → ↥S` with `ysel i ∈ F i` for all
`i`. The clustering bound is then a constraint on this *fixed*
function: at every `x`, the values `ysel j` for `j ∈ ρ.finsupport x`
must cluster within `ε` of `ysel i₀` for some `i₀` depending on `x`.
There is no clause in UHC or in the S18c/d cover construction that
forces this. Indeed, `F i` and `F j` can be wildly different convex
sets even when `i, j` are nearby (e.g., `F i = {0, 1}`-style jumps
are excluded by upper hemicontinuity in the Hausdorff-distance sense
but not by the thickening clause alone).

### §3.3 What is genuinely needed

Cellina's original construction (for **lower** hemicontinuous `F`)
provides each cover element with a **fixed reference point**
`y_i ∈ F x_i` such that `F z` hits `B(y_i, ε)` for `z ∈ U_i` — i.e.,
LHC at the chosen point. This forces `ysel j ∈ B(y_j, ε)` (with `ysel`
chosen adaptively per cover element), and a triangle-inequality
argument across overlapping cover elements gives clustering.

For **upper** hemicontinuous `F`, the analogous strengthening is not
available — UHC controls `F z` as a set, not at chosen points. The
Cellina–Browder *graph form* (the one axiomatised here as
`approx_selection_exists`) accepts this by relaxing the conclusion
to the existential graph bound rather than pointwise distance. The
clustering bound is the precise place where this distinction shows
up in the construction. **The S29 ACT iteration cannot close
clustering by `lebesgue_number_lemma_of_metric` alone.**

---

## §4 Two candidate routes for the post-S28 ACT chain

### §4.A Route A — ε/3-scaling + uniform refinement

Run the cover construction at scale `ε' := ε/3` (not `ε`), producing
`U'`, `ρ'`, finite subcover `s'` with all bounds at radius `ε/3`.
Apply Lebesgue at the *outer* scale: ∃ δ > 0 such that every δ-ball
in `↥S` lies in some single `U' i`. Choose any `i ∈ ρ'.finsupport x`
as the reference `i₀`. Then for `j ∈ ρ'.finsupport x`:

- `x ∈ U' j` (subordinate) ⟹ `dist x j < ε/3` (S26 input-ball clause
  at scale ε/3).
- Triangle: `dist i₀ j < 2ε/3`.
- **Gap:** This bounds `dist i₀ j` (in `↥S`), not `dist (ysel j) (ysel i₀)`
  (in `↥S`). To bridge, we need an additional hypothesis or construction
  step. One candidate: use the S18d thickening clause at *both* `i₀`
  and `j`, pick any `y_x ∈ F x`, get `z_{i₀} ∈ F i₀, z_j ∈ F j` each
  within `ε/3` of `y_x`. Then `dist z_{i₀} z_j < 2ε/3`. But `ysel i₀
  ≠ z_{i₀}` and `ysel j ≠ z_j` in general, so this still does not
  bound `dist (ysel i₀) (ysel j)`.

Route A reduces the cleanness gap but does not close it without a
**stronger UHC hypothesis** (e.g., upper hemicontinuity in the
Hausdorff-distance sense, which would let us bound the Hausdorff
distance `d_H (F i, F j) < ε` and hence pull `ysel j ∈ F j` to a
point in `F i` within `ε`).

### §4.B Route B — anchored selector via S22's `exists_nearest_in_image_F`

S22 ACT (PR #19671) landed `exists_nearest_in_image_F` (file line ~928),
a private helper that produces the nearest point in `Subtype.val '' F i`
to any reference `y_0 ∈ EuclideanSpace ℝ (Fin n)`. The idea: define
`ysel` **adaptively per cover element** as

```
ysel i := the nearest point in F i to a fixed reference y_0 ∈ S.
```

Pros: gives `dist (ysel i) y_0 = d(y_0, F i)` (a concrete handle).
Cons: depends on a single global reference `y_0` whose distance to
each `F i` is uncontrolled. Specifically, `dist (ysel i) y_0 = d(y_0, F i)`
can be large if `F i` is far from `y_0`. Triangle then gives
`dist (ysel i) (ysel j) ≤ d(y_0, F i) + d(y_0, F j)`, with no useful
upper bound.

Route B is a dead end unless `y_0` is replaced by **a per-x reference**
`y_0(x)` (e.g., a point in `F x`). But `ysel` cannot depend on `x` (it
must be fixed before `f x` is even defined).

### §4.C Conclusion: defer clustering to S30+, land Lebesgue helper first

Neither route closes clustering in a single iteration. The S29 ACT
deliverable should therefore be the **Lebesgue subcover helper**
(§5 below) as a *standalone lemma*, independent of the clustering
argument. This isolates the bearer plumbing — the same incremental
strategy used by S18c→S18d→S18e and by S19a→S22 — so the harder
uniform-thickening step (S30+) inherits a clean Lebesgue radius from
S29 and a clean S26/S27 reduction of the goal.

---

## §5 Paste-ready S29 ACT signature (helper, doc-only)

Proposed helper to live alongside `exists_finite_subcover_for_uhc`
(`SchauderFixedPointOQ03OQ01.lean:693`):

```lean
/-- **S29 scaffold (Lebesgue number for the UHC cover):**

    Augments `exists_finite_subcover_for_uhc` with a uniform Lebesgue
    radius `δ > 0` such that every `δ`-ball in `↥S` is contained in
    some single cover element `U i`. The pointwise containment
    `Metric.ball x δ ⊆ U (i x)` (for `i x` depending on `x`) is the
    uniform refinement needed to bound distances between centers in
    `ρ.finsupport x` from above by a calibrated multiple of `ε`.

    This lemma does **not** close the output-side clustering bound
    `dist (ysel j) (ysel i) < ε` directly — see
    `sessions/2026-06-02-s28-prep-clustering-lebesgue.md` §3 for the
    underlying obstacle that UHC controls `F z` as a *set* and the
    `ysel` selector is fixed globally before clustering is even posed.
    It is intended as input to a subsequent S30+ uniform-thickening
    step.

    **Proof.** `↥S` is compact (`isCompact_iff_compactSpace.mp
    hS_compact` materialises `[CompactSpace ↥S]`, the same one-line
    construction used by S18c at line 704). The `U` family from
    `exists_finite_subcover_for_uhc` is an open cover of
    `Set.univ : Set ↥S` (`hU_open` + `hU_mem` give `Set.univ ⊆ ⋃ i, U i`
    by the same one-liner as S18d line 767). Apply
    `lebesgue_number_lemma_of_metric`
    (`Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean` at pinned rev
    `2df2f0150c…`) to obtain the uniform `δ > 0` and the per-`x`
    cover-element witness.

    No new axiom is introduced; `axiom approx_selection_exists`
    (Axiom 2 above) remains unchanged. -/
private lemma exists_lebesgue_subcover_for_uhc {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ↥S → Set ↥S, ∃ s : Finset ↥S, ∃ δ : ℝ,
      0 < δ ∧
      (∀ x : ↥S, IsOpen (U x)) ∧
      (∀ x : ↥S, x ∈ U x) ∧
      (∀ x : ↥S, U x ⊆ Metric.ball x ε) ∧
      (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
      (⋃ x ∈ s, U x = (⊤ : Set ↥S)) ∧
      (∀ x : ↥S, ∃ i : ↥S, Metric.ball x δ ⊆ U i) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  -- Step 1: invoke S18c to obtain the open cover with input-ball + thickening
  -- + finite-subcover clauses.
  obtain ⟨U, s, hU_open, hU_mem, hU_ball, hU_sub, hs_cover⟩ :=
    exists_finite_subcover_for_uhc S hS_compact F hF_uhc ε hε
  -- Step 2: derive Set.univ ⊆ ⋃ i, U i (same one-liner as S18d).
  have hU_cover_univ : (Set.univ : Set ↥S) ⊆ ⋃ i : ↥S, U i := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  -- Step 3: apply lebesgue_number_lemma_of_metric to obtain the uniform δ.
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hU_open hU_cover_univ
  -- Step 4: package the Lebesgue witness restricted to ↥S (via mem_univ).
  refine ⟨U, s, δ, hδ_pos, hU_open, hU_mem, hU_ball, hU_sub, hs_cover, ?_⟩
  intro x
  exact hδ x (Set.mem_univ x)
```

Estimated cost: ~30 LOC (24 lines of statement + body shown above plus
~6 lines of docstring header). No new imports. `theoremCount` would
move 17 → 18 (under the canonical regex), `lineCount` would move
1419 → ~1450. `axiomCount` unchanged at 2.

---

## §6 INFRA snapshot (session start)

- **Host disk:** 28 Gi available (`df -h` `/System/Volumes/Data`),
  GREEN at the standing 5 Gi soft-floor. Pin-stable since the
  cycle-31 disk recovery (memory project log
  `project_deployer_2026_06_02_cycle31_3merges_disk_recovery.md`).
- **Docker daemon:** Server section populated, Client version
  `29.4.1`. GREEN (matches state.md S26 ACT note "Docker v29.4.1, disk
  66 Gi"; disk has since rolled to 28 Gi but remains GREEN).
- **G9 self-symlink cycle:** `proofs/.lake` still points to
  `/Users/rwalters/GitHub/lean-genius/proofs/.lake` itself (verified by
  `readlink`). Recurrence of the S6 / S25 STATE-SYNC carry-forward.
  This blocks **local Mathlib browsing** in the worktree but is not a
  blocker for this doc-only PREP (bearer survey via `gh search code`
  + `raw.githubusercontent.com` worked cleanly and confirmed
  `lebesgue_number_lemma_of_metric` at the pinned SHA).
- **Mathlib pin SHA:** unchanged at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (now ≥17-day SHA-stable
  window across all S22→S28 sessions; matches the bearer pin used by
  S22 ACT, S26 ACT, S27 ACT and the seven bearer-rewalks logged in
  memory for sibling researcher-1 problems on 2026-06-02).
- **State.md drift:** Current Focus block was last updated at S26 ACT
  (2026-05-28); the S27 ACT same-day extension landed via PR #20891
  but was not absorbed into the state.md heading. This S28 STATE-SYNC
  pass discharges that drift (see same-PR `state.md` edit).
- **meta.json drift:** `theoremCount: 14` (set by mechanic PR #19983
  2026-05-17 from the regex-canonical S25 baseline). The actual file
  now has 17 entries under the canonical regex (17 = 14 base + 2 from
  S26 + 1 from S27, with 7 public + 10 `private` lemmas). The mechanic
  has not yet auto-synced this drift; not blocking and left to the
  mechanic queue.

---

## §7 Decision matrix — S29 ACT vs alternatives

| Option | Scope | Risk | Recommend |
|--------|-------|------|-----------|
| S29 ACT: land `exists_lebesgue_subcover_for_uhc` (§5) | ~30 LOC, 1 lemma, 0 new axiom, 0 new sorry | LOW (bearer confirmed at pinned SHA, proof body is 4 tactic lines) | **YES** — incremental progress consistent with the S18c→S18d→S18e cadence |
| S29 ACT: attempt full clustering bound | 200+ LOC, multi-helper, requires deciding Route A vs B vs new | HIGH (genuine math gap per §3.3; literature suggests UHC graph form is intrinsically existential) | **NO** — premature; needs a separate PREP pass after §3.3's gap is resolved |
| S29 STATE-SYNC only | doc-only, no Lean | LOW (no progress; S28 STATE-SYNC already discharged the absorption) | **NO** — redundant after this PR |
| S29 PREP further: route C survey (e.g., separable-selection theorem) | doc-only | MEDIUM (might find a cleaner closed-form route) | **MAYBE** — defer to post-S29 ACT, after Lebesgue helper lands |

**Selected:** S29 ACT = land `exists_lebesgue_subcover_for_uhc` per §5.
Single helper, paste-ready, bearer pre-verified, isolated from the
clustering obstacle.

---

## §8 No build, no JSON, no meta.json edits in this PR

This PR's diff is exactly:
1. **(new)** `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-06-02-s28-prep-clustering-lebesgue.md` (this file).
2. **(edit)** `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/state.md` — S28 STATE-SYNC absorption of S27 ACT (S26 ACT subsumed) into Current Focus, demoting S26 ACT to Prior Focus.

No Lean source file is touched. No JSON / meta.json edits. No build
verification needed (carries forward the S27 ACT 3074-job clean build
at the same pinned SHA — Lean file is byte-identical to the post-PR
#20891 state).

**Next Action** (binds S29 ACT iteration): land the helper from §5 in
`SchauderFixedPointOQ03OQ01.lean` between
`exists_finite_subcover_for_uhc` (line 693) and
`exists_partition_subordinate_to_uhc_cover` (line 752). Estimated
diff: +30 LOC, theoremCount 17 → 18, lineCount 1419 → ~1450,
axiomCount unchanged at 2, build-pending qualifier discharged by the
same 3074-job baseline plus the 4-line tactic body.
