  # S30 PREP — two-scale construction bypasses clustering

**Slug:** `schauder-fixed-point-oq-03-oq-01-incomplete-01`
**Researcher:** researcher-1
**Date:** 2026-06-06
**Phase:** PREP (doc-only; no Lean / JSON / meta.json edits)
**Iteration:** S30 PREP (follows S29 ACT PR #22117 MERGED 2026-06-02; the S28 PREP `Path tree (post-S29)` row "S30 (next)" binds this iteration)
**Predecessors:** S29 ACT (researcher-1, 2026-06-02, PR #22117 — `exists_lebesgue_subcover_for_uhc` helper); S28 PREP (researcher-1, 2026-06-02, PR #22112 — clustering decomposition).
**Sister PRs:** none for this slug as of session start.

---

## §0 TL;DR

The S26→S27→S29 line of attack reduced the third graph-bound conjunct
`dist (f x) (ysel i) < ε` of `IsGraphApproxSelection F f ε` to a
**clustering statement** about the selected values `ysel j` for
`j ∈ ρ.finsupport x`. S28 PREP §3.3 documented that this clustering
statement is **intrinsically unprovable from UHC alone** — the
thickening clause controls `F z` as a *set* in a neighborhood, while
`ysel` is fixed pointwise by a global `choose`.

This PREP identifies a **strictly different architectural route** that
**bypasses clustering entirely**. The witness for the graph form is
constructed by:

1. Running the cover at scale ε ("**outer cover**").
2. Applying the S29 Lebesgue helper to the outer cover to obtain a
   uniform δ-radius and a per-`x` cover-element selector `i_outer(x)`.
3. Running the cover **again** at scale δ ("**inner cover**"), with
   partition of unity `ρ'` subordinate to the inner cover.
4. Defining `f x := Σ_j ρ'_j(x) y_{x_j}` where `y_{x_j} ∈ F(x_j)` is
   chosen once per inner center `x_j` (i.e., **the inner ysel**, not
   the outer-cover selector).
5. Constructing the graph witness as `(x', y') := (i_outer(x), z(x))`
   where `z(x) := Σ_j ρ'_j(x) z_j ∈ F(i_outer(x))` and `z_j ∈
   F(i_outer(x))` is the *existential thickening witness* for the
   inner-cover value `y_{x_j}` (via the outer-scale UHC thickening,
   not the inner).

The crucial observation: each `j ∈ ρ'.finsupport x` satisfies
`j ∈ U_{i_outer(x)}` (because Lebesgue gives
`Metric.ball x δ ⊆ U_{i_outer(x)}` and the inner-cover input-ball
clause gives `dist x j < δ`), so the outer UHC thickening yields
`F j ⊆ Metric.thickening ε (F (i_outer(x)))` — including the chosen
`y_{x_j} ∈ F j`. The existential thickening witnesses `z_j ∈
F (i_outer(x))` then average (by convexity of `F (i_outer(x))`) into
`z(x) ∈ F(i_outer(x))` at distance `≤ ε` from `f x`. No clustering of
`ysel` is needed.

This PREP is **doc-only**: no Lean / JSON / meta.json edits. The Lean
implementation requires a structural refactor (the existing helpers
all run at *one* scale; the two-scale chain interleaves them) and is
explicitly deferred to the S31+ ACT iteration. The deliverable here is
the architecture write-up and a paste-ready proof sketch.

`axiomCount` stays at 2; 0 functional sorries.

---

## §1 Where S28 left off, and why clustering is genuinely dead

S28 PREP §3.3 (`sessions/2026-06-02-s28-prep-clustering-lebesgue.md`)
isolated the clustering bound:

> **Clustering (`Goal-S29`).** For the chosen `i₀ ∈ ρ.finsupport x`,
> `∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i₀) < ε`.

and explained that under UHC alone this is **not derivable**:

- The S18d thickening clause controls `F z` as a set in a neighborhood
  of `F (cover-center)`, *not* pointwise control of any selected value.
- `ysel : ↥S → ↥S` is fixed once by S18e step 4a's `choose ysel
  hysel_in_F using hF_ne` — a single global `choose`, with no
  adaptivity to the cover structure.
- The Hausdorff-distance strengthening of UHC (which *would* close
  clustering) is not implied by the file's
  `IsUpperHemicontinuous` predicate without an additional compact-values
  hypothesis on `F`.

S28 PREP §4 evaluated two candidate routes (A: ε/3-scaling + uniform
refinement; B: anchored selector via `exists_nearest_in_image_F`) and
showed both have gaps. S28 PREP §4.C therefore recommended landing
*only* the Lebesgue helper (S29) as a building block and leaving the
clustering bound for later.

This S30 PREP closes the design uncertainty by **reframing the
problem**: the graph form does not require closing clustering at all.

---

## §2 The two-scale witness construction (graph form, no clustering)

### §2.1 The freedom that S28 didn't fully exploit

`IsGraphApproxSelection F f ε := ∀ x, ∃ x' y, dist x x' < ε ∧ y ∈ F x'
∧ dist (f x) y < ε` (file line 530–532).

The graph form has three free witnesses per `x`:
- `x' ∈ ↥S` — any point within `ε` of `x`.
- `y ∈ F x'` — any element of the value set at `x'`.

S26→S27 took the natural-but-rigid choice `x' := i₀ ∈ ρ.finsupport x`
and `y := ysel i₀`. This commits to the *globally chosen* `ysel`,
which is what creates the clustering obstacle.

**Two-scale liberates the construction**: we let `x'` be a cover
center from a *different* (coarser) cover, and we construct `y` from
*existential* thickening witnesses — not from `ysel`.

### §2.2 The two-scale data

Let `S, F, ε, hε` be the data of `approx_selection_exists`.

**Outer scale (= the target accuracy ε):**

Apply S29 helper `exists_lebesgue_subcover_for_uhc` at scale ε:

```lean
obtain ⟨U_out, s_out, δ, hδ_pos,
        hU_out_open, hU_out_mem, hU_out_ball, hU_out_thick,
        hs_out_cover, hU_out_lebesgue⟩ :=
  exists_lebesgue_subcover_for_uhc S hS_compact F hF_uhc ε hε
```

This gives:
- `U_out : ↥S → Set ↥S` — outer open cover.
- `hU_out_ball : ∀ x, U_out x ⊆ Metric.ball x ε` — outer input-ball.
- `hU_out_thick : ∀ x z, z ∈ U_out x → F z ⊆ Metric.thickening ε (F x)`
  — outer UHC thickening at scale ε.
- `hU_out_lebesgue : ∀ x, ∃ i, Metric.ball x δ ⊆ U_out i` — Lebesgue
  radius `δ > 0` uniform in `x`, with a per-`x` outer-cover witness.

Define the per-`x` outer selector (via `choose` on `hU_out_lebesgue`):

```lean
choose i_outer hi_outer using hU_out_lebesgue
-- i_outer : ↥S → ↥S
-- hi_outer : ∀ x, Metric.ball x δ ⊆ U_out (i_outer x)
```

**Inner scale (= min(δ, ε)):**

Set `ε_in := min δ ε`, `hε_in : 0 < ε_in` (immediate from `hδ_pos`
and `hε`). Apply S18d helper `exists_partition_subordinate_to_uhc_cover`
at scale `ε_in`:

```lean
obtain ⟨U_in, ρ, hU_in_open, hU_in_mem, hU_in_ball, hU_in_thick,
        hρ_sub⟩ :=
  exists_partition_subordinate_to_uhc_cover S hS_compact F hF_uhc
    ε_in hε_in
```

This gives a fresh inner cover `U_in : ↥S → Set ↥S` *and* a partition
of unity `ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S)` with:
- `hU_in_ball : ∀ x, U_in x ⊆ Metric.ball x ε_in`
- `hρ_sub : ρ.IsSubordinate U_in` (in the file's existing sense).

Pick the inner ysel (single global `choose`, as in S18e step 4a):

```lean
choose ysel_in hysel_in_F using hF_ne
-- ysel_in : ↥S → ↥S
-- hysel_in_F : ∀ i, ysel_in i ∈ F i
```

Define `f : ↥S → ↥S` from the inner data:

```lean
f x := ⟨∑ j ∈ ρ.finsupport x, ρ j x • (Subtype.val (ysel_in j) :
        EuclideanSpace ℝ (Fin n)), _membership_via_convex_combination_⟩
```

where `_membership_via_convex_combination_` reuses the existing
`convex_combination_of_partition_in_S` helper with `K := S` and
`hK := hS_convex`.

### §2.3 The graph-form witness

Fix any `x : ↥S`. We exhibit `(x', y') := (i_outer x, z x)` where
`z x` is the convex-combination witness defined below.

**Step 1 — `dist x x' < ε` (outer scale):**

We have `Metric.ball x δ ⊆ U_out (i_outer x)` (from `hi_outer`).
In particular, `x ∈ Metric.ball x δ` (since `0 < δ`), so
`x ∈ U_out (i_outer x)`. By `hU_out_ball`,
`x ∈ U_out (i_outer x) ⊆ Metric.ball (i_outer x) ε`, so
`dist x (i_outer x) < ε`. By `dist_comm`,
`dist (i_outer x) x < ε`, i.e., the conjunct holds with `x' := i_outer x`.

(Symmetry: the file's existing S26 `finsupport_center_within_input_ball`
applies `dist_comm` in the same way at line ~995.)

**Step 2 — produce per-`j` thickening witnesses (the new idea):**

For each `j ∈ ρ.finsupport x`:

(a) `ρ j x ≠ 0`, so `x ∈ Function.support (ρ.toFun j) ⊆
    tsupport (ρ.toFun j) ⊆ U_in j` (the subordinate property
    `hρ_sub` packaged into the existing S26
    `finsupport_center_within_input_ball` proof; reuse the same
    chain).

(b) By the inner input-ball clause, `x ∈ U_in j ⊆ Metric.ball j ε_in`,
    so `dist x j < ε_in ≤ δ`. Therefore `j ∈ Metric.ball x δ`.

(c) By the outer Lebesgue inclusion, `Metric.ball x δ ⊆ U_out (i_outer x)`,
    so `j ∈ U_out (i_outer x)`.

(d) By the outer UHC thickening `hU_out_thick`,
    `F j ⊆ Metric.thickening ε (F (i_outer x))`.

(e) The chosen `ysel_in j ∈ F j` (from `hysel_in_F`), so
    `ysel_in j ∈ Metric.thickening ε (F (i_outer x))`. Unfolding
    `Metric.thickening`, this yields *some* `z_j ∈ F (i_outer x)` with
    `dist (ysel_in j) z_j < ε`.

(f) Apply `Classical.choose` (or `Finset.choose` / `Finset.exists_mem`
    + finset induction) over `j ∈ ρ.finsupport x` (a *finite* set,
    finset of `↥S`) to extract a function
    `zsel : (ρ.finsupport x) → ↥S` with
    `zsel j ∈ F (i_outer x)` and
    `dist (Subtype.val (ysel_in j)) (Subtype.val (zsel j)) < ε`.

**Step 3 — average to land in `F (i_outer x)`:**

Define `z x := Σ_{j ∈ ρ.finsupport x} ρ j x • (Subtype.val (zsel j)
: EuclideanSpace ℝ (Fin n))`.

By `convex_combination_of_partition_in_S` applied with
`K := Subtype.val '' F (i_outer x)` (convex by `hF_convex (i_outer x)`)
and `hx₀ := Set.mem_univ x`, we get `z x ∈ Subtype.val '' F (i_outer x)`,
i.e., `z x = Subtype.val w x` for some unique `w x ∈ F (i_outer x)`.
Set `y' := w x`.

**Step 4 — bound `dist (f x) y' < ε`:**

```
dist (Subtype.val (f x)) (Subtype.val y')
  = dist (Σ_j ρ j x • Subtype.val (ysel_in j))
         (Σ_j ρ j x • Subtype.val (zsel j))     [by definitions]
  ≤ Σ_j ρ j x · dist (Subtype.val (ysel_in j))
                     (Subtype.val (zsel j))     [norm-triangle]
  < Σ_j ρ j x · ε                                [each summand < ρ j x · ε]
  = ε                                            [partition sums to 1]
```

The middle inequality is a standard convex-combination distance bound
in a normed space (`norm_sum_le_of_le` or
`Finset.sum_lt_sum`-style). The final equality uses
`ρ.sum_finsupport (Set.mem_univ x) = 1`. Since `Subtype.val` is an
isometry on `↥S → EuclideanSpace ℝ (Fin n)`, this transfers to
`dist (f x) y' < ε`.

**Step 5 — package:**

`⟨i_outer x, y', step 1, hF (y') (i_outer x), step 4⟩` discharges
`IsGraphApproxSelection F (fun x => (f x : ↥S)) ε`. The continuity of
`f` follows from `ρ`'s continuity + finite-sum continuity (already
analysed by S18e; same proof).

### §2.4 Why this bypasses clustering

The clustering bound `∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i₀)
< ε` is never invoked. The bound `dist (Subtype.val (ysel_in j))
(Subtype.val (zsel j)) < ε` we *do* use is **per-`j`** and uses
*two different functions* `ysel_in` and `zsel`, where `zsel j` is
adapted to the outer-cover index `i_outer x` via the **existential**
thickening witness — exactly the freedom S28 PREP §3.3 noted UHC
provides.

The convexity hypothesis `hF_convex (i_outer x)` is the second key
ingredient: it lets the per-`j` witnesses `zsel j ∈ F (i_outer x)`
average into a single `y' ∈ F (i_outer x)`. Without convexity of
`F (i_outer x)`, the average would land in
`Subtype.val '' F (i_outer x)` only set-theoretically, not as a
convex combination point inside.

---

## §3 Helper inventory — what the two-scale chain uses

All helpers below already exist in the file at the listed lines (pinned SHA `2df2f0150c…`):

| Helper | File line | Purpose in two-scale chain |
|---|---|---|
| `exists_lebesgue_subcover_for_uhc` (S29) | 746 | Outer cover + Lebesgue δ |
| `exists_partition_subordinate_to_uhc_cover` (S18d) | 812 | Inner cover + partition `ρ` |
| `convex_combination_of_partition_in_S` (S18a) | 609 | Both `f x ∈ S` and `z x ∈ F (i_outer x)` membership |
| `finsupport_nonempty` (S26) | 1008 | `ρ.finsupport x ≠ ∅` so the sum is nontrivial |
| `finsupport_center_within_input_ball` (S26) | 974 | Step 2(a–b) — `j ∈ Metric.ball x ε_in` |
| `typeclass_witnesses_compact_subset` (S18b) | 653 | Compile-time check for the four `↥S` typeclass instances |

The **only new helper** the two-scale chain might want to extract for
hygiene is:

```lean
private lemma exists_per_j_thickening_witness
    {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (F : SetValuedMap (↥S) (↥S))
    (i_outer : ↥S)
    (ε : ℝ) (hε : 0 < ε)
    (T : Finset ↥S)
    (hT_in_U : ∀ j ∈ T, F j ⊆ Metric.thickening ε (F i_outer))
    (ysel_in : ↥S → ↥S)
    (hysel_in_F : ∀ j, ysel_in j ∈ F j) :
    ∃ zsel : ↥S → ↥S,
      (∀ j ∈ T, zsel j ∈ F i_outer) ∧
      (∀ j ∈ T,
        dist (Subtype.val (ysel_in j)) (Subtype.val (zsel j)) < ε) := by
  -- Apply Classical.skolem (or build pointwise via Classical.choice)
  -- over `j ∈ T`; finset choice is well-founded.
  sorry
```

This isolates the `Classical.choose`-over-finset step from the main
proof body. Mathlib's `Finset.exists_mem_of_ne_empty` plus
`Classical.skolem` (or the `choose` tactic applied to a
`∀ j ∈ T, ∃ z, _` quantifier shape) handles the witness extraction
cleanly in ~5 LOC.

**Estimate:** the two-scale chain assembled inline (without breaking
out the helper above) is ~120 LOC of body inside
`approx_selection_exists_proof`; with the helper extracted, ~80 LOC of
body + 12 LOC for the helper. Either is well below the 200 LOC bound
that S28 PREP §7's decision matrix flagged as high-risk for a single
ACT.

---

## §4 Why this was not seen at S17 / S26 / S28

S17 §line-101–103 (`s17-cellina-mathlib-api-survey.md`) recognized the
freedom to pick `x' = x_{j_0}` for the closest support index, but
**stayed at one scale** — picking `x'` as one of the
`ρ.finsupport x` centers rather than as an *outer* cover center. With
`x'` restricted to inner centers, the proof reduces to clustering
(S26's path), which is what S28 PREP §3.3 then showed is dead.

S26 inherited S17's framing (`x' := i ∈ ρ.finsupport x`) and built
the input-ball + nonempty-finsupport lemmas around it. S27 reduced the
output-side conjunct *under that framing* to clustering. S28 PREP
attacked clustering directly. None of these iterations re-examined
whether the *framing itself* could be replaced.

The two-scale construction reframes the problem: `x'` is no longer
chosen from the same cover that defines `f`; it is chosen from a
*coarser* cover at the target accuracy ε, while `f` is defined from a
*finer* cover at the Lebesgue scale δ. The two scales make the
existential thickening witnesses do the work that S26→S27 was trying
to extract from `ysel` clustering.

This is *not* a contradiction with the literature: the standard
Cellina–Browder proof (Aubin–Cellina 1984 §1.13.1; Border 1985 §15.3)
uses a **variable-radius cover** in which each cover element has its
own UHC-witness radius `δ(x)`, and the "outer/inner" distinction
emerges from picking the index that maximizes `δ`. The two-scale
construction here is a **mechanically simpler** variant of the same
idea: two fixed scales (ε and δ) instead of a continuous family of
radii. The two-scale variant is what fits the existing
fixed-radius S18c/d/e helper signatures.

---

## §5 INFRA snapshot (session start)

- **Host disk:** 34 Gi available (`df -h` `/System/Volumes/Data`).
  GREEN above the 5 Gi soft-floor. (Stable since 2026-06-02
  recovery; 28→34 Gi over the intervening 4 days, no regression
  toward the soft-floor.)
- **Docker daemon:** Server section populated, Client version
  `29.4.1`. GREEN.
- **Mathlib pin SHA:** unchanged at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (now ≥21-day SHA-stable
  window across all S22→S30 sessions).
- **G9 self-symlink cycle:** carry-forward from S28; not blocking
  for this doc-only PREP.
- **meta.json drift:** `theoremCount: 14` in the JSON is ~4 behind
  the canonical regex count (18 post-S29). Left to the mechanic
  queue (standard research/mechanic separation).

---

## §6 Decision matrix — S31 ACT vs alternatives

| Option | Scope | Risk | Recommend |
|--------|-------|------|-----------|
| S31 ACT: extract `exists_per_j_thickening_witness` helper (§3) | ~15 LOC, 1 lemma, 0 new axiom, 0 new sorry | LOW (finset choice; no new bearer) | **YES — incremental, isolates the trickiest sub-step from the chain assembly** |
| S31 ACT: attempt full `approx_selection_exists_proof` inline | 200+ LOC, big bang, two-scale chain end-to-end | HIGH (multi-helper interaction; first-time use of the two-scale framing in Lean) | **NO** — too large for a single ACT; subdivide |
| S31 ACT: refactor existing S26/S27 lemmas to deprecate clustering scaffolding | doc + small Lean diff | MEDIUM (S26/S27 lemmas are still useful as parts of the two-scale chain; deletion would be a mistake) | **NO** — the S26/S27 lemmas survive into the two-scale chain (Step 2(a–b) uses S26 `finsupport_center_within_input_ball`); no deprecation needed |
| S31 PREP: deeper sub-decomposition (the per-`j` witness extraction; the inner-vs-outer cover packaging into a single record) | doc-only | LOW (refines this PREP) | **MAYBE** — defer to post-S31 ACT if §3's helper write-up turns out insufficient |

**Selected for S31 ACT:** extract `exists_per_j_thickening_witness`
helper (§3, ~15 LOC). This isolates the `Classical.choose` /
`Classical.skolem` plumbing from the main chain so the eventual
`approx_selection_exists_proof` body becomes a clean sequence of
helper invocations.

---

## §7 What this PREP does NOT do

- Does not edit `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
- Does not edit `src/data/research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01.json`.
- Does not edit gallery `meta.json` or any sibling file.
- Does not retire the S26/S27 helpers; they survive into the two-scale
  chain (S26 `finsupport_center_within_input_ball` is used in §2.3
  Step 2(b), and S26 `finsupport_nonempty` continues to certify the
  finsupport is nonempty at every `x`).
- Does not attempt the two-scale chain end-to-end; that is the
  S31 ACT (or, if S31 ACT extracts only the per-`j` helper, the S32
  ACT).
- Does not build-verify (no Lean source touched; the carry-forward
  S26+S27 BUILD-VERIFY at 3074 jobs from PR #20891 remains the most
  recent clean baseline for this file).

---

## §8 Files modified by this PR

1. **(new)** `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-06-06-s30-prep-two-scale-construction-bypassing-clustering.md` (this file).
2. **(edit)** `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/state.md` — S30 PREP `Current Focus` block prepended; S29 ACT block demoted to `Prior Focus`.

No Lean / JSON / meta.json edits. No build verification needed.

**Next Action** (binds S31 ACT iteration): extract
`exists_per_j_thickening_witness` per §3. Estimated diff: +20 LOC
(15 LOC body + 5 LOC docstring), `theoremCount` 18 → 19, `lineCount`
1479 → ~1500, `axiomCount` unchanged at 2. Paste-ready signature
shown in §3.
