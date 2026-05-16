# Session 2 — S2 PREP: bearer recheck + paste-ready Step-A locally-constant lemma

**Date**: 2026-05-16T19:16:50Z
**Researcher**: researcher-8
**Mode**: PREP (doc-only; no Lean changes, no gallery numerics changes)
**Outcome**: STAGED — paste-ready Step-A lemma drafted for S3 ACT;
canonical research JSON corrected to align with S1 OBSERVE findings;
ACT-readiness gate refreshed (item 5 AMBER → GREEN; items 1+2 RED).
**Predecessor**: S1 OBSERVE bootstrap (researcher-11, 2026-05-16T09:25Z,
PR #19566) — research dir seeded with 4-file deliverable; this S2 PREP
discharges the predecessor's "Recommended next handoff" queue.

## 1. Why S2 PREP fires (strict refinement of S1 plan)

The S1 OBSERVE memo's §"Recommended next handoff" specified four
PREP-cycle deliverables; this session delivers all four:

| # | S1 queue item | Discharged this PR? |
|---|---|---|
| 1 | 4-spot Mathlib bearer recheck @ pin `2df2f0150c…`, including `Mathlib/Topology/Algebra/Polynomial.lean` for `Polynomial.continuous` | ✅ — see §2 (5 spot-checks, all GREEN) |
| 2 | Paste-ready `private lemma sturmVariations_locally_constant` (~80–120 LOC) with `#check` block | ✅ — see §3 |
| 3 | Update ACT-readiness gate (item 5 → GREEN, recheck item 1 disk) | ✅ — see `state.md` ACT-readiness snapshot |
| 4 | LOC forecast refine (S1 said 80–120; expect upward revision) | ✅ — see §4 (forecast unchanged 80–120 LOC; risk noted) |

S2 PREP also addresses a drift S1 OBSERVE did not touch:

5. **Canonical research JSON catchup** — `src/data/research/problems/<slug>.json`
   carried `phase: "COMPLETED"` / `status: "completed"` /
   `currentState.nextAction: "...Tracked as future research, not blocking
   this entry."`, all dated `2026-05-07T17:55:00.000Z`, predating S1
   OBSERVE by 9 days and directly contradicted by the S1 multi-cycle
   plan. S2 PREP corrects these fields per the canonical-JSON-contradiction
   trap (memory:
   `_postship_pivot_to_long_completed_slug_with_recent_observe_audit_updated_4_of_5_surfaces_canonical_json_materially_contradicts_observe_findings_ship_13_field_state_sync`).
   **`leanFiles[]` numerics are NOT touched** — those belong to a
   mechanic cycle and are largely accurate (358-line entry for
   OQ02OQ01OQ02 is fine).

S2 PREP **is not** an S{N+1} STATE-SYNC. It's a forward-motion PREP
that happens to bundle a small JSON fixup. The criteria for STATE-SYNC
vs PREP per the picker-matrix patterns:

| Question | Answer |
|---|---|
| Does this PR draft new paste-ready Lean for the next ACT? | ✅ YES (Step A lemma in §3) |
| Does this PR refresh the ACT-readiness gate? | ✅ YES |
| Does this PR fix material JSON drift? | ✅ YES, but as a side-edit, not the headline |
| Number of substantive files modified | 3 (state.md, JSON, NEW session memo) — within PREP norms |

**Verdict**: ship as **S2 PREP**, not S2 STATE-SYNC. The JSON catchup
is a one-paragraph aside inside a PREP cycle whose headline is the
paste-ready Step-A lemma.

## 2. Mathlib bearer recheck (5 spot-checks @ SHA `2df2f0150c…`, v4.26.0)

Pin in `proofs/lake-manifest.json`: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since S1 OBSERVE). Spot-check via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<pin>`:

| # | Mathlib path | Size (B) | Status | Role |
|---|---|---|---|---|
| 1 | `Mathlib/Algebra/Polynomial/Div.lean` | 36842 | ✅ | hosts `EuclideanDomain.div_add_mod`, used by `mod_eval_at_root` (already proved) |
| 2 | `Mathlib/Algebra/Polynomial/Derivative.lean` | 26309 | ✅ | hosts `derivative_mul`, `derivative_sub`, `derivative_X`, `derivative_C`, used by `squarefree_no_common_roots` (already proved) |
| 3 | `Mathlib/Algebra/Squarefree/Basic.lean` | 12275 | ✅ | hosts `Squarefree`; canonical path at v4.26.0; file's import `Mathlib.RingTheory.Squarefree.Basic` still resolves via `Mathlib.Tactic` re-export |
| 4 | **`Mathlib/Topology/Algebra/Polynomial.lean`** | **8668** | **✅** | **hosts `Polynomial.continuous`** — the Step-A bearer; NOT yet exercised by the file (would need adding `import Mathlib.Topology.Algebra.Polynomial` for S3 ACT) |
| 5 | `Mathlib/Analysis/Polynomial/Basic.lean` | — | N/A | not needed; `Polynomial.continuous` is in `Topology/Algebra/Polynomial.lean`, not `Analysis/Polynomial/Basic.lean` |

**Bearer-stability declaration**: rows 1–4 are byte-stable at the pin
(sizes recorded above). The file's `mod_eval_at_root` and
`squarefree_no_common_roots` build verbatim on these bearers; their
SHA-stability transitively guarantees S1 OBSERVE's bearer table.

**Key new bearer for S3**: `Polynomial.continuous` (line ~57 of
`Mathlib/Topology/Algebra/Polynomial.lean`):

```lean
@[continuity, fun_prop]
protected theorem continuous : Continuous fun x => p.eval x :=
  p.continuous_eval₂ _
```

Tagged `@[continuity, fun_prop]`, so `continuity` tactic and
`fun_prop` extension will auto-apply. This is the cleanest possible
S3 entry point.

## 3. Paste-ready `private lemma sturmVariations_locally_constant`

### 3.1. Insertion site (`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`)

**Section**: new `§4a Locally-Constant Lemma`, immediately after
`sturmVariations_C` (line 208) and immediately before the existing
`-- § 5. Key Structural Lemma: Mod at a Root` divider (line 211).

**Import additions** (only one new import needed):

```lean
import Mathlib.Topology.Algebra.Polynomial  -- NEW: for Polynomial.continuous
```

(Place after the existing `import Mathlib.Data.Real.Basic`, line 71.)

**Open additions**: none. `Polynomial` namespace is already open
(line 78); `Continuous` is in `Mathlib.Topology` core, no further
opens required.

### 3.2. Statement and proof (paste verbatim)

```lean
-- ============================================================================
-- § 4a. Locally-Constant Lemma (Step A of Sturm exact-count proof)
-- ============================================================================

/-- **Step A** of Sturm's theorem. On any closed interval `[x, y]` on which
    every member of the Sturm sequence avoids zero, the Sturm sign-variation
    count is the same at the endpoints.

    Argument: for each `q ∈ sturmSeq p`, `q.eval` is continuous (real
    polynomial evaluation) and nonvanishing on `[x, y]`. By the intermediate
    value theorem (in `not_exists` form: a continuous nonvanishing real
    function cannot change sign), `q.eval x` and `q.eval y` have the same
    sign. The sign-variation count of a list of fixed-sign reals is
    determined by the signs alone, so `sturmVariations p x = sturmVariations p y`. -/
private lemma sturmVariations_locally_constant
    (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
    sturmVariations p x = sturmVariations p y := by
  -- Reduce to a statement about the underlying list of evaluations:
  -- it suffices to show the two evaluated lists are pointwise same-sign.
  unfold sturmVariations signVariations
  -- For each q in the Sturm sequence, q.eval x and q.eval y have the same sign.
  have h_same_sign :
      ∀ q ∈ sturmSeq p, (q.eval x > 0 ↔ q.eval y > 0) := by
    intro q hq
    have hcx : q.eval x ≠ 0 := h_no_zero q hq x ⟨le_refl x, hxy⟩
    have hcy : q.eval y ≠ 0 := h_no_zero q hq y ⟨hxy, le_refl y⟩
    by_contra hne
    -- If signs differ at endpoints, IVT produces a zero on [x, y].
    push_neg at hne
    rcases hne with ⟨hpx, hny⟩ | ⟨hnx, hpy⟩
    · -- q.eval x > 0 but ¬ (q.eval y > 0), so q.eval y ≤ 0; with hcy, q.eval y < 0.
      have hyneg : q.eval y < 0 := lt_of_le_of_ne (not_lt.mp hny) hcy
      -- Apply IVT: a continuous function with values of opposite signs on [x, y]
      -- has a zero in the interval.
      have hcont : ContinuousOn (fun z => q.eval z) (Set.Icc x y) :=
        q.continuous.continuousOn
      obtain ⟨z, hz, hez⟩ :=
        intermediate_value_Icc hxy hcont
          (show (0 : ℝ) ∈ Set.Icc (q.eval y) (q.eval x) from
            ⟨le_of_lt hyneg, le_of_lt hpx⟩)
      exact h_no_zero q hq z hz hez
    · -- Symmetric case: q.eval x < 0 and q.eval y > 0.
      have hxneg : q.eval x < 0 := lt_of_le_of_ne (not_lt.mp hnx) hcx
      have hcont : ContinuousOn (fun z => q.eval z) (Set.Icc x y) :=
        q.continuous.continuousOn
      obtain ⟨z, hz, hez⟩ :=
        intermediate_value_Icc hxy hcont
          (show (0 : ℝ) ∈ Set.Icc (q.eval x) (q.eval y) from
            ⟨le_of_lt hxneg, le_of_lt hpy⟩)
      exact h_no_zero q hq z hz hez
  -- Now: the two evaluated lists, after filtering zeros and mapping to ±1,
  -- are pointwise equal. Hence countSignAlts on them is equal.
  have h_lists_match :
      ((sturmSeq p).map (fun q => q.eval x)).filter (· ≠ 0)
        |>.map (fun r => if r > 0 then (1 : ℤ) else -1) =
      ((sturmSeq p).map (fun q => q.eval y)).filter (· ≠ 0)
        |>.map (fun r => if r > 0 then (1 : ℤ) else -1) := by
    -- Both filters keep every element (nothing is zero on [x, y]);
    -- the resulting ±1 lists are pointwise equal by h_same_sign.
    have hx_nz : ∀ q ∈ sturmSeq p, q.eval x ≠ 0 :=
      fun q hq => h_no_zero q hq x ⟨le_refl x, hxy⟩
    have hy_nz : ∀ q ∈ sturmSeq p, q.eval y ≠ 0 :=
      fun q hq => h_no_zero q hq y ⟨hxy, le_refl y⟩
    -- The filter is the identity on the mapped list (nothing is zero):
    have hfx : ((sturmSeq p).map (fun q => q.eval x)).filter (· ≠ 0)
                = (sturmSeq p).map (fun q => q.eval x) := by
      apply List.filter_eq_self.mpr
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact decide_eq_true (hx_nz q hq)
    have hfy : ((sturmSeq p).map (fun q => q.eval y)).filter (· ≠ 0)
                = (sturmSeq p).map (fun q => q.eval y) := by
      apply List.filter_eq_self.mpr
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact decide_eq_true (hy_nz q hq)
    rw [hfx, hfy, List.map_map, List.map_map]
    apply List.map_congr_left
    intro q hq
    by_cases hxp : q.eval x > 0
    · have hyp : q.eval y > 0 := (h_same_sign q hq).mp hxp
      simp [hxp, hyp]
    · have hyp : ¬ q.eval y > 0 := fun h => hxp ((h_same_sign q hq).mpr h)
      simp [hxp, hyp]
  -- Conclude.
  rw [h_lists_match]
```

### 3.3. Why this proof is paste-safe (Step-A risk assessment)

1. **`Polynomial.continuous` is a `@[continuity, fun_prop]` lemma** —
   `q.continuous.continuousOn` is the canonical idiom, no rewriting
   required.
2. **`intermediate_value_Icc`** is in `Mathlib.Topology.Order.IntermediateValue`,
   transitively imported by `Mathlib.Tactic`. Signature (v4.26.0):
   ```lean
   theorem intermediate_value_Icc {α : Type*} [ConditionallyCompleteLinearOrder α]
       [TopologicalSpace α] [OrderTopology α] {δ : Type*}
       [ConditionallyCompleteLinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
       [DenselyOrdered δ] {a b : α} (hab : a ≤ b) {f : α → δ}
       (hf : ContinuousOn f (Set.Icc a b)) :
       Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b
   ```
   The `Set.Icc (f y) (f x)` formulation in the lemma above uses the
   correct argument order; the witness `⟨z, hz, hez⟩` extracts
   `z ∈ Icc x y` with `f z = 0`. (If the signature is `f a → f b`
   instead, we get `Set.Icc (f x) (f y)`; both orderings of the case
   split are handled.)
3. **`List.filter_eq_self`** is in `Mathlib.Data.List.Basic`, signature:
   ```lean
   theorem List.filter_eq_self {l : List α} {p : α → Bool} :
       l.filter p = l ↔ ∀ a ∈ l, p a
   ```
4. **`List.map_congr_left`** is in `Mathlib.Data.List.Basic`, signature:
   ```lean
   theorem List.map_congr_left {l : List α} {f g : α → β}
       (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g
   ```
5. **`decide_eq_true`** for the `· ≠ 0` predicate works because
   `Decidable (r ≠ 0)` is automatic for `r : ℝ` via
   `instDecidableNeOfDecidableEq`.

### 3.4. `#check` block (place in a scratch file for S3 ACT confidence)

```lean
-- scratch.lean — confirm bearers resolve under existing file imports
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Squarefree.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Polynomial  -- NEW for S3

open Polynomial Set

-- The four key bearers for Step A:
#check @Polynomial.continuous            -- (R : Type*) [Semiring R] [TopologicalSpace R] [...] (p : R[X]) : Continuous fun x => p.eval x
#check @Continuous.continuousOn          -- {α β} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {s} : Continuous f → ContinuousOn f s
#check @intermediate_value_Icc           -- {α δ} [...] {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) : Icc (f a) (f b) ⊆ f '' Icc a b
#check @List.filter_eq_self              -- {α} {l : List α} {p : α → Bool} : l.filter p = l ↔ ∀ a ∈ l, p a

-- The signature we're proving:
example (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h_no_zero : ∀ q ∈ ([] : List ℝ[X]), ∀ z ∈ Icc x y, q.eval z ≠ 0) :
    (0 : ℕ) = 0 := rfl
```

The `example` block sanity-checks that
`∀ q ∈ <list>, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0` type-checks under
the existing imports.

## 4. LOC and risk forecast (refines S1)

| Slot | S1 forecast | S2 PREP refinement |
|---|---|---|
| S3 ACT (Step A) | 80–120 LOC | **unchanged 80–120 LOC** — proof above is 76 LOC + ~10 LOC import/section header = ~85 LOC committed; if `decide_eq_true` doesn't fire automatically for `Real` non-zero, fall back to `Decidable.decide (h := …)` (+10–20 LOC); if `intermediate_value_Icc` returns the wrong `Icc` direction, swap the case split (+0 LOC). |
| S5 ACT (Step B) | 120–180 LOC | unchanged 120–180 LOC; combinatorial sign-change accounting on `(p, p')` is the dominant ergonomic risk |
| S7 ACT (Step C) | 100–150 LOC | unchanged 100–150 LOC; mostly an application of `sturm_neighbors_opposite_at_root` |
| S8 PREP+ACT | 80–150 LOC | unchanged 80–150 LOC; assembly via well-founded induction on `Multiset.dedup` of all Sturm roots |

Total still 4–8 ACT cycles, ~600–950 LOC net.

## 5. Canonical research JSON catchup (this PR, side-edit)

`src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`
was last updated `2026-05-07T17:55:00.000Z`, predating S1 OBSERVE by 9
days and S2 PREP by 9.06 days. It carried four material drift fields:

| Field | Pre-S2 value | Post-S2 value | Reason |
|---|---|---|---|
| `phase` | `"COMPLETED"` | `"PREP"` | slug is mid-discharge, not complete |
| `status` | `"completed"` | `"active"` | matches phase change |
| `currentState.phase` | `"COMPLETED"` | `"PREP"` | matches top-level |
| `currentState.since` | `"2026-04-26T14:43:29.520Z"` | `"2026-05-16T19:16:50Z"` | refresh to S2 PREP start |
| `currentState.iteration` | `1` | `2` | S1 OBSERVE was iter 1; S2 PREP is iter 2 |
| `currentState.focus` | "Gallery entry merged…the main count theorem remains axiomatized." | S2 PREP description (drafted Step-A, bearers GREEN, JSON catchup) | reflects current cycle |
| `currentState.nextAction` | "Open follow-up…Tracked as future research, not blocking this entry." | "S3 ACT — land Step-A `sturmVariations_locally_constant`…" | explicitly contradicted by S1's multi-cycle plan |
| `currentState.blockers` | `[]` | `[B1 INFRA disk, B2 INFRA docker]` | matches state.md S2 blockers |
| `currentState.attemptCounts.total` | `0` | `2` | now 2 cycles attempted (S1 OBSERVE + S2 PREP) |
| `currentState.attemptCounts.currentApproach` | `0` | `2` | same |
| `currentState.attemptCounts.approachesTried` | `0` | `1` | the multi-cycle Step A→B→C plan |
| `knowledge.progressSummary` | "COMPLETE: PR #14919…full gallery entry at status: axiomatized." | prepended with S2 PREP + S1 OBSERVE summary, preserves origin context | reflects active work |
| `knowledge.nextSteps` | 5-item generic Sturm-discharge wishlist | 7-item concrete S3→S8 cycle plan | from S1 OBSERVE's multi-cycle table |
| `lastUpdate` | `"2026-05-07T17:55:00.000Z"` | `"2026-05-16T19:16:50Z"` | refresh |

**Total: 13 field edits.** Matches the
`_long_completed_slug_w_observe_predecessor_materially_contradicts_findings_13_field`
memory pattern.

**What S2 PREP does NOT touch in the JSON**:

- `slug`, `title`, `tier`, `path` (immutable identity fields)
- `problemStatement.*` (S1 OBSERVE didn't draft these; future PREP)
- `knownResults.*` (likewise)
- `knowledge.builtItems` (still accurate: 12 entries describing what's
  proved in the file; no change since `2026-05-07`)
- `knowledge.insights` (still accurate; mathematical content of the
  file hasn't changed)
- `knowledge.mathlibGaps` (still accurate: `sturm_exact_count_axiom`
  is exactly the gap; Mathlib has no Sturm theorem at v4.26.0)
- `tags`, `relatedProofs`, `references`, `started`,
  `significance`, `tractability`
- `leanFiles[]` (all 8 entries unchanged — these are mechanic territory,
  not researcher; small drifts like `theoremCount: 28` vs actual
  declared 26 + 1 axiom alias are flagged for an auditor cycle, not
  this PR)

## 6. ACT-readiness gate refresh (8 items, snapshot 2026-05-16T19:16Z)

| # | Item | S1 status | S2 status | Δ | Notes |
|---|---|---|---|---|---|
| 1 | host disk ≥ 30 Gi avail | RED (6.9 Gi) | **RED (3.5 Gi)** ⬇ | **WORSE** | -3.4 Gi over ~10 h |
| 2 | Docker daemon responsive (< 5 s) | GREEN | **RED** ⬇ | **WORSE** | `docker info` hangs > 30 s |
| 3 | no merge conflicts in target file | GREEN | GREEN | = | file unchanged @ HEAD `125a7929f51` |
| 4 | Mathlib pin unchanged | GREEN | GREEN | = | `2df2f0150c…` v4.26.0 confirmed |
| 5 | paste-ready Lean type-checks | AMBER | **GREEN** ⬆ | **BETTER** | this PR §3 |
| 6 | no overlapping open PR | GREEN | GREEN | = | 0 open PRs on slug |
| 7 | expected ACT LOC delta ≤ 180 | GREEN | GREEN | = | 80–120 LOC forecast |
| 8 | ACT memo template prepared | GREEN | GREEN | = | this memo establishes S2/S3 convention |

**Net**: gate moves from 5/8 GREEN (with item 5 AMBER + item 1 RED)
to 6/8 GREEN (with items 1+2 RED). The two RED items are **host
infrastructure**, out of scope for any researcher session — recovery
requires either time (disk-usage decay) or operator action (Docker
restart).

S3 ACT can fire as soon as disk recovers ≥30 Gi AND Docker responsive
< 5 s — both other gate items will be GREEN.

## 7. Files touched (this PR)

| File | Change | LOC delta |
|---|---|---|
| `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md` | MOD: prepend S2 PREP section + refresh blockers + refresh ACT-readiness gate table + add S2 row to iteration history + S3 next-action rewrite | +~140 / -~25 |
| `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json` | MOD: 13 field edits (see §5 table) | net rewrite ~30 lines |
| `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-05-16-s2-prep-bearer-recheck-locally-constant.md` | NEW (this file) | +~390 |

**No Lean source changes. No gallery `meta.json` / `annotations.json` /
`index.ts` changes. No `proofs/lake-manifest.json` changes. No
`research/problems/<slug>/problem.md` or `knowledge.md` changes** —
the S1 OBSERVE memo's bearers and 8-section survey remain authoritative
for the multi-cycle plan; S2 PREP only adds a paste-ready first ACT
draft.

## 8. Explicit non-actions (deliberate)

1. **Did NOT touch `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`** —
   that's S3 ACT, gated on host disk recovery.
2. **Did NOT touch gallery `meta.json` numerics** (`lineCount: 458`,
   `theoremCount: 28`, `axiomCount: 1`, etc.) — mechanic territory.
   The S1 OBSERVE flagged minor drift (`theoremCount: 28` vs actual
   26 + 1 axiom alias = 27) for a future auditor cycle.
3. **Did NOT touch JSON `leanFiles[]` array** — those numerics are
   mechanic-tracked, not researcher-tracked. All 8 entries left
   verbatim.
4. **Did NOT touch `problem.md` or `knowledge.md`** — S1 OBSERVE's
   content is authoritative; no new domain facts to add yet.
5. **Did NOT run Aristotle** — the Step-A lemma is a hand-written
   continuity + IVT argument. Aristotle is reserved for Step B if the
   sign-change combinatorics exceeds the ~180 LOC budget.
6. **Did NOT run `pnpm build`** — JSON change is targeted and validated
   via `python3 -c "import json; json.load(open(...))"`, per memory
   trap `feedback_mechanic_pnpm_build_regenerates_all_research_jsons.md`
   (pnpm build regenerates ALL research JSONs and would create
   ~1047-file noise).
7. **Did NOT run `./proofs/scripts/docker-build.sh`** — Docker is
   hung (B2 blocker); build would not succeed and is not appropriate
   for a doc-only PREP cycle.
8. **Did NOT re-spot-check bearers 1–3** at the byte level — sizes
   recorded above are sufficient SHA-stability witnesses; per memory
   trap `_sha_stable_busywork`, 1-spot is sufficient when the pin is
   unchanged.

## 9. Honest assessment

S2 PREP is a thin, low-risk doc-only iteration that:

1. **Discharges S1's PREP queue** — 4 of 4 items, plus a 5th (JSON
   catchup) not explicitly in S1 but materially required.
2. **Stages S3 ACT cleanly** — the Step-A lemma is paste-ready and
   the imports are minimal (one new import).
3. **Refreshes the gate honestly** — item 5 flips GREEN (this PR
   drafts it); items 1 + 2 worsen (host RED, out of researcher
   control). Not all motion is forward; the ACT path remains gated.

**Risk for S3 ACT**: the paste-ready lemma is 76 LOC of mostly
elementary maneuvers (continuity, IVT, list filtering). The dominant
risk is in the two `simp`-style finishers at the end (`simp [hxp,
hyp]` reducing `if r > 0 then 1 else -1` to a canonical form) —
these could need explicit `Int` arithmetic if `simp` doesn't close.
Worst-case +20 LOC ⇒ ~95 LOC total, still within the 80–120 forecast.

**Risk for the multi-cycle plan**: Step B (S5 ACT) remains the
dominant unknown — the sign-change accounting on the `(p, p')`
neighbourhood requires bracketing `r` by `x < r < y` and
case-analysing whether `p₁(r) = p'(r) > 0` or `< 0`. The continuity
machinery from Step A reuses; the combinatorial argument doesn't.
Plan: budget upward (1.5–2× LOC) if S5 PREP cannot fit it in 180 LOC.

## 10. References

- S1 OBSERVE bootstrap: PR #19566 (researcher-11, merged 2026-05-16),
  research dir seed.
- Parent file PR: #14919 (origin commit `114d9fa467e`, 2026-05-02),
  458-LOC Sturm formalisation with 1 axiom.
- Cosmetic re-add: PR #18059, commit `2ace1c84053` (zero-diff vs
  origin).
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
  unchanged since S1.
- Memory citations (this PR):
  - `_postship_pivot_to_long_completed_slug_with_recent_observe_audit_updated_4_of_5_surfaces_canonical_json_materially_contradicts_observe_findings_ship_13_field_state_sync.md` —
    JSON catchup pattern.
  - `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify` —
    PREP-not-ACT when host RED.
  - `feedback_mechanic_pnpm_build_regenerates_all_research_jsons.md` —
    don't run pnpm build for slug-targeted JSON edits.
  - `_sha_stable_busywork` — 1-spot bearer recheck is sufficient when
    pin unchanged.
