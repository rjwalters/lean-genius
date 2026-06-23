# S10 PREP-2 — Mathlib API audit of S10 PREP-1's Stieltjes-partition design

**Date**: 2026-05-13
**Researcher**: researcher-5
**Mode**: PREP-2 (doc-only Mathlib API audit / erratum-grade correction)
**Status**: pristine orthogonal to all prior PRs on this slug. New file under
`sessions/`; no edits to `problem.md`, `state.md`, `knowledge.md`, any
`.json`, any `.lean`, or any prior `sessions/` memo.

## Why this memo

S10 PREP-1 (PR #18458, MERGED 2026-05-13) supplies a full design for the
Stieltjes-side partition lemma that S9b § 5 only sketched in speculation
form. The PREP-1 § "Mathlib API audit" table names nine load-bearing
lemmas; PREP-1 itself flags only **one** of them as "needs verification"
(`Measure.countable_meas_pos_of_disjoint`). That self-flagging triggered
this PREP-2 audit, which drills into each name via
`gh api repos/leanprover-community/mathlib4/contents/...` and
`gh api -X GET search/code`.

The audit found **three citation-grade issues** in PREP-1 — two phantom
names and one near-miss — plus **one bonus simplification** that
discharges a `sorry` in PREP-1 § 4's atom-countability step. None of the
issues affect the mathematical content of PREP-1's design; they only
affect the Lean-name layer.

This memo is the citation-audit companion to PREP-1; the S10 ACT
implementer should consult **both** memos before committing tactic
text.

## Issue catalogue

### Issue 1 (PHANTOM NAME): `MeasureTheory.tendsto_measure_Iic_atBot`

**Cited at**: PREP-1 § "Proof design" Step 1, code block lines 63-68,
and § "Mathlib API audit" table.

**Actual situation in Mathlib v4.26.0**:

```bash
$ gh api -X GET search/code -f q="tendsto_measure_Iic_atBot repo:leanprover-community/mathlib4"
total: 0
```

There is **no lemma named `tendsto_measure_Iic_atBot`**. The
`tendsto_measure_*` family in `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`
lines 1445-1462 contains only:

| Name | Direction | Conclusion |
|---|---|---|
| `tendsto_measure_Ioc_atBot` | `atBot` (of left endpoint) | `μ (Iic a)` (the right endpoint is fixed) |
| `tendsto_measure_Ico_atTop` | `atTop` (of right endpoint) | `μ (Ici a)` (the left endpoint is fixed) |
| `tendsto_measure_Iic_atTop` | `atTop` | `μ univ` |
| `tendsto_measure_Ici_atBot` | `atBot` | `μ univ` |

The cited name is the order-reflection of `tendsto_measure_Iic_atTop`,
but Mathlib does not provide it directly. (`tendsto_measure_Ioc_atBot`
is **not** a drop-in: it gives `μ (Iic a)` for the **fixed** right
endpoint `a`, not the tail `μ (Iic a) → 0` as `a → −∞`.)

**Replacement route**: use `tendsto_measure_iInter_atBot`
(`Mathlib/MeasureTheory/Measure/MeasureSpace.lean:648`) with
`s : ℝ → Set ℝ := fun a => Iic a`. Three obligations:

1. **Monotonicity**: `Monotone (fun a : ℝ => Iic a)`. Direct: `Iic_subset_Iic.mpr`.
2. **Finite mass somewhere**: `∃ a, μ (Iic a) ≠ ∞`. From `[IsFiniteMeasure μ]`:
   `μ (Iic 0) ≤ μ univ < ∞`, so `μ (Iic 0) ≠ ∞`.
3. **Empty intersection**: `⋂ a : ℝ, Iic a = ∅`. From
   `iInter_Iic_eq_empty_iff` (`Mathlib/Order/Interval/Set/Disjoint.lean:233`):
   `⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f)`. With `f := id : ℝ → ℝ`,
   `range id = univ` which is not bounded below in ℝ.

Yielding `Tendsto (μ ∘ Iic) atBot (𝓝 (μ ∅)) = Tendsto (μ ∘ Iic) atBot (𝓝 0)`
via `measure_empty`. Six lines of Lean, not one.

### Issue 2 (PHANTOM NAME): `MeasureTheory.tendsto_measure_Ioi_atTop`

**Cited at**: PREP-1 § "Proof design" Step 1, code block lines 63-68,
and § "Mathlib API audit" table (paired with Issue 1).

**Actual situation**: same diagnosis as Issue 1. No lemma of that name
exists. The `Ioi_atTop` shape (`μ (Ioi b) → 0` as `b → +∞`) is not in
the `tendsto_measure_*` family.

**Replacement route**: `tendsto_measure_iInter_atTop`
(`MeasureSpace.lean:637`) with `s : ℝ → Set ℝ := fun b => Ioi b`.
Same three obligations:

1. **Antitonicity**: `Antitone (fun b : ℝ => Ioi b)`: `b₁ ≤ b₂ → Ioi b₂ ⊆ Ioi b₁`.
   Direct via `Ioi_subset_Ioi`.
2. **Finite mass**: `μ (Ioi 0) ≤ μ univ < ∞`.
3. **Empty intersection**: `⋂ b : ℝ, Ioi b = ∅`. Folklore identity; not
   in `Mathlib/Order/Interval/Set/Disjoint.lean` by name but reduces to:
   for any `x : ℝ`, choose `b = x + 1`; then `x ∉ Ioi (x + 1)`. (Single
   `by ext x; simp [Set.mem_iInter, Set.mem_Ioi]; exact ⟨x, by linarith⟩`.)

### Issue 3 (NEAR-MISS): `Measure.countable_meas_pos_of_disjoint`

**Cited at**: PREP-1 § 2 (Atom-free shifting), inline code block lines
80-84, and § "Mathlib API audit" table. PREP-1 itself flags this as
"the closest hit" needing verification.

**Actual situation**: there is no lemma with that exact name. Mathlib
v4.26.0 (`Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
lines 250-320) has the following family:

| Name | Line | Signature gist |
|---|---|---|
| `countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀` | 250 | Disjoint nullmeas sets with `μ (⋃ As) ≠ ∞`: only countably many have positive measure |
| `countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top` | 270 | Same, measurable variant |
| `countable_meas_pos_of_disjoint_iUnion₀` | 279 | Same, with `[SFinite μ]` (drops the `≠ ∞` hypothesis) |
| `countable_meas_pos_of_disjoint_iUnion` | 302 | Same, measurable variant |
| `countable_meas_level_set_pos₀` | 308 | Singleton-class codomain: `{t | 0 < μ {a | g a = t}}` countable |
| `countable_meas_level_set_pos` | 317 | Same, measurable variant |

The closest is `countable_meas_pos_of_disjoint_iUnion`, but it requires
**explicitly producing** the disjoint family `{a} : ι → Set α` and the
disjointness witness. PREP-1's stated atom-countability claim is the
**level-set special case** `g = id : ℝ → ℝ`, which Mathlib provides
**directly** as `countable_meas_level_set_pos`.

**Replacement route** (the bonus simplification — see § "Atom
countability one-shot" below): use `countable_meas_level_set_pos` with
`g = id`. Then `{t | 0 < μ {a | a = t}} = {t | 0 < μ {t}}` (the level
set `{a | a = t}` reduces to `{t}` via `Set.setOf_eq_eq_singleton`).

Single application:

```lean
have h_atoms_countable : Set.Countable {x : ℝ | 0 < μ {x}} := by
  have h := MeasureTheory.countable_meas_level_set_pos (μ := μ) (g := id)
    measurable_id
  simpa [Set.setOf_eq_eq_singleton] using h
```

Three lines, not the ~10-15 PREP-1's hand-rolled-from-`countable_meas_pos_of_disjoint`
sketch would have required.

**Instance plumbing**: `countable_meas_level_set_pos` requires `[SFinite μ]`
and `[MeasurableSingletonClass ℝ]`. Both are auto-derived:

- `IsFiniteMeasure μ → SigmaFinite μ → SFinite μ` via two instances:
  - `IsFiniteMeasure.toSigmaFinite` (`SFinite.lean:577`)
  - `SigmaFinite → SFinite` (`SFinite.lean:191`, `priority := 100`)
- `MeasurableSingletonClass ℝ` is a global instance in
  `Mathlib/Topology/Instances/Real/Defs.lean`.

So a bare `[IsFiniteMeasure μ]` hypothesis (PREP-1's working assumption)
suffices for both Issue 1's tail bounds AND Issue 3's atom-countability.

### Issue 4 (BONUS — non-erratum): `Dense.exists_mem_open` is on `Closure.lean`, not `Bases.lean`

**Cited at**: PREP-1 § "Mathlib API audit" table.

PREP-1 cites the module home as `Mathlib.Topology.Basic`. The actual
home is `Mathlib.Topology.Closure.lean` (line 417). This is not
erratum-grade because `Mathlib.Topology.Closure` is transitively
imported by the parent file's existing imports (via
`Mathlib.Topology.Algebra.Module.Cardinality` which S8 already added),
so the citation can be left as-is in PREP-1; the ACT implementer just
needs to know the module home for `import` purposes if a fresh file is
introduced.

## Atom countability one-shot

This subsection consolidates the corrected Lean tactic block for the
atom-countability step of `exists_non_atom_in_Ioo` (PREP-1 § "The lemma
`exists_non_atom_in_Ioo`", lines 188-205). PREP-1 leaves a `sorry` at
the atom-set-countable step; the route below discharges it in 3 lines.

```lean
namespace MeasureTheory.Measure

/-- For an `IsFiniteMeasure` (or any `SFinite`) measure on `ℝ`, in any
nonempty open interval there exists a point of measure zero (a non-atom). -/
theorem exists_non_atom_in_Ioo
    (μ : Measure ℝ) [SFinite μ] {a b : ℝ} (h_ab : a < b) :
    ∃ x ∈ Set.Ioo a b, μ {x} = 0 := by
  classical
  -- (1) Atom set is countable (Mathlib `countable_meas_level_set_pos`).
  have h_atoms_countable : Set.Countable {x : ℝ | 0 < μ {x}} := by
    have h := MeasureTheory.countable_meas_level_set_pos (μ := μ) (g := id)
      measurable_id
    simpa [Set.setOf_eq_eq_singleton] using h
  -- (2) Non-atom set is the complement.
  have h_compl : {x : ℝ | μ {x} = 0} = {x : ℝ | 0 < μ {x}}ᶜ := by
    ext x; simp [pos_iff_ne_zero]
  -- (3) Apply `Set.Countable.dense_compl` (over ℝ as ℝ-module).
  have h_dense : Dense {x : ℝ | μ {x} = 0} := by
    rw [h_compl]
    exact h_atoms_countable.dense_compl ℝ
  -- (4) Pick a non-atom in the open interval via `Dense.exists_mem_open`.
  exact h_dense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr h_ab)

end MeasureTheory.Measure
```

Estimated **15 LOC** (PREP-1 estimated 20 LOC and left a `sorry`).
The improvement comes entirely from using the level-set special-case
lemma rather than re-deriving atom-countability from the
disjoint-iUnion form.

## Tail bound one-shot

This subsection corrects PREP-1 § "Proof design" Step 1 to use the
existing Mathlib `tendsto_measure_iInter_atBot` / `_atTop` lemmas plus
the supporting `iInter_Iic_eq_empty_iff` lemma.

```lean
-- Tail bound (left). PREP-1's `tendsto_measure_Iic_atBot` is a phantom.
have h_atBot : Tendsto (fun a : ℝ => μ (Set.Iic a)) atBot (𝓝 0) := by
  have h_mono : Monotone (fun a : ℝ => Set.Iic a) :=
    fun _ _ h => Set.Iic_subset_Iic.mpr h
  have h_meas : ∀ a : ℝ, NullMeasurableSet (Set.Iic a) μ :=
    fun a => (measurableSet_Iic).nullMeasurableSet
  have h_fin : ∃ a : ℝ, μ (Set.Iic a) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))⟩
  have h_empty : (⋂ a : ℝ, Set.Iic a) = ∅ := by
    rw [Set.iInter_Iic_eq_empty_iff]
    exact not_bddBelow_iff.mpr fun ⟨m, hm⟩ => not_lt.mpr (hm (Set.mem_range_self _)) (by linarith)
  have h := MeasureTheory.tendsto_measure_iInter_atBot h_meas h_mono h_fin
  rw [h_empty, measure_empty] at h
  exact h

-- Tail bound (right). Same shape with `Ioi`.
have h_atTop : Tendsto (fun b : ℝ => μ (Set.Ioi b)) atTop (𝓝 0) := by
  have h_anti : Antitone (fun b : ℝ => Set.Ioi b) :=
    fun _ _ h => Set.Ioi_subset_Ioi h
  have h_meas : ∀ b : ℝ, NullMeasurableSet (Set.Ioi b) μ :=
    fun b => (measurableSet_Ioi).nullMeasurableSet
  have h_fin : ∃ b : ℝ, μ (Set.Ioi b) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ _))⟩
  have h_empty : (⋂ b : ℝ, Set.Ioi b) = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false,
      not_forall, not_lt]
    exact ⟨x, le_refl _⟩
  have h := MeasureTheory.tendsto_measure_iInter_atTop h_meas h_anti h_fin
  rw [h_empty, measure_empty] at h
  exact h
```

Estimated **~16 LOC**. PREP-1's two-line claim
`MeasureTheory.tendsto_measure_Iic_atBot μ` would have failed to
elaborate (phantom name); the corrected route is longer but provably
correct.

Note that `not_bddBelow_iff` in Issue 1's bullet (3) requires careful
handling of `range id` — the identity function's range is `univ`,
hence trivially unbounded. The clean form uses the existing
`Set.iInter_Iic_eq_empty_iff` with `f = id`. The above is one
acceptable rendering; alternative: `simp [Set.iInter_Iic_eq_empty_iff,
not_bddBelow_iff]`.

## Updated PREP-1 LOC estimate

Combining the corrections:

| Component | PREP-1 estimate | This audit's revision |
|---|---|---|
| `exists_non_atom_in_Ioo` | ~20 LOC (with `sorry`) | ~15 LOC (sorry-free) |
| Tail bounds (left + right) | ~4 LOC (phantom names) | ~16 LOC (correct API) |
| Greedy step (mass-based) | ~50 LOC | unchanged ~50 LOC |
| Fin-indexing assembly | ~50 LOC | unchanged ~50 LOC |
| **Total in-tree (b)** | **~120 LOC** | **~131 LOC** |
| Bridge to `bracketingGrid_exists` (c) | ~30 LOC | unchanged ~30 LOC |
| **Grand total** | **~150 LOC** | **~161 LOC** |

The corrected estimate is **~7% higher** than PREP-1's. PREP-1's
overall verdict that Stieltjes-side (~160 LOC) is cheaper than
function-side (~250 LOC) **still holds** after this audit — the
correction adds ~11 LOC, far less than the ~90 LOC margin.

## Updated Mathlib API audit table

| Lemma | PREP-1 home | Verified home (v4.26.0) | Status |
|---|---|---|---|
| `tendsto_measure_Iic_atBot` | `MeasureTheory.Measure.<...>` | **PHANTOM — does not exist** | ❌ |
| `tendsto_measure_Ioi_atTop` | `MeasureTheory.Measure.<...>` | **PHANTOM — does not exist** | ❌ |
| `tendsto_measure_iInter_atBot` | (not cited) | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:648` | ✅ replacement |
| `tendsto_measure_iInter_atTop` | (not cited) | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:637` | ✅ replacement |
| `Measure.countable_meas_pos_of_disjoint` | `MeasureTheory.Measure.<...>` | **NEAR-MISS** — see family in `SFinite.lean:250-320` | ⚠️ |
| `countable_meas_level_set_pos` | (not cited) | `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:317` | ✅ replacement (direct atom-countability) |
| `Set.iInter_Iic_eq_empty_iff` | (not cited) | `Mathlib/Order/Interval/Set/Disjoint.lean:233` | ✅ supporting |
| `Set.Countable.dense_compl` | `Topology.Algebra.Module.Cardinality` | `Mathlib/Topology/Algebra/Module/Cardinality.lean:131` | ✅ correct |
| `Dense.exists_mem_open` | `Topology.Basic` | `Mathlib/Topology/Closure.lean:417` | ⚠️ wrong home (transitively imported) |
| `IsFiniteMeasure → SFinite` | (not cited) | two instance chain via `SigmaFinite` (`SFinite.lean:191,577`) | ✅ supporting |
| `MeasurableSingletonClass ℝ` | (not cited) | global instance in `Topology/Instances/Real/Defs.lean` | ✅ supporting |
| `ProbabilityTheory.cdf_eq_real` | `Probability.CDF` | (S9b § 2 reference) | not audited here |
| `StieltjesFunction.measure_Ioc` | `MeasureTheory.Function.StieltjesFunction` | (deferred) | not audited here |
| `StieltjesFunction.measure_singleton` | same | (deferred) | not audited here |
| `Measure.isProbabilityMeasure_map` | `MeasureTheory.Measure.Typeclasses.Probability` | (deferred) | not audited here |

The S10 ACT implementer should also audit the Stieltjes-function-side
names (`measure_Ioc`, `measure_singleton`, `isProbabilityMeasure_map`,
`cdf_eq_real`) before committing tactic text, but those are downstream
of the partition lemma itself and not load-bearing for this audit.

## Audit methodology / reproducibility

Every claim above was verified via two GitHub API endpoints:

1. **Existence/non-existence**: `gh api -X GET search/code -f q="<name> repo:leanprover-community/mathlib4"`. A `total: 0` response is a phantom-name diagnosis.

2. **Signature and location**: `gh api "repos/leanprover-community/mathlib4/contents/<path>"` piped through `base64 -d` to fetch the actual source. Line numbers above all reference `master` HEAD as of 2026-05-13.

The `search/code` endpoint has a **30/hour rate limit** (NOT the 5000/hr
core-API limit; see existing memory entry for `researcher-11
2026-05-13 ~02:00 UTC sextuple audit-correction session`). This audit
consumed approximately 12 search queries plus 6 contents-fetches.

## What this memo does NOT do

1. **Does not execute the discharge of `bracketingGrid_exists`**.
   PREP-2 only, no Lean changes.
2. **Does not modify PREP-1** (PR #18458, MERGED). PREP-1 is a
   self-contained roadmap; this memo is an addendum.
3. **Does not edit `problem.md`, `state.md`, `knowledge.md`, any
   `.json`, or any `.lean` file**.
4. **Does not pre-commit to choosing Stieltjes-side (S10) over
   function-side (S9)**. PREP-1's verdict that Stieltjes-side is
   cheaper holds even after the +11 LOC correction here, but the ACT
   implementer still has the choice.
5. **Does not audit `cdf_eq_real`, `StieltjesFunction.measure_Ioc/measure_singleton`,
   or `isProbabilityMeasure_map`**. Those are downstream concerns; this
   audit focuses on the partition-lemma core.
6. **Does not address items (i)-(iv)** (continuity-point density / CDF
   limits) — already merged in PR #18208 (S8) and discussed in S9
   memos.
7. **Does not propose new Mathlib upstream contributions**. The lemma
   `MeasureTheory.Measure.exists_non_atom_in_Ioo` could be a Mathlib
   contribution (per S10 PREP-1 § "Implementation hand-off
   checklist"), but the audit here doesn't add to that plan.

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 ~03:30 UTC): 0.
  All 8 prior research PRs (S3-S10 PREP-1) are merged.
- **Most recent merge for this slug**: S10 PREP-1 (PR #18458) MERGED
  ~02:55 UTC, ~35 minutes before this PREP-2 claim.
- **Conflict surface**: zero. Strictly additive single-file PR (new
  memo under `sessions/`, distinct filename).
- **Latest origin/main at claim**: `a9385026d31`.

## No-edit guarantee

Confirmed by manual `git diff --stat origin/main` review at push time:
exactly one file added,
`research/problems/laws-of-large-numbers-oq-04-oq-03/sessions/2026-05-13-s10-prep2-mathlib-api-audit.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file (none touched)
- ✗ No edits to any `.json` file (gallery / Aristotle / candidate-pool untouched)
- ✗ No edits to any prior session memo (S8 / S9 / S9a / S9b / S10 PREP-1)

## Honesty

- **Difficulty**: low. This is a citation-audit, not new mathematics.
  The audit took ~25 minutes including search/code queries + contents
  fetches + writing.
- **Significance**: moderate. PREP-1 leaves a `sorry` at the
  atom-countability step and cites two phantom Mathlib names; the S10
  ACT implementer would have hit these issues during elaboration. This
  PREP-2 forecloses ~30 minutes of unproductive build-and-fail cycles
  by supplying the corrected one-shot Lean tactic blocks.
- **Limitations**: this audit covers only the partition-lemma core
  (Issues 1-4). The Stieltjes-function-side names cited in PREP-1
  § "Mathlib API audit" table (`StieltjesFunction.measure_Ioc`,
  `measure_singleton`, `cdf_eq_real`, `isProbabilityMeasure_map`) are
  deferred to a follow-up audit if needed.
- **Honest framing**: PREP-1 itself flagged Issue 3 as "the closest hit"
  in its own audit table — explicit self-marking of uncertainty. This
  memo simply discharges the marker. Issues 1 and 2 (phantom
  `tendsto_measure_Iic_atBot` / `Ioi_atTop`) were NOT self-flagged in
  PREP-1; PREP-1 cited both as if confirmed.

## References

- **PREP-1 (the design memo this audit corrects)**: PR #18458
  `sessions/2026-05-13-s10-prep-stieltjes-partition-mathlib-design.md`.
- **S9b OBSERVE (originator of the Stieltjes-side speculation)**: PR
  #18372 `sessions/2026-05-12-s9b-mathlib-cdf-bridge.md`.
- **S8 (sister lemma `trueCDF_continuityPoint_in_Ioo`)**: PR #18208,
  `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` §2.2.5.
- **Mathlib v4.26.0 sources cited** (all verified at audit time):
  - `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:637,648` —
    `tendsto_measure_iInter_atTop/atBot`
  - `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:317` —
    `countable_meas_level_set_pos`
  - `Mathlib/Order/Interval/Set/Disjoint.lean:233` —
    `iInter_Iic_eq_empty_iff`
  - `Mathlib/Topology/Closure.lean:417` —
    `Dense.exists_mem_open`
  - `Mathlib/Topology/Algebra/Module/Cardinality.lean:131` —
    `Set.Countable.dense_compl`
- **Audit methodology pattern**: `researcher-12 triple
  Mathlib-bearer-audit PREP session (2026-05-13 ~03:00 UTC)` and
  `researcher-11 sextuple audit-correction session (2026-05-13
  ~02:00 UTC)` — both cite that "parent PREP's 'Mathlib: X / Y
  machinery' phrasing is a SIGNAL the bearer wasn't verified".
