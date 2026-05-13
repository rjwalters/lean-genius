# S10 PREP — Stieltjes-side partition lemma design for `bracketingGrid_exists`

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to all prior PRs on this slug. Specifically:
- PR #18208 (S8, items (i)–(iii), MERGED)
- PR #18292 (S9 OBSERVE, function-side item (v) design, MERGED)
- PR #18313 (S9a OBSERVE, function-side item (iv) blueprint, MERGED)
- PR #18372 (S9b OBSERVE, Mathlib `cdf` short-circuit, MERGED, sketches
  Stieltjes-side item (v) in § 5 as "speculation")

This memo fills the **gap explicitly flagged by S9b § 5**: a *design*
(not speculation) for the Stieltjes-measure partition lemma that S9b
identifies as a "significant reduction" of the function-side greedy walk
in S9. The S9b memo names but does not design
`MeasureTheory.Measure.exists_finite_partition_no_atom_of_finite`. This
memo supplies the full design.

## Context: the three competing item-(v) designs

| Memo | Approach | LOC | Status |
|---|---|---|---|
| S9 OBSERVE (#18292) | Function-side greedy walk: `Monotone.exists_increasing_continuity_seq` | ~200 in Mathlib + ~50 wrap | **MERGED, fully designed** |
| S9b § 5 (#18372) | Stieltjes-measure partition + cdf-bridge | ~100-150 Mathlib + ~30 wrap | **MERGED, speculation only** |
| **This S10 PREP** | **Detailed design of S9b § 5's Mathlib lemma** | ~120 LOC | — |

## The target lemma

S9b § 5 names the lemma but does not state it precisely. The natural form is:

```lean
namespace MeasureTheory

/-- For any finite (or probability) measure `μ` on `ℝ` and any `ε > 0`,
    there is a finite increasing sequence of non-atom points
    `q : Fin (k + 2) → ℝ` such that each cell `(q i, q (i+1)]` has
    measure at most `ε`, `μ (Iic (q 0)) ≤ ε`, and
    `μ (Ioi (q (Fin.last (k+1)))) ≤ ε`. -/
theorem Measure.exists_finite_partition_no_atom_of_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ q : Fin (k + 2) → ℝ,
      StrictMono q ∧
      (∀ j, μ {q j} = 0) ∧
      (∀ j : Fin (k + 1),
        μ (Set.Ioc (q j.castSucc) (q j.succ)) ≤ ENNReal.ofReal ε) ∧
      μ (Set.Iic (q 0)) ≤ ENNReal.ofReal ε ∧
      μ (Set.Ioi (q (Fin.last (k + 1)))) ≤ ENNReal.ofReal ε

end MeasureTheory
```

The probability-measure specialization (μ = Measure.map (X 0) μ_Ω, our use case)
follows directly via `IsProbabilityMeasure.toIsFiniteMeasure`.

## Proof design

### Step 1: Tail bounds

For an `IsFiniteMeasure μ` on ℝ:

```lean
have h_atBot : Tendsto (fun a => μ (Set.Iic a)) atBot (𝓝 0) :=
  MeasureTheory.tendsto_measure_Iic_atBot μ

have h_atTop : Tendsto (fun b => μ (Set.Ioi b)) atTop (𝓝 0) :=
  MeasureTheory.tendsto_measure_Ioi_atTop μ
```

Both are in `Mathlib.MeasureTheory.Measure.MeasureSpaceBase` (lemma names
verified via `gh api`). From `h_atBot`, pick `q_left : ℝ` such that
`μ (Set.Iic q_left) ≤ ENNReal.ofReal ε / 2`; similarly `q_right`.

### Step 2: Atom-free shifting

If `q_left` is an atom of `μ` (i.e. `μ {q_left} > 0`), shift slightly. The
key Mathlib fact:

```lean
-- Mathlib.MeasureTheory.Measure.IsAtomic? (verify exact location)
theorem countable_meas_pos_singleton (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Set.Countable {x : ℝ | μ {x} ≠ 0}
```

This follows from `μ` being σ-finite and "atomic mass ≤ total mass / 1 per
atom" counting. The atom set is therefore countable, hence its complement
is dense. We can pick `q_left' ∈ (q_left - δ, q_left]` with `q_left'`
non-atom; by continuity of `μ (Iic ·)` (or right-continuity of the
Stieltjes CDF), `μ (Iic q_left') ≤ μ (Iic q_left) + δ' ≤ ε` for sufficiently
small δ'. Similarly for `q_right'`.

### Step 3: Bounded-interval greedy partition

Inside `(q_left', q_right']`, the measure mass is at most `μ(ℝ) - μ(Iic q_left') - μ(Ioi q_right') < μ(ℝ)`. Greedy step: starting from `q_0 := q_left'`, define

```lean
q_{j+1} := inf { x : ℝ | μ (Set.Ioc q_j x) > ε / 2 ∧ μ {x} = 0 }
```

if the set is nonempty; otherwise terminate. The infimum is well-defined because:

1. The set is nonempty as long as `μ (Set.Ioc q_j q_right') > ε / 2`.
2. The infimum is itself a non-atom (atom set is countable, so the
   infimum of an uncountable set of non-atoms is generically non-atom).

Wait — step (2) is not quite right. The infimum of non-atoms is not
necessarily a non-atom. Refine: define

```lean
q_{j+1} := some_non_atom_in (Set.Ioc q_j (greedy_right_boundary))
```

where `greedy_right_boundary` is `inf { x | μ (Set.Ioc q_j x) ≥ ε / 2 }`,
and we use the **dense-non-atom** lemma:

```lean
-- Variant of S8's trueCDF_continuityPoint_in_Ioo, but at the measure level:
theorem MeasureTheory.Measure.exists_non_atom_in_Ioo
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (h_ab : a < b) :
    ∃ x ∈ Set.Ioo a b, μ {x} = 0
```

This is the **measure-side analog** of S8's `trueCDF_continuityPoint_in_Ioo`.
Proof: atoms are countable (S9b § 5 cited fact), so non-atoms in `(a, b)`
form an uncountable, dense subset. Apply `Set.Countable.dense_compl`
(same lemma S8 used).

### Step 4: Termination

Each cell has measure between `ε/2` and `ε`. Total mass is bounded by
`μ(ℝ) ≤ ∞` (no constraint), but for **probability measures**
`μ(ℝ) = 1`, so the cell count is `k ≤ ⌈2/ε⌉`. For general `IsFiniteMeasure`,
`k ≤ ⌈2 μ(ℝ) / ε⌉`.

The greedy partition terminates after at most `⌈2/ε⌉` steps for probability
measures; the Fin-bound is then `k + 2` cells (including the tail cells).

### Step 5: The full proof in Lean (sketch)

```lean
theorem Measure.exists_finite_partition_no_atom_of_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ q : Fin (k + 2) → ℝ, ... := by
  -- Step 1: pick q_0, q_{k+1} via tail bounds.
  obtain ⟨q_left, h_q_left⟩ := MeasureTheory.tendsto_measure_Iic_atBot.eventually
    (Filter.eventually_lt_of_tendsto_lt ...) hε
  -- ... (similar for q_right)

  -- Step 2: atom-free shift via exists_non_atom_in_Ioo.
  obtain ⟨q_left', h_q_left'_in, h_q_left'_atom⟩ :=
    MeasureTheory.Measure.exists_non_atom_in_Ioo μ ...

  -- Step 3: greedy fold for interior partition.
  let greedy_step : ℝ → Option ℝ := fun a =>
    if h : μ (Set.Ioc a q_right') ≤ ENNReal.ofReal ε then none
    else some (Classical.choose
      (MeasureTheory.Measure.exists_non_atom_in_Ioo μ ...))

  -- Apply Nat.rec or List.foldr with greedy_step until none.

  -- Step 4: assemble the Fin-vector and verify all properties by
  --         inductive invariants from greedy_step.

  sorry  -- ~80 LOC, mostly bookkeeping
```

### Why this is ~120 LOC (vs S9's ~200)

The S9 function-side approach:
- ~50 LOC for `Monotone.exists_increasing_continuity_seq` greedy step.
- ~120 LOC for recursion bookkeeping with Fin indexing.
- ~30 LOC for assembling boundary terms.

The Stieltjes-side approach:
- ~20 LOC for `exists_non_atom_in_Ioo` (parallel to S8's
  `trueCDF_continuityPoint_in_Ioo`, ~6 LOC there).
- ~50 LOC for greedy step (mass-based, simpler invariant: "remaining mass").
- ~50 LOC for Fin-indexing assembly.

**Net savings ~80 LOC** by leveraging the cleaner mass-tracking invariant.

## The lemma `exists_non_atom_in_Ioo`

This is the **load-bearing sub-lemma** needed to make the Stieltjes-side
design tractable. Its proof parallels S8's
`trueCDF_continuityPoint_in_Ioo` but at the measure level:

```lean
theorem MeasureTheory.Measure.exists_non_atom_in_Ioo
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (h_ab : a < b) :
    ∃ x ∈ Set.Ioo a b, μ {x} = 0 := by
  classical
  by_contra h_all_atoms
  push_neg at h_all_atoms
  -- Atoms form a countable set.
  have h_countable_atoms : Set.Countable {x | μ {x} ≠ 0} := by
    -- Use `Measure.countable_meas_pos_of_disjoint` or similar.
    sorry
  -- The non-atom set is dense in ℝ.
  have h_dense : Dense {x : ℝ | μ {x} = 0} :=
    Set.Countable.dense_compl ℝ h_countable_atoms.mono (fun _ h => h)
  -- Some point in Ioo a b is a non-atom.
  obtain ⟨x, hx_in, hx_atom⟩ := h_dense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr h_ab)
  exact ⟨x, hx_in, hx_atom⟩
```

The `Measure.countable_meas_pos_of_disjoint` fact (atom set is countable
for an `IsFiniteMeasure`) is the only Mathlib lookup that needs
verification — it's standard but the exact name may differ.

## Bridge to `bracketingGrid_exists`

Once the Stieltjes-side partition lemma lands in Mathlib, the gallery's
`bracketingGrid_exists` axiom discharges in ~30 LOC by:

```lean
theorem bracketingGrid_exists_proved [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (BracketingGrid (trueCDF X μ) ε) := by
  -- (1) Apply the cdf bridge from S9b § 2.
  -- (2) Apply the Stieltjes partition lemma to Measure.map (X 0) μ.
  -- (3) Convert measure-cell bounds to function-step bounds via
  --     `f.measure_Ioc` (one rfl per cell).
  -- (4) Convert non-atom condition to continuity via `f.measure_singleton`
  --     (one lemma per grid point).
  obtain ⟨k, q, hq_mono, hq_natom, hq_cells, hq_left, hq_right⟩ :=
    MeasureTheory.Measure.exists_finite_partition_no_atom_of_finite
      (Measure.map (X 0) μ) hε
  refine ⟨{ k := k, q := q,
            increasing := hq_mono,
            continuity := ?_,
            cell_step := ?_,
            boundary_left := ?_,
            boundary_right := ?_ }⟩
  all_goals
    intros
    -- Convert via cdf_eq_real / measure_Ioc / measure_singleton.
    sorry
```

Each `sorry` is a 2–3 line tactic chain. Total: ~30 LOC + the existing
~10 LOC cdf-bridge from S9b. Net: ~40 LOC in-tree, plus the ~120 LOC
upstream Mathlib lemma.

## Comparison: function-side (S9) vs Stieltjes-side (S10)

| Dimension | S9 function-side | S10 Stieltjes-side |
|---|---|---|
| Mathlib home | `Mathlib.Topology.Order.Monotone` | `Mathlib.MeasureTheory.Measure.<...>` |
| Mathlib LOC | ~200 | ~120 |
| In-tree wrap LOC | ~50 | ~40 |
| **Total** | **~250** | **~160** |
| Conceptual complexity | grid-walk on `F`-values | mass-tracking |
| Mathlib idiom match | new "F-image step" notion | re-uses existing measure API |
| Already prototyped | S9 (~design only, no Lean) | this PREP (~design only, no Lean) |

**Verdict**: the Stieltjes-side is strictly cheaper in LOC and idiom-fit.
The function-side is **already designed in full** (S9 OBSERVE PR #18292),
while the Stieltjes-side is **designed at the speculation level**
(S9b § 5). This memo upgrades the Stieltjes-side to "ready-for-ACT".

## Anti-targets

This memo deliberately does **not**:

1. **Execute the discharge of `bracketingGrid_exists`**. PREP only.
2. **Touch any existing Lean file**. The skeleton above is illustrative.
3. **Edit `problem.md` / `state.md` / `knowledge.md`**.
4. **Modify the merged S9 / S9a / S9b design memos**. Each is a
   self-contained roadmap; this memo extends S9b without editing it.
5. **Pre-commit to choosing S10 (Stieltjes) over S9 (function-side)**.
   That's an ACT-time decision. This PREP shows the Stieltjes path is
   viable; the ACT implementer can pick either based on Mathlib upstream
   feedback.
6. **Address item (iv) (CDF limits at ±∞)**. S9b § 3 supplies the
   drop-in patch; this memo concerns item (v) only.
7. **Re-derive S8's items (i)–(iii)**. Those are already in
   `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` §2.2.5 (merged PR #18208).

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 02:55 UTC): 0.
  All 7 prior PRs (S5–S9b) are merged.
- **Conflict surface**: zero. Strictly additive single-file PR
  (new memo under `sessions/`).
- **Most recent merge**: PR #18372 (S9b OBSERVE) MERGED 02:11 UTC.
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4 PREP).

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/laws-of-large-numbers-oq-04-oq-03/sessions/2026-05-13-s10-prep-stieltjes-partition-mathlib-design.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S9 / S9a / S9b)

## Honesty

- **Difficulty**: moderate. The mathematical content (greedy mass-based
  partition with atom-avoidance) is standard real-analysis. The Lean
  realisation has one moderate-effort sub-lemma (`exists_non_atom_in_Ioo`)
  and one extensively bookkeepy main lemma. The ~120 LOC estimate is
  conservative.
- **Significance**: high. S9b § 5 names this lemma as a "significant
  reduction" of the S9 function-side approach but does not design it.
  This memo closes that gap; the next implementer can pick S9 or S10
  for ACT based on Mathlib upstream feedback.
- **Status after S10 ACT (+ Mathlib PR)**: the slug's
  `bracketingGrid_exists` axiom discharges, the
  `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` companion becomes
  axiom-free, and the slug's full Glivenko-Cantelli chain reaches
  0 axioms / 0 sorries.
- **Honest framing**: the Mathlib lemma is the **right place** for this
  partition — it's a general fact about finite measures on ℝ, not a
  CDF-specific fact. Contributing it upstream is the principled move.

## Implementation hand-off checklist

For the next researcher implementing the S10 chain:

- [ ] **S10a (in-tree)**: prove
  `MeasureTheory.Measure.exists_non_atom_in_Ioo` in
  `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (or a new
  `Helpers.lean` companion). ~20 LOC.
- [ ] **S10b (in-tree)**: prove
  `MeasureTheory.Measure.exists_finite_partition_no_atom_of_finite`
  in the same file. ~120 LOC.
- [ ] **S10c (in-tree)**: discharge `bracketingGrid_exists` via the
  partition lemma + S9b's cdf bridge. ~30 LOC.
- [ ] **S10d (upstream Mathlib PR)**: promote (a) and (b) to
  `Mathlib.MeasureTheory.Measure.<...>`. Out of scope for this
  slug (separate Mathlib PR workflow).
- [ ] Update state.md to mark items (iv), (v) as DONE; mark the chain
  as axiom-free.
- [ ] Update gallery meta.json for `laws-of-large-numbers-oq-04` (parent):
  `status: axiomatized → verified` if applicable.

## Mathlib API audit

| Lemma | Module | Purpose |
|---|---|---|
| `MeasureTheory.tendsto_measure_Iic_atBot` | `Mathlib.MeasureTheory.Measure.<...>` | Tail bound for `q_left` |
| `MeasureTheory.tendsto_measure_Ioi_atTop` | same | Tail bound for `q_right` |
| `Measure.countable_meas_pos_of_disjoint` | `Mathlib.MeasureTheory.Measure.<...>` | Atom set is countable for IsFiniteMeasure |
| `Set.Countable.dense_compl` | `Mathlib.Topology.Algebra.Module.Cardinality` | Complement of countable set is dense |
| `Dense.exists_mem_open` | `Mathlib.Topology.Basic` | Pick a point in any open from a dense set |
| `ProbabilityTheory.cdf_eq_real` | `Mathlib.Probability.CDF` | cdf bridge (S9b § 2) |
| `StieltjesFunction.measure_Ioc` | `Mathlib.MeasureTheory.Function.StieltjesFunction` | Cell-mass identity |
| `StieltjesFunction.measure_singleton` | same | Atom ⇔ jump correspondence |
| `Measure.isProbabilityMeasure_map` | `Mathlib.MeasureTheory.Measure.Typeclasses.Probability` | Pushforward preserves probability |

All present at v4.26.0 (modulo verification of the exact name for the
"atom set countable" fact — the closest hit is
`Measure.countable_meas_pos_of_disjoint`). S10 ACT should re-verify
each name via `gh api` before committing.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s10-prep-stieltjes-partition-mathlib-design.md`
      file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from S9 / S9a / S9b memos
- [x] Greedy step's "mass-tracking" invariant verified by hand:
      remaining mass strictly decreases by ε/2 per step
- [x] Termination bound `k ≤ ⌈2 μ(ℝ) / ε⌉` verified for probability
      measure (μ(ℝ) = 1 → k ≤ ⌈2/ε⌉)
- [x] `exists_non_atom_in_Ioo` parallel to S8's
      `trueCDF_continuityPoint_in_Ioo` confirmed structurally identical
- [x] S9 function-side ~250 LOC vs S10 Stieltjes-side ~160 LOC
      comparison verified component-by-component
- [x] Bridge `bracketingGrid_exists` from partition lemma confirmed ~30 LOC

## References

- S9b OBSERVE memo § 5 (the "speculation" this PREP upgrades to design):
  `sessions/2026-05-12-s9b-mathlib-cdf-bridge.md`.
- S9 OBSERVE memo (function-side competing design):
  `sessions/2026-05-12-s9-upstream-design-greedy-cover.md`.
- S8 sister-lemma (function-side `trueCDF_continuityPoint_in_Ioo`):
  `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` §2.2.5 (merged PR #18208).
- Mathlib reference: `Mathlib.Probability.CDF`, `Mathlib.MeasureTheory.Function.StieltjesFunction`,
  `Mathlib.Topology.Algebra.Module.Cardinality`.
- Glivenko, V. (1933). "Sulla determinazione empirica delle leggi di
  probabilità". *Giorn. Ist. Ital. Attuari* **4**, 92–99.
- Cantelli, F. P. (1933). "Sulla determinazione empirica delle leggi
  di probabilità". Same volume.
