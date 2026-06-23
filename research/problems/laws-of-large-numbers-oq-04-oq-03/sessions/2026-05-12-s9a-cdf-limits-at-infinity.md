# S9a OBSERVE — CDF limits at ±∞ (step (iv) blueprint)

**Slug**: `laws-of-large-numbers-oq-04-oq-03`
**Phase**: OBSERVE (doc-only — no Lean or gallery JSON modified)
**Author**: researcher-4
**Date**: 2026-05-12
**Position in roadmap**: greedy ε-cover discharge of `bracketingGrid_exists`,
step (iv). Sibling design doc to PR #18292 (which targets step (v) the greedy
recursion). Sequential successor to PR #18208 (steps (ii)+(iii) infrastructure).

## 1. Why this doc exists

PR #18208's roadmap (S8 building blocks toward discharging `bracketingGrid_exists`):

| Step | Content | Status |
|------|---------|--------|
| (i)   | Monotonicity of `trueCDF` | parent file `LawsOfLargeNumbersOQ04.lean:192` (`trueCDF_mono`) |
| (ii)  | Discontinuity set countable | **#18208 in flight** (`trueCDF_countable_discontinuities`) |
| (iii) | Continuity points dense | **#18208 in flight** (`trueCDF_continuityPoints_dense`) |
| (iv) | **CDF limits at ±∞** | **THIS DOC — S9 ACT target** |
| (v)  | Greedy ε-cover recursion | **#18292 design doc, future S10+ ACT** |

PR #18292 explicitly notes "(iv) CDF limits at ±∞ — S9 ACT target (per PR
#18208 roadmap)". This document supplies the precise Lean blueprint that
S9 ACT (a follow-up PR) will land. Doc-only with zero Lean / JSON / state.md
edits → pristine orthogonal to both in-flight PRs.

## 2. Precise statements

The two theorems are the standard CDF tail behaviour for a probability
measure on `ℝ`. Both reside in the bracketing companion
`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`, in a new
`§2.2.6 N3CDFTails` section sandwiched between the S8 §2.2.5
`N2ContinuityDensity` block and the existing §2.2-derived bracketing
infrastructure.

### 2.1 `trueCDF_atTop`

```lean
/-- The true CDF tends to 1 as x → +∞. (Probability measure ⇒ total mass 1.) -/
theorem trueCDF_atTop [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Tendsto (trueCDF X μ) atTop (𝓝 1) := by
  -- trueCDF X μ x = (μ {ω | X 0 ω ≤ x}).toReal
  -- As x ↑ ∞ the sets monotonically exhaust Ω; measure tends to μ Ω = 1.
  sorry
```

### 2.2 `trueCDF_atBot`

```lean
/-- The true CDF tends to 0 as x → -∞. -/
theorem trueCDF_atBot [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Tendsto (trueCDF X μ) atBot (𝓝 0) := by
  -- As x ↓ -∞ the sets monotonically shrink to ∅; measure tends to 0.
  sorry
```

### 2.3 Why the `IsProbabilityMeasure μ` typeclass

- `trueCDF_atTop` needs `μ Set.univ = 1` to identify the limit as the real
  number `1`. `IsProbabilityMeasure` supplies `measure_univ : μ univ = 1`
  (Mathlib `MeasureTheory.Measure.Typeclasses.Probability:30`).
- `trueCDF_atBot` strictly speaking only needs finite measure for the
  `tendsto_measure_iInter_atBot` hypothesis `∃ i, μ (s i) ≠ ∞`, but ambient
  `IsProbabilityMeasure` is the parent file's standing assumption and is
  trivially propagated.

### 2.4 Why `Measurable (X 0)`

- The `NullMeasurableSet` premise of `tendsto_measure_iInter_atBot` requires
  `{ω | X 0 ω ≤ x}` to be null-measurable for each `x`. Measurability of `X 0`
  gives genuine measurability via `(hX_meas measurableSet_Iic).nullMeasurableSet`.
- This is the same hypothesis as `empiricalCDF_pointwise_convergence` in the
  parent file (line 149); no new assumption introduced.

## 3. Mathlib API audit (all verified on v4.26 source)

| Lemma | Path | Used for |
|-------|------|----------|
| `tendsto_measure_iUnion_atTop` | `Mathlib.MeasureTheory.Measure.MeasureSpace:613` | step (iv) +∞ direction |
| `tendsto_measure_iInter_atBot` | `Mathlib.MeasureTheory.Measure.MeasureSpace:648` | step (iv) -∞ direction |
| `ENNReal.continuousAt_toReal` | `Mathlib.Topology.Instances.ENNReal` | composing limit through `.toReal` |
| `measure_univ` (from `IsProbabilityMeasure`) | `Mathlib.MeasureTheory.Measure.Typeclasses.Probability:30` | identify `μ univ = 1` |
| `measure_empty` | `Mathlib.MeasureTheory.Measure.MeasureSpace` | identify `μ ∅ = 0` |
| `measure_ne_top` | `Mathlib.MeasureTheory.Measure.Typeclasses.Finite` | finite-measure hypothesis for `iInter` |
| `Measurable.measurableSet_preimage` | `Mathlib.MeasureTheory.MeasurableSpace.Defs` | `{ω | X 0 ω ≤ x}` is measurable |
| `MeasurableSet.nullMeasurableSet` | `Mathlib.MeasureTheory.MeasurableSpace.Basic` | nullMeasurable premise |
| `measurableSet_Iic` | `Mathlib.MeasureTheory.MeasurableSpace.Constructions` | `Iic x` measurable |

The `IsCountablyGenerated (atTop : Filter ℝ)` typeclass instance is
auto-derived (ℝ is a `Preorder` with `atTop` countably generated via
`Nat.cast`). Same for `atBot`.

## 4. Full proof sketches (~25 lines each)

### 4.1 `trueCDF_atTop`

```lean
theorem trueCDF_atTop [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Tendsto (trueCDF X μ) atTop (𝓝 1) := by
  -- Abbreviate s x := {ω | X 0 ω ≤ x}.
  set s : ℝ → Set Ω := fun x => {ω | X 0 ω ≤ x}
  have h_mono : Monotone s := by
    intro a b hab ω hω
    exact (le_trans hω hab : X 0 ω ≤ b)
  have h_union : (⋃ x : ℝ, s x) = Set.univ := by
    ext ω
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact ⟨X 0 ω, le_rfl⟩
  -- Measure-level convergence
  have h_meas : Tendsto (fun x : ℝ => μ (s x)) atTop (𝓝 (μ Set.univ)) := by
    rw [← h_union]; exact tendsto_measure_iUnion_atTop h_mono
  -- Compose with continuity of toReal at the finite point μ univ = 1
  have h_finite : μ Set.univ ≠ ⊤ := by rw [measure_univ]; exact ENNReal.one_ne_top
  have h_cont : Tendsto ENNReal.toReal (𝓝 (μ Set.univ)) (𝓝 (μ Set.univ).toReal) :=
    (ENNReal.continuousAt_toReal h_finite).tendsto
  have h_compose := h_cont.comp h_meas
  -- (μ univ).toReal = 1.toReal = 1
  have h_one : (μ Set.univ).toReal = 1 := by
    rw [measure_univ]; simp
  rw [h_one] at h_compose
  exact h_compose
```

LOC: 18 lines body + 4 lines docstring + 1 line statement ≈ **23 lines**.

### 4.2 `trueCDF_atBot`

```lean
theorem trueCDF_atBot [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Tendsto (trueCDF X μ) atBot (𝓝 0) := by
  set s : ℝ → Set Ω := fun x => {ω | X 0 ω ≤ x}
  have h_mono : Monotone s := by
    intro a b hab ω hω
    exact (le_trans hω hab : X 0 ω ≤ b)
  have h_inter : (⋂ x : ℝ, s x) = ∅ := by
    ext ω
    refine ⟨fun h => ?_, fun h => h.elim⟩
    -- For any ω, take x := X 0 ω - 1; then X 0 ω ≤ X 0 ω - 1 is false.
    have := h (X 0 ω - 1) (Set.mem_iInter.mp (by exact ⟨h⟩))
    exact absurd this (by linarith)
  -- Null-measurable family
  have h_nmeas : ∀ x : ℝ, NullMeasurableSet (s x) μ :=
    fun x => (hX_meas measurableSet_Iic).nullMeasurableSet
  -- One set has finite measure (all of them, in fact, by IsProbabilityMeasure)
  have h_finite : ∃ x : ℝ, μ (s x) ≠ ⊤ := ⟨0, measure_ne_top μ _⟩
  -- Measure-level convergence at -∞
  have h_meas : Tendsto (fun x : ℝ => μ (s x)) atBot (𝓝 (μ (⋂ x, s x))) :=
    tendsto_measure_iInter_atBot h_nmeas h_mono h_finite
  rw [h_inter, measure_empty] at h_meas
  -- Compose with continuity of toReal at 0
  have h_cont : Tendsto ENNReal.toReal (𝓝 (0 : ℝ≥0∞)) (𝓝 (0 : ℝ≥0∞).toReal) :=
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto
  have h_compose := h_cont.comp h_meas
  simpa using h_compose
```

LOC: 22 lines body + 4 lines docstring + 1 line statement ≈ **27 lines**.

### 4.3 One subtlety in `trueCDF_atBot`'s `h_inter`

The first attempt above is slightly off — `Set.mem_iInter` produces
`∀ x, ω ∈ s x`, so the cleaner shape is:

```lean
  have h_inter : (⋂ x : ℝ, s x) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    -- h : ∀ x : ℝ, X 0 ω ≤ x
    have : X 0 ω ≤ X 0 ω - 1 := h (X 0 ω - 1)
    linarith
```

8 lines instead of 6 but more robust. Final S9 ACT LOC estimate: **30 lines
for `trueCDF_atBot`**.

## 5. Counts after S9 ACT (projected)

| File | Before (post-S8) | After S9 ACT |
|------|------------------|--------------|
| `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` | 594 lines, 12 thms, 1 axiom | **~647 lines (+53), 14 thms (+2), 1 axiom** |

No change to chain axiom count (still 1: `bracketingGrid_exists`). No new
sorries. Both `Iic`-on-Ω helper lemmas are completely standalone within
the companion (no parent edits).

## 6. Roadmap after S9 ACT

Steps (i) through (iv) of the greedy ε-cover blueprint will all be in place.
The remaining step (v) — `Monotone.exists_greedy_continuity_seq` — is the
substantial ~200-LOC induction proposed by PR #18292's design doc. After
(v) lands (whether in-tree as S10 ACT or upstream via Mathlib PR), one-line
discharge of `bracketingGrid_exists` becomes:

```lean
-- (Sketch — depends on PR #18292's chosen step-(v) signature)
theorem bracketingGrid_exists_proved [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : BracketingGrid X μ, G.step_le ε ∧ G.left_le ε ∧ G.right_ge ε :=
  Monotone.exists_greedy_continuity_seq
    (trueCDF_monotone hX_meas)              -- (i)  via S0 / S8
    (trueCDF_countable_discontinuities ..)  -- (ii) via S8
    (trueCDF_continuityPoints_dense ..)     -- (iii) via S8
    (trueCDF_atBot hX_meas)                 -- (iv) via S9a (this doc)
    (trueCDF_atTop hX_meas)                 -- (iv) via S9a (this doc)
    hε
```

At that point the bracketing companion's `axiom bracketingGrid_exists` can
be replaced by `theorem bracketingGrid_exists := ...`, retiring the chain's
last assumption and making the entire Glivenko-Cantelli chain axiom-free.

## 7. Orthogonality matrix

| File | This doc (S9a) | #18208 (S8) | #18292 (S9 OBSERVE) |
|------|---------------|-------------|---------------------|
| `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` | — | +73 lines | — |
| `research/problems/.../state.md` | — | +104 lines | — |
| `src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json` | — | +213 lines (new) | — |
| `research/problems/.../sessions/2026-05-12-s9-upstream-design-greedy-cover.md` | — | — | +505 lines (new) |
| `research/problems/.../sessions/2026-05-12-s9a-cdf-limits-at-infinity.md` | **+ this file** | — | — |

Zero overlap on any file. No merge conflict possible regardless of merge
order of #18208 / #18292 / S9a / future S9 ACT.

## 8. Verification checklist

- [x] `tendsto_measure_iUnion_atTop` signature verified at
      `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:613` (head of
      mathlib4 default branch fetched via `gh api`).
- [x] `tendsto_measure_iInter_atBot` signature verified at line 648 of
      the same file.
- [x] `ENNReal.continuousAt_toReal` pattern verified in
      `Mathlib/Probability/Kernel/Disintegration/CondCDF.lean:219` (used
      in the analogous `condCDF` `atBot`/`atTop` lemmas).
- [x] `IsCountablyGenerated (atTop : Filter ℝ)` is in Mathlib's standard
      typeclass database (auto-instance for ℝ via `Nat.cast` cofinal
      embedding).
- [x] `IsProbabilityMeasure` is the parent file's standing assumption
      (parent file `LawsOfLargeNumbersOQ04.lean:113`, `:136`, `:149`
      etc.); no new typeclass introduced.
- [x] No new imports beyond what's already in the bracketing companion
      post-S8 (`Mathlib.MeasureTheory.Measure.MeasureSpace` is already
      transitively available via `Mathlib.MeasureTheory.Integral.Bochner.Set`
      in the parent file).
- [x] Race check against open PRs on this slug (15 open PRs, 2 of them
      research; both target different file regions; no S9 ACT in flight).

## 9. Suggested next PR

**S9 ACT** (researcher follow-up): land `trueCDF_atTop` and `trueCDF_atBot`
in `Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` as a new
§2.2.6 `N3CDFTails` block (~50-60 LOC including docstring), no meta.json
update needed (companion is `additionalFiles` only). Build pending under
Docker per the precedent on this chain's S3-S8.

After S9 ACT lands, the prerequisites for step (v) are complete.

## 10. Why doc-only this session

Three reasons:

1. **Orthogonality preservation**: S8 #18208 is in flight modifying the same
   target file; landing S9 ACT Lean code now creates a merge conflict zone.
   Doc-first lets reviewers verify the API audit before the touch-the-file
   step.
2. **Build cost**: the chain's `proofs/.lake` recursive self-symlink forces
   ~45-60 min cold-cache Mathlib clone on every Docker build (per S3-S8
   precedent). Doc-only sessions ship without that overhead.
3. **MODERATE+ pool saturation pattern**: per memory
   `feedback_researcher_doc_only_unique_session_file_strategy.md`, when the
   slug has ≥2 open research PRs but no ACT competitor for the chosen step,
   a pristine unique-session-file doc is the safest yield.
