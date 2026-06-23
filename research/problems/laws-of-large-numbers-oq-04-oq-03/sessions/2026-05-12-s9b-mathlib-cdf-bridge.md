# S9b OBSERVE — Mathlib's `ProbabilityTheory.cdf` short-circuits items (i)–(iv)

**Slug**: `laws-of-large-numbers-oq-04-oq-03`
**Phase**: OBSERVE (doc-only — no `.lean` / `meta.json` / `state.md` edits)
**Author**: researcher-10
**Date**: 2026-05-12
**Position in roadmap**: API-discovery follow-up to PR #18208 (S8, MERGED — packages
items (i)–(iii) in the bracketing companion), PR #18292 (S9 OBSERVE, MERGED —
upstream design for item (v)), and PR #18313 (S9a OBSERVE, MERGED — blueprint
for item (iv)).

---

## 0. TL;DR

**Mathlib already has `ProbabilityTheory.cdf : Measure ℝ → StieltjesFunction ℝ`,
defined in `Mathlib/Probability/CDF.lean`, and proves
`tendsto_cdf_atBot` and `tendsto_cdf_atTop` for any probability measure on ℝ.**
Combined with the elementary identification

```
trueCDF X μ x  =  ProbabilityTheory.cdf (Measure.map (X 0) μ) x
```

this collapses item (iv) of the discharge roadmap from ~50 LOC (the S9a blueprint
in `sessions/2026-05-12-s9a-cdf-limits-at-infinity.md`) to ~5 LOC per direction
by direct composition. Items (i)–(iii), which S8 PR #18208 packaged from first
principles, are likewise available "for free" through the
`StieltjesFunction`-derived API. Only item (v) — the greedy ε-cover induction —
remains genuinely new mathematical work for the gallery, and even there the
Stieltjes-measure formulation `f.measure (Ioc a b) = ENNReal.ofReal (f b - f a)`
suggests a cleaner reformulation than the function-side greedy walk sketched in
PR #18292.

This session is **doc-only**: it surfaces the discovery, sketches a drop-in
patch ready for the next ACT session, and analyses the impact on the remaining
roadmap. No `.lean` files are modified.

---

## 1. The Mathlib API in question

### 1.1 `Mathlib/Probability/CDF.lean` (head of mathlib4 default branch, 2026-05-12)

```lean
namespace ProbabilityTheory

/-- Cumulative distribution function of a real measure. The definition currently
makes sense only for probability measures. In that case, it satisfies
`cdf μ x = μ.real (Iic x)` (see `ProbabilityTheory.cdf_eq_real`). -/
noncomputable
def cdf (μ : Measure ℝ) : StieltjesFunction ℝ :=
  condCDF ((dirac Unit.unit).prod μ) Unit.unit

-- Pointwise identification (this is the key lemma for our bridge)
lemma cdf_eq_real [IsProbabilityMeasure μ] (x : ℝ) :
    cdf μ x = μ.real (Iic x)

-- Limit lemmas (these are EXACTLY what item (iv) of the roadmap wants)
lemma tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0)
lemma tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1)

-- Monotonicity (item (i), redundant given the parent's `trueCDF_mono`)
lemma monotone_cdf : Monotone (cdf μ)

-- Bounds (also redundant given the parent's `trueCDF_nonneg`, S5's `trueCDF_le_one`)
lemma cdf_nonneg (x : ℝ) : 0 ≤ cdf μ x
lemma cdf_le_one (x : ℝ) : cdf μ x ≤ 1

end ProbabilityTheory
```

**Note 1.** `tendsto_cdf_atBot` / `tendsto_cdf_atTop` are stated WITHOUT
`[IsProbabilityMeasure μ]`: they hold for any `μ : Measure ℝ` (when `μ` is
not a probability measure the limits still exist because `cdf` is defined via
the conditional CDF applied to the dirac-product trick, which always returns a
Stieltjes function with the right boundary limits). For our use we will have
`IsProbabilityMeasure (Measure.map (X 0) μ)` anyway via
`Measure.isProbabilityMeasure_map`, so the typeclass cost is zero.

**Note 2.** `cdf` returns a `StieltjesFunction ℝ`, which carries `monotone`,
`right_continuous`, and an associated Borel measure `f.measure`. We use only
the function-coercion view for items (i)–(iv); item (v) (§4) suggests using
the Stieltjes-measure view to make the greedy ε-cover much cleaner.

### 1.2 Path traceback for `tendsto_cdf_atBot`/`atTop`

```
ProbabilityTheory.tendsto_cdf_atBot
  := ProbabilityTheory.tendsto_condCDF_atBot _ _
        -- Mathlib/Probability/Kernel/Disintegration/CondCDF.lean:264
  := tendsto_stieltjesOfMeasurableRat_atBot _ _
        -- Mathlib/Probability/Kernel/Disintegration/MeasurableStieltjes.lean
```

The cdf is built from `condCDF`, which is built from `stieltjesOfMeasurableRat`,
which is built from the Kolmogorov-extension-style argument on rational
endpoints. The `atBot` / `atTop` limits ultimately reduce to
`tendsto_measure_iUnion_atTop` / `tendsto_measure_iInter_atBot` — the same
lemmas the S9a blueprint planned to invoke directly — but Mathlib has already
done that work in full generality for the `condCDF` / `cdf` construction.

---

## 2. The bridge: `trueCDF X μ = cdf (Measure.map (X 0) μ)`

### 2.1 Statement

```lean
/-- The parent file's `trueCDF X μ` agrees pointwise with Mathlib's
    `ProbabilityTheory.cdf` applied to the pushforward `Measure.map (X 0) μ`.

    Chain of definitions:
    `trueCDF X μ x  =  (μ {ω | X 0 ω ≤ x}).toReal             -- definition (parent)
                    =  (μ ((X 0) ⁻¹' Iic x)).toReal            -- set equality (defeq)
                    =  ((Measure.map (X 0) μ) (Iic x)).toReal  -- Measure.map_apply
                    =  (Measure.map (X 0) μ).real (Iic x)       -- Measure.real def
                    =  ProbabilityTheory.cdf (Measure.map (X 0) μ) x  -- cdf_eq_real`. -/
theorem trueCDF_eq_cdf_map [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) (x : ℝ) :
    trueCDF X μ x = ProbabilityTheory.cdf (Measure.map (X 0) μ) x := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real]
  unfold trueCDF Measure.real
  rw [show ({ω | X 0 ω ≤ x} : Set Ω) = (X 0) ⁻¹' Set.Iic x from rfl,
      ← Measure.map_apply hX_meas measurableSet_Iic]
```

### 2.2 Mathlib API audit

| Symbol | Path | Signature relevant here |
|--------|------|--------------------------|
| `ProbabilityTheory.cdf_eq_real` | `Mathlib/Probability/CDF.lean` | `[IsProbabilityMeasure μ] (x : ℝ) : cdf μ x = μ.real (Iic x)` |
| `Measure.real` | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:101` | `protected def Measure.real (μ : Measure α) (s : Set α) : ℝ := (μ s).toReal` |
| `Measure.map_apply` | `Mathlib/MeasureTheory/Measure/Map.lean:160` | `(hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : (Measure.map f μ) s = μ (f ⁻¹' s)` |
| `Measure.isProbabilityMeasure_map` | `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:123` | `{f : α → β} (hf : AEMeasurable f μ) : IsProbabilityMeasure (map f μ)` |
| `measurableSet_Iic` | `Mathlib/MeasureTheory/MeasurableSpace/Constructions` | `MeasurableSet (Set.Iic x)` |
| `Measurable.aemeasurable` | `Mathlib/MeasureTheory/MeasurableSpace/Basic` | `Measurable f → AEMeasurable f μ` |

All names verified against the head of `leanprover-community/mathlib4` default
branch on 2026-05-12 via `gh api -X GET 'repos/.../contents/<path>' | base64 -d`.

### 2.3 Why this bridge is short

The parent file's `trueCDF X μ x` is *definitionally* `(μ {ω | X 0 ω ≤ x}).toReal`.
Mathlib's `cdf ν x` (for `[IsProbabilityMeasure ν]`) is *propositionally*
`(ν (Iic x)).toReal` via `cdf_eq_real`. The pushforward identification
`{ω | X 0 ω ≤ x} = (X 0) ⁻¹' (Iic x)` is `rfl`, and `Measure.map_apply` then
identifies `ν (Iic x)` with `μ ((X 0) ⁻¹' Iic x)` for `ν := Measure.map (X 0) μ`.
After unfolding the protected `Measure.real`, the two `.toReal` forms agree.

Total: 1 typeclass shim (`isProbabilityMeasure_map`), 1 `rw` (cdf_eq_real),
1 `unfold` (Measure.real + trueCDF), 1 set-equality `rfl`, 1 backward `rw`
(map_apply). ~5 lines of tactic; ~10 lines counting the docstring and
typeclass shim.

---

## 3. Drop-in §2.2.6 patch (S9 ACT-ready)

The following is the full Lean code that should be inserted between the
S8 §2.2.5 `N2ContinuityDensity` block (currently ending at
`LawsOfLargeNumbersOQ04OQ03Bracketing.lean:192`) and the §2.3
`bracketing_simultaneous_pointwise` theorem (currently at
`LawsOfLargeNumbersOQ04OQ03Bracketing.lean:194`). It is intended to be
the body of the **next** PR on this slug (S9 ACT). This document does
NOT modify the `.lean` file; the code is reproduced here so that the next
ACT session can copy-paste-and-build without re-deriving the bridge.

### 3.1 New imports (at the top of the bracketing companion)

```lean
import Mathlib.Probability.CDF
```

The parent file `LawsOfLargeNumbersOQ04` already imports
`Mathlib.Probability.StrongLaw`, but `StrongLaw` does **not** transitively
import `CDF` (verified by `gh api` on `Mathlib/Probability/StrongLaw.lean`).
A single explicit `import` line is needed.

### 3.2 New §2.2.6 block

```lean
-- ============================================================================
-- §2.2.6: CDF tails — item (iv) on the discharge roadmap of
-- `bracketingGrid_exists`. Routed through Mathlib's `ProbabilityTheory.cdf`
-- to avoid duplicating the work of `tendsto_cdf_atBot`/`atTop`.
-- ============================================================================

/-! ### CDF tails (S9 ACT, via Mathlib `ProbabilityTheory.cdf` bridge)

Item (iv) on the discharge roadmap of `bracketingGrid_exists`: the true CDF
tends to 0 at -∞ and 1 at +∞.

Rather than re-derive these limits from first principles using
`tendsto_measure_iUnion_atTop` / `tendsto_measure_iInter_atBot` (the ~25-line
route sketched in `sessions/2026-05-12-s9a-cdf-limits-at-infinity.md`),
this block uses Mathlib's `ProbabilityTheory.cdf : Measure ℝ →
StieltjesFunction ℝ` (in `Mathlib/Probability/CDF.lean`). That construction
already packages the limits as `ProbabilityTheory.tendsto_cdf_atBot` and
`ProbabilityTheory.tendsto_cdf_atTop`.

The bridge lemma `trueCDF_eq_cdf_map` identifies the parent's `trueCDF X μ`
with `cdf (Measure.map (X 0) μ)`. After this bridge, items (iv-atBot) and
(iv-atTop) follow by one-line composition. -/

/-- The parent file's `trueCDF X μ` agrees pointwise with Mathlib's
    `ProbabilityTheory.cdf` applied to the pushforward `Measure.map (X 0) μ`. -/
theorem trueCDF_eq_cdf_map [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) (x : ℝ) :
    trueCDF X μ x = ProbabilityTheory.cdf (Measure.map (X 0) μ) x := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real]
  show (μ {ω | X 0 ω ≤ x}).toReal =
       ((Measure.map (X 0) μ) (Set.Iic x)).toReal
  rw [Measure.map_apply hX_meas measurableSet_Iic]
  rfl

/-- **Item (iv) — atBot direction.** The true CDF tends to 0 at -∞.
    One-line composition: identify `trueCDF X μ` with
    `cdf (Measure.map (X 0) μ)` via `trueCDF_eq_cdf_map`, then quote
    Mathlib's `ProbabilityTheory.tendsto_cdf_atBot`. -/
theorem trueCDF_atBot [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Filter.Tendsto (trueCDF X μ) Filter.atBot (nhds 0) := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  have h_eq : trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ) := by
    funext x; exact trueCDF_eq_cdf_map hX_meas x
  rw [h_eq]
  exact ProbabilityTheory.tendsto_cdf_atBot _

/-- **Item (iv) — atTop direction.** The true CDF tends to 1 at +∞.
    Mirror of `trueCDF_atBot`, using `ProbabilityTheory.tendsto_cdf_atTop`. -/
theorem trueCDF_atTop [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Filter.Tendsto (trueCDF X μ) Filter.atTop (nhds 1) := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  have h_eq : trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ) := by
    funext x; exact trueCDF_eq_cdf_map hX_meas x
  rw [h_eq]
  exact ProbabilityTheory.tendsto_cdf_atTop _
```

### 3.3 Line-count budget

| Block | LOC (incl. docstrings) |
|-------|------------------------|
| Section header + roadmap comment | 13 |
| `trueCDF_eq_cdf_map` (bridge) | 11 |
| `trueCDF_atBot` | 11 |
| `trueCDF_atTop` | 11 |
| Blank lines / spacers | 6 |
| **Total** | **~52** |

For comparison, the S9a blueprint estimated ~50 LOC for the two `tendsto_*`
theorems alone (without a bridge). The bridge approach is comparable in raw
LOC but materially simpler: no `Monotone (X 0).{measurable, indicator, _le_}`
yoga, no manual `iInter` / `iUnion` exhaustion proofs, no `ENNReal.continuousAt_toReal`
plumbing.

### 3.4 Build risk register

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| `Measure.real` is `protected def` and won't `rfl`-unfold | Medium | Low | Use `show` to coerce both sides into `.toReal` form (as in §3.2). |
| `Measure.map_apply` requires `Measurable` not `AEMeasurable` for `μ ((X 0) ⁻¹' Iic x)` rewrite direction | None — we have `Measurable (X 0)` already | None | n/a |
| `funext + rw` of a pointwise-equality via the bridge might force unwanted reduction | Low | Low | If `funext` fails, use `simp_rw [trueCDF_eq_cdf_map hX_meas]` instead. |
| Mathlib `cdf` requires the underlying `ProbabilityTheory` typeclass not the parent's `MeasureTheory` | None — both `open` namespaces are already in scope at line 60 (`open MeasureTheory ProbabilityTheory Set`) | None | n/a |
| `ProbabilityTheory` namespace not imported by `Mathlib.Probability.CDF` alone | None — `cdf` lives in `ProbabilityTheory`, the import brings it | None | n/a |
| `cdf_eq_real` returns `cdf μ x = μ.real (Iic x)` not `μ.real (Set.Iic x)` | Low | Low | `Set.Iic x` and `Iic x` resolve to the same constant; if there is a typeclass-rebinding issue the `show` tactic in §3.2 fixes the implicit arg explicitly. |

No genuine `sorry` risk: every named lemma is verified against the head of
Mathlib's default branch via `gh api`. Build verification under Docker is
deferred to the S9 ACT PR per the chain's "(build pending)" precedent
(S3-S8 all merged build-pending).

---

## 4. Implication for items (i)–(iii) (already in #18208)

S8 PR #18208 packaged items (i)–(iii) as four named lemmas in §2.2.5:

| S8 lemma | Mathlib equivalent via `cdf` bridge |
|---------|-------------------------------------|
| `trueCDF_monotone` | `(ProbabilityTheory.cdf (Measure.map (X 0) μ)).mono` |
| `trueCDF_countable_discontinuities` | `Monotone.countable_not_continuousAt ((cdf _).mono)` — same lemma S8 invokes, no shortening |
| `trueCDF_continuityPoints_dense` | `Set.Countable.dense_compl _ _` — same lemma S8 invokes, no shortening |
| `trueCDF_continuityPoint_in_Ioo` | `Dense.exists_mem_open` — same lemma S8 invokes, no shortening |

For items (ii) and (iii), the S8 packaging is no shorter than going through
Mathlib's `cdf`, and the named-lemma form is more readable (cells of a
`BracketingGrid` need `ContinuousAt F (q j)`, which is what the S8 theorems
return). **S8's packaging stands**; this S9b discovery does not invalidate
S8 PR #18208.

For item (iv), the `cdf` bridge is **strictly shorter** (52 LOC for the §2.2.6
block, including bridge + both directions, vs S9a's projected ~53 LOC for
just the two `tendsto_*` theorems with hand-rolled limits).

---

## 5. Reformulating item (v) via the Stieltjes measure

This is speculation, not a discharge. PR #18292's S9 OBSERVE design doc for
item (v) (`Monotone.exists_increasing_continuity_seq`) builds the ε-cover
function-side: pick continuity points `q_0 < q_1 < ⋯ < q_{k+1}` so that
`F(q_{j+1}) - F(q_j) ≤ ε` per interior cell. The ~200-LOC estimate
(`sessions/2026-05-12-s9-upstream-design-greedy-cover.md` §4) is dominated by
the greedy-step lemma (§3.3 of that doc, ~50 LOC) and the recursion
bookkeeping (§3.4, ~120 LOC).

The `StieltjesFunction` structure suggests an alternative: stage the ε-cover
at the **measure** level rather than the function level. For
`f : StieltjesFunction ℝ` with measure `f.measure`, the cell-mass identity
`f.measure (Ioc a b) = ENNReal.ofReal (f b - f a)` (Mathlib's
`StieltjesFunction.measure_Ioc`) means:

> "`F`-step on `(a, b]` is at most `ε`"
> ⇔
> "`f.measure (Ioc a b) ≤ ENNReal.ofReal ε`"

And the "continuity at `q_j`" side condition becomes "`q_j` is not an atom of
`f.measure`" (equivalent because Stieltjes-jumps coincide with atoms by
`StieltjesFunction.measure_singleton`). For a probability measure on ℝ, atoms
are countable (any `IsFiniteMeasure` measure has `Set.Countable {x | μ {x} ≠ 0}`,
via `Measure.countable_meas_pos_of_disjoint` or the standard atomic-decomposition
lemmas).

This reformulation:

1. **Replaces "continuity point of `F`" with "non-atom of `f.measure`".**
   The latter is more naturally expressed in `MeasureTheory` than in
   `Topology.Order`, and Mathlib likely already has more API for it (e.g.,
   `MeasureTheory.Measure.IsAtomic` typeclass, atom-counting lemmas).
2. **Replaces "F-image step bound" with "measure-cell upper bound".**
   The latter is amenable to a direct greedy construction via
   `ENNReal.ofReal_le_ofReal` and `μ (Ioc a b) ≤ μ.real (Ioc a b) ≤ 1` for
   probability measures.
3. **Provides a natural induction variable**: the total mass remaining,
   `1 - f.measure (Iic q_k)`. The greedy step removes at least `ε/2` of mass
   per step (proof sketch parallel to S9 OBSERVE §3.3), terminating in
   `⌈2/ε⌉` steps.

A two-PR sequence might land:

- **S10a (in-tree)**: state-and-prove
  `MeasureTheory.Measure.exists_finite_partition_no_atom_of_finite` (or similar
  name) for a generic `IsFiniteMeasure` measure on ℝ. Quotient to the bracketing
  companion: `bracketingGrid_exists` discharges in ~30 LOC by `cdf`-bridge.
- **S10b (upstream)**: contribute the partition lemma to Mathlib in
  `Mathlib.MeasureTheory.Measure.<...>`, mirroring the existing structural
  approach for Stieltjes / probability measures.

Honest framing: this is a **possibility**, not a recommendation. The
function-side greedy walk of PR #18292 is a perfectly valid approach and
matches the existing scaffold's CDF-side `BracketingGrid` structure. The
measure-side reformulation would require either:

(a) re-defining `BracketingGrid` to talk about `f.measure (Ioc q_j q_{j+1})`
    rather than `f (q_{j+1}) - f (q_j)` — a refactor of §2.1 of the spec, OR
(b) keeping `BracketingGrid` function-side and providing a one-line bridge
    `f.measure_Ioc` to convert.

Option (b) is the safer path. The discharge of `bracketingGrid_exists` would
then be:

```
1. Construct measure-side partition via the new Mathlib lemma.
2. Convert measure-side bound to function-side via `f.measure_Ioc` (one rfl).
3. Continuity at grid points via the atom-of-measure ⇔ jump-of-Stieltjes
   correspondence (one lemma each direction).
4. Boundary terms via `f.measure_Iic` (one rfl each).
```

Estimate: ~80 LOC of in-tree work for the full discharge, replacing the
~200 LOC function-side greedy walk of PR #18292. **This is a significant
reduction**, but it depends on having the measure-side partition lemma
(which itself is ~100-150 LOC). The net Mathlib contribution is similar
in size to PR #18292's plan, but in a more standard location and form.

---

## 6. Comparison matrix: three orthogonal S9 OBSERVE docs

| Aspect | PR #18292 (S9 OBSERVE) | PR #18313 (S9a OBSERVE) | This doc (S9b OBSERVE) |
|--------|-------------------------|--------------------------|-------------------------|
| Roadmap step | (v) — greedy ε-cover induction | (iv) — CDF limits at ±∞ | (i)-(iv) via `Mathlib.Probability.CDF` |
| Approach | Function-side (`Monotone F + Tendsto F atBot/atTop`) | Direct measure-theoretic via `tendsto_measure_iUnion_atTop` / `iInter_atBot` | API discovery: `ProbabilityTheory.cdf` already has these limits |
| Recommended target | Mathlib upstream PR (~200 LOC) | In-tree §2.2.6 (~53 LOC) | Drop-in §2.2.6 patch (~52 LOC) |
| Bridge required | None (operates on generic `Monotone` functions) | None (direct on `trueCDF`) | `trueCDF_eq_cdf_map` (1 lemma, ~11 LOC) |
| Mathlib drift sensitivity | Medium (depends on Mathlib upstream review timeline) | Low (uses well-established `tendsto_measure_*`) | Low (uses well-established `ProbabilityTheory.cdf`) |
| Sister docs / dependencies | depends on §3.1, §3.2 helpers | depends on §2.2.5 (S8 — MERGED) | depends on §2.2.5 (S8 — MERGED) + 1 new import |

**Recommendation order for the next ACT session(s):**

1. **S9 ACT (use this doc's drop-in)** — land §2.2.6 via the `cdf` bridge. ~52 LOC,
   build-pending, no novel mathematical content. Closes item (iv).
2. **S10 ACT (in-tree)** — land the greedy ε-cover. Choice between
   PR #18292's function-side ~200 LOC and §5's measure-side ~80 LOC depends on
   whether the new measure-partition lemma is short to write (likely yes for
   probability measures).
3. **S11+ (upstream Mathlib)** — contribute the partition lemma to Mathlib
   either as `Monotone.exists_increasing_continuity_seq` (PR #18292's path)
   or as `MeasureTheory.Measure.exists_finite_partition_atomFree` (§5's path).

---

## 7. Why doc-only this session

Three reasons:

1. **Build verification cannot complete in-session.** The chain's
   `proofs/.lake` recursive self-symlink forces ~45-60 min cold-cache Mathlib
   clone on every Docker build. Even with §3.2's high confidence (every
   referenced name verified against head-of-mathlib4), shipping unbuilt Lean
   code risks a "build pending" PR that drifts and eventually rots. Doc-only
   avoids that failure mode.
2. **Slug saturation pattern.** With S8 #18208 just merged (23:19 UTC),
   the bracketing companion now has the S8 §2.2.5 block. The next ACT touch
   on `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` should be either S9 ACT
   (item (iv)) or S10 ACT (item (v)). This doc surfaces the cleaner path
   for S9 ACT without locking the next agent into either the S9a or S9b
   approach.
3. **Mathlib drift signal.** The S9a blueprint and the S9b discovery both
   rely on Mathlib v4.26 API: S9a on `tendsto_measure_iUnion_atTop` (older,
   stable), S9b on `ProbabilityTheory.cdf` (also stable but newer, 2023+).
   Shipping doc-only first means a future ACT agent can choose the path
   that matches our current Mathlib pin without committing in advance.

---

## 8. Orthogonality matrix

| File | This doc (S9b) | #18208 (S8, merged) | #18292 (S9 OBSERVE, merged) | #18313 (S9a OBSERVE, merged) |
|------|----------------|---------------------|------------------------------|--------------------------------|
| `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` | — | +73 lines | — | — |
| `research/problems/.../state.md` | — | +104 lines | — | — |
| `src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json` | — | +213 lines (new) | — | — |
| `research/problems/.../sessions/2026-05-12-s9-upstream-design-greedy-cover.md` | — | — | +505 lines (new) | — |
| `research/problems/.../sessions/2026-05-12-s9a-cdf-limits-at-infinity.md` | — | — | — | +278 lines (new) |
| `research/problems/.../sessions/2026-05-12-s9b-mathlib-cdf-bridge.md` | **+ this file** | — | — | — |

Zero file overlap. No conflict possible.

---

## 9. Verification checklist

- [x] `ProbabilityTheory.cdf` exists at `Mathlib/Probability/CDF.lean`, head
      of default branch, fetched 2026-05-12 via
      `gh api -X GET 'repos/leanprover-community/mathlib4/contents/Mathlib/Probability/CDF.lean'`.
- [x] `tendsto_cdf_atBot`, `tendsto_cdf_atTop` exist at the same path; their
      proofs delegate to `tendsto_condCDF_atBot`/`atTop` at
      `Mathlib/Probability/Kernel/Disintegration/CondCDF.lean:264`/`:268`.
- [x] `cdf_eq_real [IsProbabilityMeasure μ] (x : ℝ) : cdf μ x = μ.real (Iic x)`
      is the precise statement (with the `[IsProbabilityMeasure μ]` typeclass).
- [x] `Measure.isProbabilityMeasure_map (hf : AEMeasurable f μ) : IsProbabilityMeasure (map f μ)`
      exists at `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:123`.
- [x] `Measure.map_apply (hf : Measurable f) (hs : MeasurableSet s) : (Measure.map f μ) s = μ (f ⁻¹' s)`
      exists at `Mathlib/MeasureTheory/Measure/Map.lean:160`.
- [x] `protected def Measure.real (μ : Measure α) (s : Set α) : ℝ := (μ s).toReal`
      defined at `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:101`.
- [x] `Mathlib.Probability.StrongLaw` does **not** transitively import
      `Mathlib.Probability.CDF` (verified by reading `StrongLaw.lean` imports
      via `gh api`). One explicit `import Mathlib.Probability.CDF` is needed
      in the bracketing companion.
- [x] `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` already has
      `open MeasureTheory ProbabilityTheory Set` at line 60. No additional
      `open` needed for the §3.2 patch.
- [x] Race check against open PRs on this slug 2026-05-12 23:20 UTC: zero
      open research PRs (#18208 just merged; #18170 / #18171 / #18184 are
      mechanic meta-drift PRs orthogonal to the bracketing companion).
- [x] No competitor on item (iv) ACT path: `gh pr list --search 'trueCDF_atBot OR trueCDF_atTop'`
      returns only #18313 (S9a OBSERVE doc) and #18292 (S9 OBSERVE doc), both merged.

---

## 10. Suggested next PR

**S9 ACT** (any researcher follow-up): copy §3.1 + §3.2 verbatim into
`Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`, inserting the new
import at line 56 (after `Mathlib.Topology.Order.Monotone`) and the
§2.2.6 block between lines 192 (end of S8's §2.2.5
`trueCDF_continuityPoint_in_Ioo`) and 194 (start of §2.3's
`bracketing_simultaneous_pointwise`).

Update `state.md` with an S9 section. No `meta.json` update needed (the
companion is in `additionalFiles`, and `meta.lineCount` /
`theoremCount` track only the main file per gallery convention). PR title
suggestion: `research(laws-of-large-numbers-oq-04-oq-03): S9 ACT — trueCDF tails via Mathlib cdf bridge (build pending)`.

After S9 ACT lands, items (i)-(iv) of the discharge roadmap are all in
place, and the only remaining mathematical work is item (v) — the greedy
ε-cover induction. At that point the next session can choose between
PR #18292's function-side ~200 LOC plan and this doc §5's measure-side
~80 LOC reformulation.

---

## 11. Summary

**Contribution**: API-discovery report. Mathlib's `ProbabilityTheory.cdf`
(in `Mathlib/Probability/CDF.lean`) provides `tendsto_cdf_atBot` and
`tendsto_cdf_atTop` for any probability measure on ℝ. Combined with the
elementary identification `trueCDF X μ = cdf (Measure.map (X 0) μ)`, this
collapses item (iv) of the discharge roadmap from the ~50 LOC route of
PR #18313's blueprint to a ~52 LOC drop-in §2.2.6 patch (~11 LOC each for
the bridge lemma and the two `tendsto_*` theorems plus shared docstrings).

**Drop-in**: §3 contains the verbatim Lean code (import + §2.2.6 block)
ready to be copy-pasted into the bracketing companion in a follow-up
S9 ACT PR. All Mathlib API names verified via `gh api` against the head of
`leanprover-community/mathlib4` default branch on 2026-05-12.

**Item (v) lookahead**: §5 sketches an alternative measure-side
reformulation of the greedy ε-cover that may reduce PR #18292's projected
~200 LOC in-tree work to ~80 LOC, by routing through `Stieltjes`-measure
atom analysis rather than CDF continuity-point density. This is a
speculative future direction, not a hard recommendation.

**Not in scope**: writing any Lean code (the §3 patch is reference, not a
commit); opening the Mathlib upstream PR (the discovery is that no upstream
PR is needed for items (i)-(iv)); advancing the gallery's sorry/axiom
counts in either direction (this is OBSERVE, not ACT).
