# Knowledge Base: fundamental-theorem-calculus-oq-01-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Targeted completion of the gallery proof `fundamental-theorem-calculus-oq-01`
(`proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean`, namespace `FTCLebesgue`).

Target: the Lebesgue FTC — an absolutely continuous `F : ℝ → ℝ` on `[a,b]` is
a.e. differentiable, `F'` is integrable, and `∫ₐᵇ F' = F b - F a`.

The file defines `AbsolutelyContinuousOn F a b` via the classical ε–δ
condition over finite families of pairwise-disjoint subintervals (disjointness
allows shared endpoints: `bs j ≤ as k ∨ bs k ≤ as j`).

### Current gaps in the parent file (as of 2026-05-28)

- **2 axioms**
  - `lebesgue_ftc_differentiable`: AC ⟹ a.e. differentiable on `(a,b)`.
  - `lebesgue_ftc_integral`: `∫ₐᵇ deriv F = F b - F a` (the deep result).
- **1 sorry**
  - `cantor_function_not_ac` (line ~224 originally): existence of a continuous,
    monotone `F` with `F 0 = 0`, `F 1 = 1`, `¬ AbsolutelyContinuousOn F 0 1`.

---

## Mathlib Infrastructure Assessment (2026-05-28)

NOTE: Mathlib source is not checked out on the host (the `proofs/.lake` symlink
is self-referential; Mathlib lives only inside the Docker build volume), so the
API names below are from knowledge and **must be confirmed at build time**
before being relied upon.

- **Function-level AC**: Mathlib has `MeasureTheory.Measure.AbsolutelyContinuous`
  (`μ ≪ ν`) for *measures*, but no ε–δ `AbsolutelyContinuousOn` for functions.
  Our definition genuinely fills this gap (candidate for upstreaming).
- **Bounded variation** (`Mathlib.Analysis.BoundedVariation`):
  - `eVariationOn f s : ℝ≥0∞` (iSup over finite monotone samplings).
  - `BoundedVariationOn f s := eVariationOn f s ≠ ⊤`; `LocallyBoundedVariationOn`.
  - Additivity over split intervals (`eVariationOn.Icc_add_Icc`-style).
  - Jordan-type decomposition: a `LocallyBoundedVariationOn` function is a
    difference of two monotone functions (`…exists_monotoneOn_sub_monotoneOn`).
  - a.e. differentiability of BV functions on ℝ
    (`LocallyBoundedVariationOn.ae_differentiableWithinAt`-style).
- **Monotone ⟹ a.e. differentiable**: `Monotone.ae_differentiableAt` (already
  used in the file as `monotone_ae_differentiable`); `MonotoneOn` variant.
- **Vitali / Lebesgue differentiation**: `VitaliFamily`,
  `VitaliFamily.ae_tendsto_measure_inter_div`; ℝ has a concrete Vitali family.
- **Stieltjes measures**: `StieltjesFunction` and its measure — relevant to the
  integral-recovery axiom via Radon–Nikodym (`Measure.rnDeriv`).
- **Cantor function**: no named Devil's-staircase construction appears to exist
  in Mathlib. Filling the `sorry` requires building it (or an equivalent
  singular monotone function) from scratch — substantial infrastructure.

---

## De-axiomatization Roadmap

### Linchpin lemma (next concrete target): AC ⟹ LocallyBoundedVariationOn

Elementary and self-contained mathematically:

1. Apply AC with `ε = 1` to obtain `δ > 0`.
2. Partition `[a,b]` into `N = ⌈(b-a)/δ⌉` consecutive subintervals, each of
   length `< δ`.
3. On a piece `[c,d]` with `d - c < δ`: for any monotone sampling
   `c ≤ u₀ ≤ … ≤ uₙ ≤ d`, the increment intervals `(uᵢ, uᵢ₊₁)` are
   pairwise disjoint (shared endpoints allowed) with total length
   `uₙ - u₀ ≤ d - c < δ`, so by AC `∑ |F(uᵢ₊₁) - F(uᵢ)| < 1`. Hence
   `eVariationOn F (Icc c d) ≤ 1`.
4. By additivity, `eVariationOn F (Icc a b) ≤ N < ⊤`.

Lean risk: requires the exact `eVariationOn` iSup characterization and
`Icc_add_Icc` additivity, plus ENNReal/`edist` bookkeeping
(`edist x y = ENNReal.ofReal |x - y|` on ℝ). Confirm names against Mathlib in a
build before committing.

### Then: AC ⟹ a.e. differentiable (removes `lebesgue_ftc_differentiable`)

`AC ⟹ LocallyBoundedVariationOn ⟹` (Mathlib) a.e. differentiable on `(a,b)`.
Upgrade `DifferentiableWithinAt` to `DifferentiableAt` on the open interior.

### Hardest: the integral identity (removes `lebesgue_ftc_integral`)

Likely path: monotone parts give `StieltjesFunction` measures; AC of `F` ⟺ its
Stieltjes measure `≪ volume`; `rnDeriv` equals `F'` a.e.; integrate to recover
`F b - F a`. Deep — defer until the differentiability axiom is discharged.

### The `sorry` (Cantor counterexample)

Lower priority (not needed for the FTC itself; it only certifies that AC is
*necessary*). Needs a from-scratch singular monotone function. No witness is
obviously easier to formalize than the standard Cantor function (all such
witnesses are singular / Cantor-like).

---

## Progress This Session (2026-05-28, researcher-1)

Added two verified, sorry-free lemmas to the parent file, strengthening the
proven AC theory and supplying a building block the Cantor statement needs:

- `ac_implies_continuousOn`: `AbsolutelyContinuousOn F a b ⟹ ContinuousOn F (Icc a b)`
  (packages the existing uniform-continuity lemma via `Metric.continuousOn_iff`).
- `ac_on_subinterval`: AC on `[a,b]` with `a ≤ c`, `d ≤ b` ⟹ AC on `[c,d]`
  (same `δ`; subintervals of `[c,d]` are subintervals of `[a,b]`).

These do not reduce the axiom/sorry count yet, but they extend the proven
regularity hierarchy (`Lipschitz → AC → ContinuousOn`, plus localization) and
set up the AC⟹BV linchpin.

---

## Insights

- Our AC disjointness condition (`bs j ≤ as k ∨ bs k ≤ as j`) permits touching
  endpoints, which is exactly what partition increments need — so the AC⟹BV
  argument applies cleanly without an extra strict-disjointness dodge.
- `ContinuousOn` (not just the ε–δ uniform statement) is the form downstream
  Mathlib lemmas and the Cantor statement consume; `ac_implies_continuousOn`
  bridges that gap.

---

## Dead Ends

None recorded yet.

---

## Session 2026-05-30 (researcher-1, SURVEY follow-up)

**Mode**: REVISIT
**Outcome**: discovery — linchpin lemma `ac_implies_bv` is **already proved**
in a sibling file. Documented the concrete discharge plan for
`lebesgue_ftc_differentiable`.

### Key Discovery

`proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean` (185 lines,
**0 sorries, 0 axioms**, gallery status `verified`) implements:

```
theorem FTCLebesgueACImpliesBV.ac_implies_bv
    {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    BoundedVariationOn F (Set.Icc a b)
```

This is exactly the AC ⟹ BV linchpin the previous session's roadmap
called out. **It is not currently imported by the parent file
`FundamentalTheoremCalculusLebesgue.lean`** — so the parent's
`lebesgue_ftc_differentiable` axiom remains live, even though the
prerequisite combinatorial step is now proved.

### Discharge Plan for `lebesgue_ftc_differentiable`

The chain `AC → BV → a.e. differentiable` is now half-done:
- **AC → BV**: proved (sibling file above).
- **BV → a.e. differentiable on `Icc`**: Mathlib provides this. The
  candidate API (to confirm in Docker build):
  - `BoundedVariationOn.ae_differentiableWithinAt_of_mem_Ici` (real line)
  - or its variant for `Icc`/`Ioo`.

**Sketch of the proof body** (to be type-checked under Docker; names
marked `‹›` are best-guess API placeholders):

```
theorem ac_implies_ae_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      volume (Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x := by
  have hbv : BoundedVariationOn F (Set.Icc a b) :=
    FTCLebesgueACImpliesBV.ac_implies_bv hab hF
  -- Mathlib: BV on Icc gives a.e. DifferentiableWithinAt on Icc.
  have hae : ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      DifferentiableWithinAt ℝ F (Set.Icc a b) x :=
    ‹BoundedVariationOn.ae_differentiableWithinAt› hbv
  -- Move from DifferentiableWithinAt on Icc to DifferentiableAt on Ioo
  -- (interior of Icc): on Ioo, the within-derivative agrees with the
  -- full derivative via `DifferentiableWithinAt.differentiableAt`
  -- with `mem_nhds_of_mem_Ioo`/`Ioo_mem_nhds`.
  ...
  refine ⟨S, hS_meas, ?_, ?_⟩
  · -- volume (Ioo a b \ S) = 0
    ...
  · intro x hx
    exact ‹upgrade DifferentiableWithinAt → DifferentiableAt at interior point›
```

The remaining work is ~30–60 lines plus API verification. Two risks:
1. Mathlib's actual name for the BV-a.e.-diff result may differ from
   the guess; need to grep `BoundedVariation` in Mathlib at build time.
2. The within-vs-full derivative bridge on `Ioo` requires
   `DifferentiableWithinAt.differentiableAt` plus the open-neighborhood
   characterization of `Ioo`.

### What This Session Did NOT Do

- No new Lean code written (Docker not run; Mathlib API not directly
  verifiable from worktree).
- Did not modify the parent file. The `lebesgue_ftc_differentiable`
  axiom and the Cantor `sorry` are unchanged.

### Recommended Next Session

1. **Docker-build the parent unchanged** to bank a clean baseline.
2. Add `import Proofs.FundamentalTheoremCalculusLebesgueOQ01` to the parent.
3. Replace the `axiom lebesgue_ftc_differentiable` with the theorem
   sketched above, using actual Mathlib API names verified by grepping
   the docker volume's mathlib sources.
4. Build. Iterate on API names until green.
5. Expected delta: 2 axioms → 1 axiom, 0 sorries change. Update
   `meta.json`: `axiomCount: 2` → `1`, status remains `axiomatized`
   (the `lebesgue_ftc_integral` axiom is still present).

### Files Modified

- `research/problems/fundamental-theorem-calculus-oq-01-incomplete-01/knowledge.md` — this entry
