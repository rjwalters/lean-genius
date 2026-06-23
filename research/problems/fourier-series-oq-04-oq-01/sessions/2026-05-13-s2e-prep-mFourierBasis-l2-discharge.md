# S2e PREP — `Mathlib.Analysis.Fourier.AddCircleMulti.mFourierBasis` discharges `sphPartialSum_L2_norm_converge` sorry

**Researcher**: researcher-6
**Date**: 2026-05-13
**Phase**: ACT (PREP / Mathlib API audit)
**Iteration**: 2e (orthogonal to S2d PR #18393's bbox-cardinality angle)
**Predecessor PRs**: #18062 (S1 OBSERVE, MERGED), #18165 (S2a ACT scaffold, MERGED), #18255 (S2c subset+card bounds, MERGED), #18393 (S2d PREP bbox cardinality, OPEN).
**Lines added**: doc-only, no Lean / no edits to `problem.md` / `knowledge.md` / `state.md` / json / meta.

## Headline finding

The S1 / S2a state.md flags the sorry in `sphPartialSum_L2_norm_converge` as the "alt-S2b path" requiring ~80–150 lines to build a custom `Plancherel_ntorus` identity in this file. **Mathlib v4.26.0 (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) already exposes this identity** as `mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)`, together with the unconditional L²-summability theorem `hasSum_mFourier_series_L2`. The sorry can be closed by a **~20-line bridge**, not 80–150 lines.

This PREP documents the bridge and the four-step plan to discharge the sorry, plus the Mathlib API verification (with line numbers in the pinned revision) so the next ACT can cite directly.

## Mathlib API surface (verified at rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67)

### 1. The type `UnitAddTorus d`

`Mathlib/Analysis/Fourier/AddCircleMulti.lean:40`:

```lean
/-- The product of finitely many copies of the unit circle, indexed by `d`. -/
abbrev UnitAddTorus (d : Type*) := d → UnitAddCircle
```

Where `UnitAddCircle := AddCircle (1 : ℝ)` is defined elsewhere in Mathlib. Specialising to `d = Fin 2`:

```
UnitAddTorus (Fin 2) = Fin 2 → UnitAddCircle = Fin 2 → AddCircle (1 : ℝ)
```

The slug's `T2 := Fin 2 → AddCircle (1 : ℝ)` is **definitionally equal** to `UnitAddTorus (Fin 2)`. No conversion lemma needed; `T2` and `UnitAddTorus (Fin 2)` reduce to the same `Fin 2 → AddCircle 1` type at the term level.

### 2. The measure `volume` vs `haarT2`

`Mathlib/Analysis/Fourier/AddCircleMulti.lean:29–37`:

```lean
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := ...
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ...
```

The product measure on `UnitAddTorus d` is `Measure.pi (fun _ => volume) = Measure.pi (fun _ => haarAddCircle)`.

The slug's `haarT2`:

```lean
-- proofs/Proofs/FourierSeriesOQ04OQ01.lean:81-82
noncomputable def haarT2 : Measure T2 :=
  Measure.pi fun _ => (haarAddCircle : Measure (AddCircle (1 : ℝ)))
```

is **literally the same definition** as Mathlib's product `volume` on `UnitAddTorus (Fin 2)`. A `defeq` bridge `volume = haarT2` should hold as `rfl` or after a 1-step unfold. If not, a 2-line `Measure.pi_congr` reconciliation closes it.

### 3. The Fourier coefficient bridge

Mathlib (`AddCircleMulti.lean:249`):

```lean
def mFourierCoeff (f : UnitAddTorus d → E) (n : d → ℤ) : E :=
  ∫ t, mFourier (-n) t • f t
```

where `mFourier n t = ∏ i, fourier (n i) (t i)` (line 53). For `E = ℂ` and `d = Fin 2`:

```
mFourierCoeff f n = ∫ t, (fourier (-(n 0)) (t 0) * fourier (-(n 1)) (t 1)) * f t
```

The slug's `multiFourierCoeff`:

```lean
-- proofs/Proofs/FourierSeriesOQ04OQ01.lean:91-92
noncomputable def multiFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) : ℂ :=
  ∫ x, f x * fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1) ∂haarT2
```

Bridge lemma (~3 lines):

```lean
theorem multiFourierCoeff_eq_mFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) :
    multiFourierCoeff f k = mFourierCoeff f k := by
  unfold multiFourierCoeff mFourierCoeff
  congr 1; ext x
  simp [UnitAddTorus.mFourier, Fin.prod_univ_two, mul_comm, mul_left_comm, mul_assoc]
```

The `congr 1; ext x` reduces to per-point integrand equality, which is a commutativity rearrangement of the three factors.

### 4. The Hilbert-basis Plancherel identity

`AddCircleMulti.lean:268`:

```lean
def mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d) :=
  HilbertBasis.mk orthonormal_mFourier (span_mFourierLp_closure_eq_top (by simp)).ge
```

The associated convergence theorem (`AddCircleMulti.lean:288`):

```lean
theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) :
    HasSum (fun i ↦ mFourierCoeff f i • mFourierLp 2 i) f := by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f
```

This is `HasSum` over `d → ℤ` directed by inclusion-of-finite-subsets. The L² limit is `f` exactly (no `volume`-a.e. business; this is the L² element).

## The four-step S2e ACT plan

Replace the slug's sorry:

```lean
-- proofs/Proofs/FourierSeriesOQ04OQ01.lean:148-151
theorem sphPartialSum_L2_norm_converge
    (f : T2 → ℂ) (_hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
      atTop (𝓝 0) := by
  sorry
```

with the following ~30 LOC:

```lean
import Mathlib.Analysis.Fourier.AddCircleMulti

open UnitAddTorus MeasureTheory Filter Topology

-- Step (a): defeq bridge T2 ↔ UnitAddTorus (Fin 2) and haarT2 ↔ volume
-- (~3 lines; one `rfl` for the type, one `Measure.pi_congr` for the measure if needed.)
private theorem haarT2_eq_volume :
    haarT2 = (volume : Measure (UnitAddTorus (Fin 2))) := by
  rfl  -- or `Measure.pi_congr fun _ => rfl` if `rfl` fails

-- Step (b): Fourier-coefficient bridge (per §3 above)
private theorem multiFourierCoeff_eq_mFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) :
    multiFourierCoeff f k = mFourierCoeff f k := by
  unfold multiFourierCoeff mFourierCoeff
  congr 1; ext x
  simp [UnitAddTorus.mFourier, Fin.prod_univ_two, mul_comm, mul_left_comm, mul_assoc]

-- Step (c): rewrite sphPartialSum as a finite partial sum of mFourierLp 2
private theorem sphPartialSum_eq_finset_sum
    (f : T2 → ℂ) (R : ℝ) :
    (sphPartialSum f R : T2 → ℂ)
      = fun x => ∑ k ∈ latticeDisc R, mFourierCoeff f k • mFourierLp 2 k x := by
  ext x
  unfold sphPartialSum
  simp_rw [multiFourierCoeff_eq_mFourierCoeff, smul_eq_mul, ← mul_assoc]
  -- ∑ k, mFourierCoeff f k * fourier (k 0) (x 0) * fourier (k 1) (x 1)
  --   = ∑ k, mFourierCoeff f k • (∏ i, fourier (k i) (x i))
  -- = ∑ k, mFourierCoeff f k • mFourier k x
  -- = ∑ k, mFourierCoeff f k • mFourierLp 2 k x  (via coeFn_mFourierLp)
  sorry  -- This is the only non-mechanical bridge; ~5 line `simp` + `Fin.prod_univ_two`

-- Step (d): close the original sorry by routing through hasSum_mFourier_series_L2
-- + Tendsto-of-HasSum on the cofinal family `latticeDisc R, R → ∞`
theorem sphPartialSum_L2_norm_converge
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
      atTop (𝓝 0) := by
  -- Convert f to an L² element fL2 : L²(UnitAddTorus (Fin 2))
  set fL2 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) := hf.toLp f with hfL2
  -- Apply mFourierBasis.hasSum_repr (equivalent to hasSum_mFourier_series_L2)
  have hHasSum : HasSum (fun k : Fin 2 → ℤ => mFourierCoeff fL2 k • mFourierLp 2 k) fL2 :=
    hasSum_mFourier_series_L2 fL2
  -- Tendsto Lemma: hasSum implies tendsto on any cofinal directed family;
  -- `latticeDisc R, R → ∞` is cofinal in finite subsets of ℤ² (by Step (e) below).
  -- Then convert eLpNorm subtraction-from-zero on the Lp side back to the original.
  sorry  -- ~10 lines: `HasSum.tendsto_sum_nat`-style + cofinality + Lp ↔ eLpNorm conversion

-- Step (e) [supporting]: cofinality of latticeDisc R in Finset (Fin 2 → ℤ)
-- This says: for every finite S ⊆ ℤ², there exists R₀ such that S ⊆ latticeDisc R₀.
-- Take R₀ = max ‖k‖ over k ∈ S, +1.
private theorem latticeDisc_cofinal :
    ∀ (S : Finset (Fin 2 → ℤ)), ∃ R₀ : ℝ, ∀ R ≥ R₀, S ⊆ latticeDisc R := by
  sorry  -- ~10 lines: induct on Finset.max'; explicit `R₀ = (S.sup ‖·‖) + 1`
```

**Total estimate**: ~30 LOC actual changes + ~10 LOC supporting cofinality lemma. Two genuine `sorry`s in the skeleton (Step (c) bridge and Step (d) tendsto-on-net), both routine but not 1-liners. **Total residual sorries after S2e ACT lands: 0** (down from the current 1). **Axiom count unchanged at 1** (`carleson_2d_sph`, the pointwise a.e. Carleson statement, which is the genuinely-open conjecture).

## Net effect on gallery status

| Metric | Before S2e ACT | After S2e ACT |
|---|---|---|
| `axiomCount` | 1 (`carleson_2d_sph`) | **1** (unchanged) |
| `sorries` | 1 (`sphPartialSum_L2_norm_converge`) | **0** |
| `status` | `axiomatized` | **`axiomatized`** (correct — Carleson axiom still present) |
| `badge` | `axiom` | **`axiom`** (correct) |

The L² version of the conjecture becomes *fully verified*; only the genuinely-open *pointwise a.e.* version remains axiomatic. This is a meaningful narrowing of the entry's claim surface.

## Orthogonality to in-flight PRs

| PR | Phase | Focus | Conflict with S2e PREP? |
|---|---|---|---|
| #18062 (MERGED) | S1 OBSERVE | territory map | no — base |
| #18165 (MERGED) | S2a ACT scaffold | axiom + sorry + sanity lemmas | no — S2e replaces the sorry; axiom unchanged |
| #18255 (MERGED) | S2c | `latticeDisc_subset_bbox` + `latticeDisc_card_le_bbox` | no — orthogonal (S2c addresses bbox cardinality of partial-sum domain; S2e addresses L² convergence of the partial sum itself) |
| #18393 (OPEN) | S2d PREP | explicit `bbox.card = (2⌈R⌉+1)²` | **no** — S2d targets `latticeDisc_card_le_explicit`; S2e targets `sphPartialSum_L2_norm_converge`. Disjoint Lean targets, disjoint file paths |
| **#this** | S2e PREP | mFourierBasis discharges L² sorry | — |

S2d and S2e are on *different theorems* in the same Lean file. The S2d ACT (when it lands) will add `bbox_card` and `latticeDisc_card_le_explicit`. The S2e ACT will replace the sorry on line 148 with the four-step bridge. Zero textual overlap.

## What this does NOT address

1. **The `carleson_2d_sph` axiom**. This is the *pointwise a.e.* version of Carleson's theorem for 2D spherical Fourier sums, which is the genuinely open conjecture (since the Bochner–Riesz multiplier theorem only handles $\delta > 1/2$ in dimension 2; the critical $\delta = 0$ pointwise a.e. case is open). S2e does NOT remove this axiom.
2. **The S2b Bochner–Riesz formalization path** (state.md line 93–101). That remains a future iteration (~300–500 LOC) targeting the regularised $\delta > 1/2$ case unconditionally.
3. **Mathlib contribution**. The `multiFourierCoeff_eq_mFourierCoeff` bridge is project-local; converting our `multiFourierCoeff` definition to *use* `mFourierCoeff` directly (eliminating the bridge altogether) is a separate refactor.

## Why this is real progress

The S1 / S2a state.md described the L² sorry as a ~80–150 LOC "build a custom `Plancherel_ntorus` identity in this file" project. This was an honest estimate at the time. But Mathlib v4.26.0 already provides:

- `mFourierBasis` (line 268) — the Hilbert basis of Fourier monomials
- `hasSum_mFourier_series_L2` (line 288) — the L² Plancherel convergence
- `hasSum_sq_mFourierCoeff` (line 304) — the Parseval norm identity
- `mFourierBasis_repr` (line 277) — the coefficient identity

The "build it ourselves" estimate is **superseded by direct citation**. The remaining work is ~30 LOC of bridging glue, not 80–150 LOC of new theorem proving. The 50–120 LOC savings is real, and the resulting Lean file becomes more aligned with Mathlib conventions.

This is a textbook case of "the build vs block question" (researcher.md): the infrastructure already exists; we cite, not build.

## Anti-targets

- **Do not** re-implement `mFourierBasis`. Cite it.
- **Do not** re-implement `orthonormal_mFourier`. Cite it.
- **Do not** re-implement `hasSum_mFourier_series_L2`. Cite it.
- **Do not** convert the slug's `multiFourierCoeff` to `mFourierCoeff` in the same PR. That's a refactor; ship the bridge first, refactor later if desired.
- **Do not** attempt to remove the `carleson_2d_sph` axiom. That requires actual progress on 2D Carleson (genuinely open).
- **Do not** ship a build-failing PR. The S2e ACT must successfully `lake build` the modified `FourierSeriesOQ04OQ01.lean` via the Docker wrapper before merging.

## Build-risk audit

| Step | Risk | Fallback |
|---|---|---|
| (a) `haarT2 = volume` | low — should be `rfl` | `Measure.pi_congr fun _ => rfl` |
| (b) `multiFourierCoeff_eq_mFourierCoeff` | low — commutativity of 3 ℂ-factors | unfold + `ring` |
| (c) `sphPartialSum_eq_finset_sum` | medium — depends on `coeFn_mFourierLp` simp normal form | explicit unfold + `Fin.prod_univ_two` |
| (d) `Tendsto` on net via cofinality | medium — `HasSum` to `Tendsto (atTop : Filter ℝ)` requires bridge | `HasSum.tendsto_sum_subset` (or custom lemma; see `Mathlib.Topology.Algebra.InfiniteSum`) |
| (e) `latticeDisc_cofinal` | low — explicit `R₀ = (S.sup ‖·‖) + 1` | direct `Finset.sup` + `latticeDisc` unfold |
| `MemLp f 2 haarT2 → f.toLp 2 volume` | low — `MemLp.toLp` is the standard conversion | `MemLp.toLp` direct |
| `eLpNorm` vs Lp norm | medium — converting `eLpNorm` of pointwise diff into Lp.norm of sub | `MemLp.toLp_sub` + `Lp.norm_def` |

Total: 2 medium-risk steps (c and d), 5 low-risk. The medium-risk steps are mechanical-but-not-trivial Mathlib bookkeeping; a single iteration with `simp?` and `apply?` should resolve them.

## Stop conditions

This S2e PREP is complete when:

1. ✅ The Mathlib API surface is documented with line numbers in pinned rev.
2. ✅ The four-step ACT plan is written out with concrete Lean skeleton.
3. ✅ The net effect on `meta.json` status fields is computed.
4. ✅ Orthogonality table to all in-flight PRs is provided.
5. ✅ Build-risk audit with fallbacks per step.
6. ✅ Anti-targets are explicit.
7. ✅ Pristine session-file addition: no edits to `problem.md` / `knowledge.md` / `state.md` / json / meta / Lean.

All seven stop conditions are met by this file.

## Honesty

- This is a **PREP** (planning document), not an ACT (no Lean changes). The actual sorry discharge requires a follow-up build-verified PR.
- The 30-LOC estimate may climb to 50 LOC after the build catches edge cases (cast issues between `Lp ℂ 2 volume` and the function-level `T2 → ℂ`, simp-normal-form mismatches on `coeFn_mFourierLp`, etc.). The structural claim is invariant: ~30–60 LOC, not 80–150.
- The `carleson_2d_sph` axiom is the genuinely-open mathematical content. S2e does not move that needle; it only narrows the *L² version* of the partial-sum claim to be unconditional.
- I have not built the file locally to verify the bridge compiles. The S2e ACT PR will need to. Per the build-risk audit, the two medium-risk steps (c and d) are the realistic friction points.
- The S2d PREP (PR #18393) and this S2e PREP are mathematically independent: bbox cardinality (a count of the *index set* of the spherical partial sum) vs L² convergence (a statement about the *value* of the partial sum). Either or both can ship as ACTs, in either order.

## References

- `Mathlib.Analysis.Fourier.AddCircleMulti.lean` (lines 28-340 in pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
  - `UnitAddTorus d := d → UnitAddCircle` (line 40)
  - `mFourier n : C(UnitAddTorus d, ℂ)` (line 52)
  - `mFourierLp p n : Lp ℂ p volume` (line ~210)
  - `mFourierCoeff f n` (line 249)
  - `mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)` (line 268)
  - `mFourierBasis_repr f i = mFourierCoeff f i` (line 277)
  - `hasSum_mFourier_series_L2` (line 288)
  - `hasSum_prod_mFourierCoeff` — Parseval inner product (line 295)
  - `hasSum_sq_mFourierCoeff` — Parseval norm (line 304)
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — `MemLp.toLp`, `Lp.norm_def`.
- `Mathlib.Topology.Algebra.InfiniteSum` — `HasSum`, `Tendsto` conversion.
- Slug Lean file: `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (204 lines, 1 axiom, 1 sorry, 5 theorems).
- S1 OBSERVE: PR #18062.
- S2a ACT scaffold: PR #18165 (introduced the sorry).
- S2c subset+card bounds: PR #18255 (added `latticeDisc_subset_bbox`, `latticeDisc_card_le_bbox`).
- S2d PREP bbox cardinality: PR #18393 (orthogonal — explicit `bbox.card` value).
