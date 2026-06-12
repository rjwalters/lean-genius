# S15 ACT — sorry-free close of `sphPartialSum_L2_norm_converge`

**Author:** researcher-2
**Timestamp:** 2026-06-12
**Phase:** ACT (Lean delta — discharges the file's last sorry)
**Mode:** ACT (executes the S7 audit §4 recipe, steps 4–6)
**Iteration:** 13 → 14

## TL;DR

The unconditional companion `sphPartialSum_L2_norm_converge` is now **proved
sorry-free**. The file's only remaining assumption is the intended open
conjecture `axiom carleson_2d_sph`. Build: Docker `lean4-arm64:v4.26.0`, 7743
jobs, exit 0.

## The decisive finding (corrects the S11–S14 measure-bridge premise)

The S7 audit recipe and S11–S14 PREP/ACT work assumed the Mathlib engine
`UnitAddTorus.hasSum_mFourier_series_L2` is stated over the **global** `volume`
on `Fin 2 → AddCircle 1`, and built `haarT2_eq_volume : haarT2 = volume` as the
bridge. That premise is **wrong in a way that matters**:

- `AddCircleMulti.lean` declares a **local instance**
  `MeasureSpace UnitAddCircle := ⟨haarAddCircle⟩` (line 32). Every definition in
  that file (`mFourierLp`, `mFourierCoeff`, `hasSum_mFourier_series_L2`, …) bakes
  in *that* instance. So the engine's ambient `volume` on `UnitAddTorus (Fin 2)`
  is `Measure.pi (fun _ => haarAddCircle)`.
- Our `haarT2` is **defined** as exactly `Measure.pi (fun _ => haarAddCircle)`.
  Hence the engine's measure is **definitionally equal** to `haarT2`.
- The *global* `volume` on `AddCircle 1` is
  `ENNReal.ofReal 1 • haarAddCircle` (from `AddCircle.measureSpace`,
  `volume = ENNReal.ofReal T • haarAddCircle` is `rfl`). This is only
  *propositionally* equal to `haarAddCircle` (off by `1 •`), NOT definitionally.

So `haarT2_eq_volume` relates `haarT2` to the **wrong** (global) measure; it is
not the bridge the engine needs. The correct move is to state everything in
`haarT2` and let **defeq** unify it with the engine's measure. This worked: the
engine application `hasSum_mFourier_series_L2 (fhat : Lp ℂ 2 haarT2)` typechecks
directly, and `integral_congr_ae` across the engine/`haarT2` integrals fires by
defeq. No `volume` cast appears anywhere in the close.

## Lean delta

`proofs/Proofs/FourierSeriesOQ04OQ01.lean` (476 → 598 lines, 14 → 16 theorems):

- **`mFourier_fin2`** (sorry-free): `UnitAddTorus.mFourier k x =
  fourier (k 0) (x 0) * fourier (k 1) (x 1)` via `Fin.prod_univ_two`.
- **`mFourierCoeff_eq_multiFourierCoeff`** (sorry-free): for any `Lp`
  representative `fhat` of `f`, `mFourierCoeff (⇑fhat) k = multiFourierCoeff f k`,
  via `integral_congr_ae` + character factorisation.
- **`sphPartialSum_L2_norm_converge`** (sorry-free): the close. Structure:
  1. `fhat := hf.toLp f`, `hfhat : ⇑fhat =ᵐ f`.
  2. `hSum := hasSum_mFourier_series_L2 fhat` (engine, as a `Tendsto` over the
     inclusion-directed `Finset (ℤ²)` filter).
  3. `htend : Tendsto latticeDisc atTop atTop` from `latticeDisc_eventually_supset`
     (S9) via `tendsto_atTop_atTop`.
  4. `hConv := hSum.comp htend` → `Tendsto (fun R => ∑_{latticeDisc R} g) (𝓝 fhat)`.
  5. `hnorm` via `tendsto_iff_norm_sub_tendsto_zero`.
  6. `hbridge` (finset induction with `Lp.coeFn_add`/`Lp.coeFn_smul`/
     `coeFn_mFourierLp` + the two bridge lemmas): `⇑(∑ g) =ᵐ sphPartialSum f R`.
  7. `Lp.norm_def` + `eLpNorm_congr_ae` rewrite `‖∑ g - fhat‖` as
     `(eLpNorm (sphPartialSum f R - f) 2 haarT2).toReal`.
  8. `ENNReal.tendsto_toReal_iff` (finiteness via `Lp.eLpNorm_ne_top`) lifts to
     the `ℝ≥0∞` `eLpNorm` goal.

Note: the S10 helper `coeFn_finset_sum_haarT2` was not reused (the close inlines
the analogous induction folding in the per-term character rewrite); it remains in
the file as a standalone contribution.

Gallery `meta.json` / `annotations.json`: `sorries 1 → 0`, `theoremCount 14 → 16`,
`lineCount 476 → 598`; the `l2-norm-companion` section/annotation rewritten to
"proved (S15)" with the corrected defeq-measure explanation; section line ranges
resynced to the current file; `status` stays `axiomatized` / `badge` stays
`axiom` (the open conjecture `carleson_2d_sph` is the sole assumption).

## Gotcha logged

Lean's tokenizer rejects the combining-circumflex identifier `f̂` (U+0066 +
U+0302) with `expected token`. Used ASCII `fhat` instead.

## Next

- This entry's Lean layer is now maximal: 1 intended axiom (open conjecture),
  0 sorries. No further ACT is needed unless the conjecture itself is attacked
  (genuine open mathematics — out of scope).
- Optional cleanup (HERMIT candidate): `haarT2_eq_volume`,
  `memLp_haarT2_iff_volume`, `eLpNorm_haarT2_eq_volume` (S11/S14) targeted the
  global-volume bridge that the close did **not** need; they are now dead-end
  scaffolding and could be pruned.
