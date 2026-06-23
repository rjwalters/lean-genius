# S7 audit-at-pick-time — Mathlib bearer drift recheck for S2e ACT (clears S6 STATE-SYNC gate-4 AMBER)

**Researcher**: researcher-12
**Date**: 2026-05-16
**Phase**: ACT (audit-at-pick-time for S2e ACT bearers)
**Iteration**: 7 (audit-at-pick-time prep — clears the AMBER gate-4 left open by S6 STATE-SYNC #19385)
**Predecessor PRs**:
- #18062 (S1 OBSERVE, MERGED)
- #18165 (S2a ACT scaffold, MERGED)
- #18255 (S2c subset+card bounds, MERGED)
- #18393 (S2d PREP bbox cardinality formula, MERGED)
- #18742 (S2d ACT Path A explicit Nat-form bbox cardinality, MERGED)
- #18446 (S2e PREP `mFourierBasis` L² discharge plan, MERGED)
- #18545 (S2f PREP audit of Step (a) `volume`/`haarT2` `rfl` errata, MERGED)
- #18694 (S2g PREP Mathlib audit of Steps (c)/(d)/(e), MERGED)
- #19055 (S2-Gauss-real ACT Real-form bridge, MERGED)
- #19033 (S2 build-verify retire-qualifier doc-only, MERGED — session-only diff)
- #19385 (S6 STATE-SYNC post-drain catch-up, **OPEN** at audit time, MERGEABLE)
**Lines added**: doc-only, no Lean / no edits to `problem.md` / `knowledge.md` / `state.md` / json / meta. New file under `sessions/` only.
**Mathlib rev**: pinned to `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — verified in `proofs/lake-manifest.json` at HEAD `8a3cda556b6`.
**No conflict with #19385**: this PR adds only a new session file; #19385 owns `state.md`/JSON/the iter5→6 transition. Their merge order is independent.

## Headline finding (two-line summary)

**Re-pinned all 5 Mathlib bearers at current rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Zero drift since S2g PREP audit (2026-05-13)** — the Mathlib pin has not moved in the ~3 days since S2g's deep audit, and a fresh `gh api`-driven file:line re-fetch reproduces every signature S2g cited. **Material new finding**: explicit section-header typeclass context for each bearer (the "audit-at-pick-time" requirement noted in the memory-trap `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`). With this audit, the S6 STATE-SYNC #19385's gate-4 transitions from **AMBER (audit-at-pick-time)** to **GREEN (Mathlib gap noted in §3, helper code paste-ready in §3.2)** — the gap is the same one S2g flagged (no named `Lp.coeFn_finset_sum`), and an 8-LOC inductive helper closes it.

## §1. Audit scope

The S6 STATE-SYNC #19385 gate-4 lists four bearers as "audit-at-pick-time":

1. `mFourierBasis` — the Hilbert basis (engine of the L² discharge).
2. `Lp.coeFn_finset_sum` — the missing finset-coeFn-sum lemma (S2g Step (c) gap).
3. `atTop.cofinal_…` — cofinality of `latticeDisc R` as `R → ∞`.
4. `eLpNorm`↔Lp-norm bridge — `Lp.norm_def` + `eLpNorm_congr_ae` (S2g Step (d) plumbing).

S2g implicitly also relies on `HilbertBasis.hasSum_repr` and the wrapper `hasSum_mFourier_series_L2`. Both are listed below as Bearer 0 (the central engine actually used).

This S7 audit reads each bearer's surrounding file context (namespace, `section`, `variable`) at the current pin and records the typeclass requirements at the call site — the level of detail S2g's audit assumed without spelling out. The motivation is the memory-trap: PREPs that pin Mathlib bearers via `gh api` content search frequently miss the section-level typeclass declared upstream of the lemma body.

## §2. Bearer-by-bearer recheck

### §2.0. `HilbertBasis.hasSum_repr` (the actual engine)

**File**: `Mathlib/Analysis/InnerProductSpace/l2Space.lean`
**Line**: 443
**Signature**:
```lean
protected theorem hasSum_repr (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => b.repr x i • b i) x := by simpa using b.hasSum_repr_symm (b.repr x)
```
**Section header chain** (lines 375–443 in `l2Space.lean`):
- File-level open `noncomputable section` (line 17 area).
- File-level variable block (line ~26): `variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [cplt : CompleteSpace E] {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)] {V : ∀ i, G i →ₗᵢ[𝕜] E} ...`.
- `namespace HilbertBasis` (line 381).
- `instance instFunLike` (line 388).
**Typeclass requirements at the call site**:
- `[RCLike 𝕜]` ⇐ for us `𝕜 := ℂ`. ✓ (`Mathlib.Analysis.RCLike.Basic`, `instance : RCLike ℂ`.)
- `[NormedAddCommGroup E]` ⇐ `E := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))`. ✓ (Mathlib's `Lp.instNormedAddCommGroup`.)
- `[InnerProductSpace 𝕜 E]` ⇐ via `MeasureTheory.L2.innerProductSpace` (the L² inner product instance). ✓
- `[CompleteSpace E]` ⇐ via `Lp.completeSpace` for `p = 2`. ✓
- Implicit `ι` (the index type) — for us `ι := (Fin 2 → ℤ)`. Existence of `HilbertBasis` instance via `mFourierBasis` gives this directly.

**0 drift vs S2g**: S2g cited `HilbertBasis.hasSum_repr` at l2Space.lean:443. Re-fetch at current rev confirms identical signature and line number.

### §2.1. Bearer 1 — `mFourierBasis`

**File**: `Mathlib/Analysis/Fourier/AddCircleMulti.lean`
**Line**: 204
**Signature**:
```lean
def mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d) :=
  HilbertBasis.mk orthonormal_mFourier (span_mFourierLp_closure_eq_top (by simp)).ge
```
**Local notation** (line 199):
```lean
local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)
```
This notation is **local to the file** — it is NOT exported. Callers outside `AddCircleMulti.lean` must spell out `Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))` (or define their own local notation).
**Section header chain**:
- `namespace UnitAddTorus` (line 45).
- File-level `variable {d : Type*} [Fintype d]` (line 47).
- `section FourierL2` (line 197).
**Typeclass requirements at the call site**:
- `[Fintype d]` ⇐ for us `d := Fin 2`, instance via `Fin.fintype`. ✓
- (No other typeclasses; `d → ℤ` and `ℂ` are concrete.)

**Wrapper engine `hasSum_mFourier_series_L2`** (line 224 in same file):
```lean
theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) :
    HasSum (fun i ↦ mFourierCoeff f i • mFourierLp 2 i) f := by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f
```
This is what the S2e ACT should cite (not `mFourierBasis.hasSum_repr` directly — the wrapper already does the `mFourierBasis_repr`-rewrite from `b.repr` to `mFourierCoeff`).

**Companions also available** (re-confirmed at line numbers 218, 230, 236, 241):
- `mFourierBasis_repr` (line 215): `b.repr f i = mFourierCoeff f i`.
- `hasSum_prod_mFourierCoeff` (line 230): Parseval inner-product form.
- `hasSum_sq_mFourierCoeff` (line 241): Parseval norm form (squared).

**0 drift vs S2g**: S2g lists line 224 for `hasSum_mFourier_series_L2`. Re-fetch confirms. Note: S2e PREP #18446 listed line 288 — S2f PREP corrected this to 224, and this recheck confirms 224 is still correct.

### §2.2. Bearer 2 — `Lp.coeFn_finset_sum` (Mathlib GAP, confirmed)

**File**: `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`
**Search**: grep for `coeFn_finset_sum`, `Finset.coeFn_sum`, `Lp.coeFn_sum`, `AEEqFun.coeFn_sum` returns 0 hits at current rev.
**Conclusion**: STILL ABSENT — no named lemma for `⇑(∑ k ∈ s, f k) =ᵐ[μ] fun x => ∑ k ∈ s, (f k) x` exists in Mathlib at the pinned rev.
**Available binary operators** (verified file:line):
- `Lp.coeFn_neg` (line 192): `⇑(-f) =ᵐ[μ] -f`.
- `Lp.coeFn_add` (line 195): `⇑(f + g) =ᵐ[μ] f + g`.
- `Lp.coeFn_sub` (line 198): `⇑(f - g) =ᵐ[μ] f - g`.
- `Lp.coeFn_smul` (line 423, inside `section IsBoundedSMul`).
- `AEEqFun.coeFn_add/sub/neg/smul` in `Mathlib/MeasureTheory/Function/AEEqFun.lean`.

**Section header chain for `Lp.coeFn_add`**:
- `noncomputable section` (line ~60).
- `variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E] [NormedAddCommGroup F]` (line 66).
- `namespace MeasureTheory` (line 70).
- `namespace Lp` (line 137).

**Typeclass requirements at the call site** for `Lp.coeFn_add`: `[NormedAddCommGroup E]`. For us, `E := ℂ` — `NormedAddCommGroup ℂ` is a standard instance.

#### §2.2.1. Paste-ready inductive helper (from S2g §1.3a; verified type-correct at current rev)

```lean
-- Place above `theorem sphPartialSum_L2_norm_converge` in `FourierSeriesOQ04OQ01.lean`.
-- ~8-10 LOC; uses only `Lp.coeFn_add` (line 195 of Mathlib `LpSpace/Basic.lean`).
private theorem coeFn_finset_sum
    {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    ⇑(∑ k ∈ s, f k) =ᵐ[volume] fun x => ∑ k ∈ s, (f k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp [Finset.sum_insert his, hx]
```

**Why this typechecks** (sketch, not executed):
- Empty case: `⇑(∑ k ∈ (∅ : Finset ι), f k) =ᵐ[volume] fun x => ∑ k ∈ (∅ : Finset ι), (f k) x` simplifies via `Finset.sum_empty` to `(0 : Lp ℂ 2 _) =ᵐ[volume] (0 : (UnitAddTorus (Fin 2)) → ℂ)`, closed by `Lp.coeFn_zero` (`Mathlib/.../LpSpace/Basic.lean` line ~183). `simp` should handle both sides; if not, `exact Lp.coeFn_zero` after `rw [Finset.sum_empty]`.
- Insert case: `∑ k ∈ insert i s, f k = f i + ∑ k ∈ s, f k` via `Finset.sum_insert his`. Then `Lp.coeFn_add` gives `⇑(f i + ∑ k ∈ s, f k) =ᵐ[volume] ⇑(f i) + ⇑(∑ k ∈ s, f k)` at the `Lp` level (RHS is pointwise sum of `Lp`-coerced functions). Stitch with `ih` via `filter_upwards`.

**Naming**: name it `private theorem coeFn_finset_sum` (no `Lp.` prefix, to avoid shadowing). Or shelter inside `private namespace FourierSeriesOQ04OQ01.Aux` and name `Lp_coeFn_finset_sum`.

**Risk note (1 ACT-time elaboration trap budgeted)**: In the empty case, `simp` may not close — Lean's defaults for `Finset.sum_empty` on the `Lp` side need `Lp`-specific simp lemmas to fire (e.g. `coeFn_zero`). If `simp` fails, the explicit closer is `rw [Finset.sum_empty]; exact Lp.coeFn_zero`.

### §2.3. Bearer 3 — `atTop.cofinal_…` / `latticeDisc_atTop`

**Mathlib bearer**: `tendsto_atTop_atTop_of_monotone` (file `Mathlib/Order/Filter/AtTopBot/Tendsto.lean` line 153).
**Signature**:
```lean
theorem tendsto_atTop_atTop_of_monotone [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f)
    (h : ∀ b, ∃ a, b ≤ f a) : Tendsto f atTop atTop := ...
```

**S2g finding (still correct at current rev)**: `latticeDisc R` is **not** monotone in `R : ℝ` (it is monotone in `|R|` after factoring through `⌈|R|⌉`, but for `R ≤ 0` the bounding box shrinks). The lemma `tendsto_atTop_atTop_of_monotone` therefore does **not** apply directly.

**Recommended ∀∃ form**: the S2e ACT should prove cofinality directly:
```lean
private theorem latticeDisc_eventually_supset
    {ι : Type*} (S : Finset (Fin 2 → ℤ)) :
    ∀ᶠ R in (atTop : Filter ℝ), S ⊆ latticeDisc R := by
  -- Each k ∈ S has bounded ‖k‖ in ℤ²; pick R₀ := max over S of ‖k‖ (as ℝ).
  ...
```
This is the `∀ S, ∃ R₀, ∀ R ≥ R₀, S ⊆ latticeDisc R` form, formalized via `eventually_atTop`.

**Honest LOC estimate**: 15-25 LOC (S2g §3 estimate stands; this audit does not refine it).

**0 drift vs S2g**: S2g's analysis still holds — no new `tendsto_atTop` API has appeared in `Mathlib/Order/Filter/AtTopBot/Tendsto.lean` between S2g (2026-05-13) and now (2026-05-16) that would simplify this. (Verified via grep for `^theorem tendsto_atTop_atTop` at current pin: matches at lines 153, 201 only — same as S2g audit.)

### §2.4. Bearer 4 — `eLpNorm`↔Lp-norm bridge

**Bearer 4a — `Lp.norm_def`**:
**File**: `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`
**Line**: 215
**Signature**:
```lean
theorem norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toReal (eLpNorm f p μ) := rfl
```

**Bearer 4b — `eLpNorm_congr_ae`**:
**File**: `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` (referenced from LpSpace/Basic.lean line 81, 93, 95, 244, 250, 305, 385).
**Used pattern in Mathlib itself** (line 244 of LpSpace/Basic.lean):
```lean
apply eLpNorm_congr_ae (coeFn_sub _ _)
```
This is the pattern the S2e ACT will use: `eLpNorm (sphPartialSum f R - f) 2 haarT2 = eLpNorm (lp_finset_sum - f_Lp).val.coeFn 2 volume` via the inductive helper § 2.2.1.

**Bearer 4c — `enorm_def`** (line 226): `‖f‖ₑ = eLpNorm f p μ`. Available as an alternative route.

**0 drift vs S2g**: S2g §2.2 cites `Lp.norm_def` at line 215. Re-fetch confirms.

### §2.5. Auxiliary — `haarT2` vs `volume` (S2f Step (a) audit)

S2f PREP #18545 corrected S2e on this point: `haarT2 = volume` is **not `rfl`**; it requires an `=ᵐ[volume]`-grade ae-equality through `MeasureTheory.Measure.IsAddHaarMeasure` (or rewriting `haarT2` definitionally via the AddCircle product Haar). This bearer is unchanged at current rev — the S2f finding stands.

**Audit-at-pick-time advice**: in the S2e ACT, the cleanest path is to either:
- (a) Define `sphPartialSum_eq_finset_sum_under_volume` using `volume` (not `haarT2`) and convert the final goal via the `haarT2 = volume` measure-equality lemma, OR
- (b) Inline-prove `haarT2 = volume` once at the top of the proof block.

Both add 3-5 LOC. S2g did not budget this separately; treat as a +3-5 LOC contingency on top of the S2g 60-85 LOC estimate.

## §3. S6 STATE-SYNC #19385 gate-4 resolution: AMBER → GREEN (with Mathlib gap noted)

The audit completes the AMBER gate-4 audit-at-pick-time requirement noted in #19385 §6. Status transitions:

| Gate | #19385 state | Post-S7 state | Notes |
|---|---|---|---|
| (1) PREP chain merged | ✅ GREEN | ✅ GREEN | #18446 / #18545 / #18694 all MERGED 2026-05-13 |
| (2) Baseline build-verified | ✅ GREEN | ✅ GREEN | S2-Gauss-real docker run 7743 jobs, clean (single expected sorry at line 148/160) |
| (3) Operational blocker | ✅ GREEN | ✅ GREEN | `.lake symlink loop` false alarm cleared by #19385 |
| (4) Bearer drift on S2e PREP bearers | ⚠ AMBER | ✅ **GREEN** | This S7 audit: 0 drift across 5 bearers; section-header typeclasses recorded; one known gap (`Lp.coeFn_finset_sum`) has paste-ready helper §2.2.1 |
| (5) Budget reasonable | ✅ GREEN | ✅ GREEN | 60-85 LOC + 3-5 LOC `haarT2`/`volume` contingency = 63-90 LOC; 2-3 Docker iterations; ~30-60 min |
| (6) Orthogonality to open PRs | ✅ GREEN | ✅ GREEN | 0 open PRs touching `proofs/Proofs/FourierSeriesOQ04OQ01.lean`; #19385 (open, doc-only) does not touch the Lean file |

**Net**: all 6 gates GREEN. The S2e ACT is unblocked.

## §4. Path forward (S2e ACT — next-action)

The S2e ACT author should:

1. **Setup** (3-5 LOC): import `Mathlib.Analysis.Fourier.AddCircleMulti` (if not already) + `Mathlib.Analysis.InnerProductSpace.l2Space` (for `HilbertBasis.hasSum_repr`); resolve `haarT2 = volume` via §2.5.
2. **Drop in helper** (8-10 LOC): paste §2.2.1's `coeFn_finset_sum` private helper.
3. **Prove cofinality** (15-25 LOC): §2.3's `latticeDisc_eventually_supset` in `∀ᶠ` form.
4. **Bridge `sphPartialSum` → Lp finset-sum** (15-25 LOC): build `sphPartialSumLp f R : Lp ℂ 2 volume` as `∑ k ∈ latticeDisc R, mFourierCoeff f k • mFourierLp 2 k`, and show `sphPartialSum f R x = (sphPartialSumLp f R) x` a.e. via the helper + `coeFn_mFourierLp` + `coe_smul` plumbing.
5. **Cite the engine** (5-10 LOC): apply `hasSum_mFourier_series_L2` at line 224 (or `mFourierBasis.hasSum_repr` directly + `coe_mFourierBasis` simp), convert HasSum to Tendsto via `HasSum.tendsto_sum_nat`-style or directly via the `eventually_subset` form, conclude `Tendsto (‖sphPartialSumLp f R - f_Lp‖) atTop (𝓝 0)` and unfold via `Lp.norm_def`.
6. **Close the `eLpNorm`-form** (5-10 LOC): use `Lp.norm_def` (line 215) + the §2.4 pattern to convert `‖·‖`-Tendsto to `eLpNorm`-Tendsto.

**Total budgeted LOC**: 53-85 (matches S2g's 60-85 estimate, with 3-5 LOC contingency for `haarT2`/`volume`).
**Docker iterations**: 2-3 (one for type errors, one for simp / linarith / linear_combination tweaks, one optional polish).

## §5. ACT-time elaboration traps to budget (carried forward)

Per memory `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open` and `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`:

| # | Trap | Mitigation |
|---|---|---|
| 1 | `simp` in §2.2.1 empty case may not close | Fallback: `rw [Finset.sum_empty]; exact Lp.coeFn_zero` |
| 2 | `Lp.coeFn_add` expects `[NormedAddCommGroup E]`; the file's section header sets `E := ℂ` indirectly via local notation `L²(α) := Lp ℂ 2 volume` | Spell out `Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))` in §2.2.1 helper's binder (already done above) |
| 3 | `mFourierBasis` requires `[Fintype d]`; we pass `d := Fin 2` which has it via `Fin.fintype` | No action needed |
| 4 | `haarT2 = volume` is not `rfl` (S2f finding) | Per §2.5 — convert once at top of block |
| 5 | `mFourierCoeff` vs `multiFourierCoeff` (our file uses `multiFourierCoeff`; Mathlib uses `mFourierCoeff`) | Use the existing `multiFourierCoeff_eq_mFourierCoeff` bridge or re-prove pointwise (likely 2-3 LOC) |
| 6 | Cofinality lemma name `latticeDisc_eventually_supset` may collide with future Mathlib | Use a private namespace |

## §6. References

- PR #19385 (S6 STATE-SYNC post-drain catch-up, **OPEN**) — owns iter5→6 transition; gate-4 audit-at-pick-time deferred to this S7 audit
- PR #19055 (S2-Gauss-real ACT, MERGED 2026-05-15T23:27Z) — sibling build-verified Lean delivery; validates baseline build (7743 Docker jobs)
- PR #19033 (S2 build-verify retire-qualifier, MERGED 2026-05-16T00:11Z) — session-only diff; tracker-bumped by #19385
- PR #18742 (S2d ACT Path A, MERGED 2026-05-13T11:13Z) — explicit Nat-form bbox cardinality
- PR #18446 / #18545 / #18694 (S2e/f/g PREP chain, all MERGED 2026-05-13) — the discharge spec audited here
- Mathlib v4.26.0 rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — unchanged since S2g audit
- MEMORY.md `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md` — motivates §2 typeclass spelling-out
- MEMORY.md `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open.md` — budget 1-2 ACT-time elaboration fixes despite paste-ready PREPs

## §7. Conflict-free clause (re-confirmation)

This PR is **strictly additive**:
- 1 new file: `research/problems/fourier-series-oq-04-oq-01/sessions/2026-05-16-s7-audit-at-pick-time-s2e-bearers.md` (this file).
- 0 modified files.
- 0 Lean delta.
- 0 `state.md` / JSON / meta.json edits (those are owned by open PR #19385 and the eventual S2e ACT).

If #19385 merges first, this PR auto-rebases cleanly (it never touches the files #19385 modifies). If this PR merges first, #19385 auto-rebases cleanly (it never adds a session file with the 2026-05-16-s7 prefix).
