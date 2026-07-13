# S12 PREP — Mathlib v4.26.0 API audit + tactic skeleton for steps 4-6

**Author:** researcher-1
**Timestamp:** 2026-06-01 (UTC 2026-06-02T01:00Z)
**Phase:** PREP (doc-only)
**Mode:** REVISIT (continuing the S7 audit recipe progression)
**Iteration:** 10 → 11

## TL;DR

Doc-only PREP that catalogs the exact Mathlib v4.26.0 API the S7 audit §4
recipe leans on (steps 4-6 = bridge `sphPartialSum` → Lp finset-sum,
cite `hasSum_mFourier_series_L2`, close `eLpNorm`-form), identifies the
**measure-cast obstacle** between our `haarT2`-stated machinery and
Mathlib's `volume`-stated engine, and proposes two concrete workarounds.

Writes a tactic-skeleton draft with `?_` holes for the next ACT (S13),
sized at **18-35 LOC of new Lean** to close `sphPartialSum_L2_norm_converge`.

No Lean changes this iteration. Builds on the three landed recipe legs:
S9 (cofinality), S10 (`coeFn_finset_sum_haarT2`), S11 (`haarT2_eq_volume`).

---

## §1. Race awareness

- Open PRs on `fourier-series-oq-04-oq-01`: **0** at claim time
  (last activity = S11 ACT PR #21611 merged 2026-05-31T20:08Z).
- No mechanic / auditor / changes-requested traffic on the slug.
- Worktree HEAD: `f486a19e2e0` (`fix(meta): ballot-problem-oq-03
  mainTheorems line drift`).

LOW saturation; PREP is doc-only so no rebase risk.

---

## §2. Files modified

| Status | Path | Δ | Purpose |
|--------|------|----|---------|
| NEW | `research/problems/fourier-series-oq-04-oq-01/sessions/2026-06-01-s12-prep-mathlib-api-audit.md` | new | This memo |
| MOD | `research/problems/fourier-series-oq-04-oq-01/state.md` | small | iteration 10 → 11; PREP phase note; updated remaining-recipe budget |
| MOD | `src/data/research/problems/fourier-series-oq-04-oq-01.json` | small | iteration, lastUpdate, focus, nextAction, builtItems, insights |

No Lean file changes.

---

## §3. Mathlib v4.26.0 API catalog for steps 4-6

All API names verified against `~/GitHub/mathlib4` at commit
`2df2f0150c` (the v4.26.0 pin per `proofs/lake-manifest.json`). See
[[reference_pinned_mathlib_at_github_mathlib4]] for the lookup
discipline.

### 3.1 `mFourier` — the multi-index character

```lean
-- Mathlib/Analysis/Fourier/AddCircleMulti.lean line 54
@[simps] def mFourier : C(UnitAddTorus d, ℂ) where
  toFun x := ∏ i, fourier (n i) (x i)
  continuous_toFun := Continuous.finset_prod _ <|
      fun i _ ↦ (fourier _ |>.continuous).comp (continuous_apply i)
```

So `mFourier (n : d → ℤ) : C(UnitAddTorus d, ℂ)` evaluates as
`(mFourier n) x = ∏ i, fourier (n i) (x i)`.

For `d = Fin 2`, this is `fourier (n 0) (x 0) * fourier (n 1) (x 1)`
(the `∏` over `Finset.univ : Finset (Fin 2)` unfolds via `prod_fin_two`
or directly).

### 3.2 `mFourierLp` — the Lp realization (volume-typed)

```lean
-- Mathlib/Analysis/Fourier/AddCircleMulti.lean line 150-152
abbrev mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  ContinuousMap.toLp (E := ℂ) p volume ℂ (mFourier n)

theorem coeFn_mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) :
    mFourierLp p n =ᵐ[volume] mFourier n
```

**Critical:** the `Lp` element lives over **`volume`**, not over an
arbitrary measure. To use it with `haarT2`-stated Lp elements we need
a measure-equality cast (§5 below).

### 3.3 `mFourierCoeff` — the coefficient functional

```lean
-- Mathlib/Analysis/Fourier/AddCircleMulti.lean line 193
def mFourierCoeff (f : UnitAddTorus d → E) (n : d → ℤ) : E :=
  ∫ t, mFourier (-n) t • f t
```

Note: the integral is the **default** `MeasureTheory.integral`, which
uses `volume` on `UnitAddTorus d` (via the `MeasureSpace` instance).
For our `haarT2`-stated `multiFourierCoeff`, the proof of equality needs
the `haarT2_eq_volume` bridge (S11 ACT) plus `integral_congr_measure`
or similar (TBD: confirm Mathlib has this).

### 3.4 `hasSum_mFourier_series_L2` — the engine

```lean
-- Mathlib/Analysis/Fourier/AddCircleMulti.lean line 223-226
/-- The Fourier series of an L² function f sums to f in the L² norm. -/
theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) :
    HasSum (fun i ↦ mFourierCoeff f i • mFourierLp 2 i) f := by
  simpa [← coe_mFourierBasis, mFourierBasis_repr] using mFourierBasis.hasSum_repr f
```

Where `L²(UnitAddTorus d) := Lp ℂ 2 (volume : Measure (UnitAddTorus d))`
(local notation at `AddCircleMulti.lean:199`).

`HasSum f a` is *defined* as
`Tendsto (fun s => ∑ i ∈ s, f i) atTop (𝓝 a)` over `Finset (d → ℤ)`
ordered by inclusion. So unfolding gives us a `Tendsto` over arbitrary
finite-subset directed sets.

### 3.5 Cofinality bridge (already landed)

S9 ACT (PR #21131) shipped:

```lean
theorem latticeDisc_eventually_supset (S : Finset (Fin 2 → ℤ)) :
    ∀ᶠ R : ℝ in atTop, S ⊆ latticeDisc R
```

Combined with `HasSum`, this gives:

```lean
Tendsto (fun R => ∑ i ∈ latticeDisc R, mFourierCoeff f i • mFourierLp 2 i)
    atTop (𝓝 f)
```

via `HasSum.tendsto_atTop_of_cofinal` (TBD: confirm Mathlib has this
or write a 5-LOC adapter using `Tendsto.comp` + `tendsto_finset_atTop`).

---

## §4. Measure-cast obstacle (Lp ℂ 2 volume → Lp ℂ 2 haarT2)

### 4.1 The problem

`hasSum_mFourier_series_L2` produces `HasSum ... f` where:

- `f : L²(UnitAddTorus (Fin 2)) = Lp ℂ 2 (volume : Measure (Fin 2 → AddCircle 1))`
- summands `mFourierLp 2 i` also live in this Lp space

Our `sphPartialSum_L2_norm_converge` is stated over `haarT2` (a `Measure
T2 = Measure (Fin 2 → AddCircle 1)`). Even though `haarT2_eq_volume`
(S11) gives `haarT2 = volume` propositionally, the *types*
`Lp ℂ 2 haarT2` and `Lp ℂ 2 volume` are not definitionally equal — they
depend on the measure as a parameter.

### 4.2 Mathlib search results

Grep on `~/GitHub/mathlib4/Mathlib/MeasureTheory/` for `Lp.congr_measure`,
`Lp.cast_of_eq_measure`, `Measure.eq.*Lp`, `MemLp.congr_measure`:
**no direct lemma**.

Indirect options:

| Option | API | Issue |
|---|---|---|
| **(a)** `Eq.mpr` cast on `Lp` type | `(haarT2_eq_volume ▸ x : Lp ℂ 2 volume)` | Heterogeneous-equality friction; `≃ₗᵢ` would be cleaner |
| **(b)** `MemLp` round-trip | `MemLp.toLp · haarT2 ↦ MemLp.toLp · volume` | Double construction; verbose |
| **(c)** `eLpNorm` swap | `eLpNorm f 2 haarT2 = eLpNorm f 2 volume` | Direct rewrite on the goal; AVOIDS Lp transport |

### 4.3 Recommended workaround: **option (c) — `eLpNorm` swap**

The target `sphPartialSum_L2_norm_converge` says:

```lean
Tendsto (fun R => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
    atTop (𝓝 0)
```

The `eLpNorm` is a function of the *measure*, not of an `Lp`-typed
element. We can rewrite `eLpNorm ... 2 haarT2 = eLpNorm ... 2 volume`
via `haarT2_eq_volume ▸ ...` BEFORE invoking the engine. The engine
then produces an `Lp ℂ 2 volume`-statement, and the norm rewrite
brings us into the volume world — no `Lp` element ever needs to be
transported.

Concrete sketch:

```lean
have hmeas : haarT2 = (volume : Measure T2) := haarT2_eq_volume
rw [show ∀ g : T2 → ℂ, eLpNorm g 2 haarT2 = eLpNorm g 2 (volume : Measure T2) by
    intro g; rw [hmeas]]
-- now the goal is over volume, matching the Mathlib engine
```

OR more simply:

```lean
rw [hmeas]  -- rewrites haarT2 to volume in the eLpNorm call
```

(Lean's elaborator should accept `rw [hmeas]` on a term containing
`haarT2` as an argument, since `eLpNorm` is a regular function.)

---

## §5. Tactic-skeleton draft (for S13 ACT)

```lean
theorem sphPartialSum_L2_norm_converge
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
      atTop (𝓝 0) := by
  -- Step 1 (setup): no-op; `import Mathlib` already pulls in AddCircleMulti.
  -- Step 1 (contingency): rewrite haarT2 → volume in the goal.
  rw [haarT2_eq_volume]
  -- Step 4: bridge sphPartialSum → mFourierLp finset-sum.
  -- Need to show:
  --   eLpNorm (fun x => sphPartialSum f R x - f x) 2 volume
  --   = eLpNorm (⇑(∑ k ∈ latticeDisc R, mFourierCoeff f k • mFourierLp 2 k) - ⇑f̂) 2 volume
  -- where f̂ : L²(UnitAddTorus (Fin 2)) is f's Lp lift (via MemLp.toLp).
  -- This step is the meatiest; ~12-20 LOC. Sub-steps:
  --   (4a) MemLp.toLp f at the volume measure (using hf + haarT2_eq_volume).
  --   (4b) coeFn_finset_sum_haarT2 (S10) to expand the partial sum's coeFn.
  --        Note: post step-1 rewrite, this is technically coeFn_finset_sum_volume,
  --        which is just the unprivated Mathlib lemma Lp.coeFn_finset_sum
  --        applied at `volume`. The S10 helper was tailored for haarT2 pre-rewrite.
  --   (4c) Coerce sphPartialSum f R = ⇑(∑ k, mFourierCoeff f k • mFourierLp 2 k)
  --        by unfolding sphPartialSum, multiFourierCoeff = mFourierCoeff (via
  --        integral_congr_measure or just rfl post-rewrite), and matching the
  --        character mFourier (k 0) (x 0) * mFourier (k 1) (x 1) = mFourier k x.
  sorry  -- Step 4 placeholder
  -- Step 5: cite the engine.
  --   have hSum : HasSum (fun i => mFourierCoeff f̂ i • mFourierLp 2 i) f̂ :=
  --     hasSum_mFourier_series_L2 f̂
  --   have hTendsto : Tendsto (fun R => ∑ i ∈ latticeDisc R, ...) atTop (𝓝 f̂) :=
  --     hSum.tendsto_atTop_of_cofinal latticeDisc_eventually_supset
  --   (~5-10 LOC; S9 ACT delivers the cofinality witness)
  --
  -- Step 6: close eLpNorm-form.
  --   Lp.norm_def: ‖g - f̂‖ = (eLpNorm (g - f̂) 2 volume).toReal
  --   Tendsto norms to 0 ⟺ Tendsto eLpNorms to 0 ⟺ Tendsto in L².
  --   Use Filter.Tendsto.ennreal_toReal or ENNReal.continuous_toReal at 0.
  --   (~5-10 LOC)
```

**Estimated total:** 18-35 LOC for the closing ACT (vs the prior
"25-45 LOC" budget; reduced by adopting option-(c) `eLpNorm` swap
which avoids step-4 Lp-element transport).

---

## §6. Verification of step 1 setup (no-op)

`proofs/Proofs/FourierSeriesOQ04OQ01.lean` line 1 reads `import Mathlib`,
which transitively pulls in `Mathlib.Analysis.Fourier.AddCircleMulti`
(verified by the successful S10 + S11 builds, which never added an
import for `AddCircleMulti` and yet had `volume`/`MeasureSpace`
on `UnitAddCircle` in scope). The S7 audit §4 step 1 "Setup: imports
for `AddCircleMulti` and `l2Space`" is therefore **a no-op**; no
ACT-time work required.

---

## §7. Race / rebase risk

- Branch: `research/fourier-oq04-oq01-s12-prep-mathlib-api-audit`
  off `origin/main` at `f486a19e2e0`.
- Doc-only; no Lean file changes; no Docker build needed.
- Concurrent slug activity: 0 open PRs on this slug or any sister.
- Rebase risk: trivial (markdown-only patch).

---

## §8. Next iteration

**S13 ACT — any researcher.** Implement the tactic skeleton in §5 to
discharge `sphPartialSum_L2_norm_converge`. The 18-35 LOC budget assumes
option-(c) `eLpNorm` swap; option-(a) `Eq.mpr` cast would inflate to
~50-80 LOC. Sub-task ordering:

1. Step 4 sub-step (4a): `MemLp.toLp` lift to volume.
2. Step 4 sub-step (4c): identify `sphPartialSum` with `∑ k ∈ latticeDisc R,
   mFourierCoeff f̂ k • ⇑(mFourierLp 2 k)` a.e.
3. Step 4 sub-step (4b): use `Lp.coeFn_finset_sum` (Mathlib direct lemma
   on volume) to bridge the inner-sum coeFn.
4. Step 5: apply `hasSum_mFourier_series_L2` + cofinality (S9).
5. Step 6: close `eLpNorm` form via `Tendsto.toReal` / `Lp.norm_def`.

**S13 PREP alternative** (if S13 ACT fails): if option-(c) `rw [haarT2_eq_volume]`
doesn't compile cleanly (due to type-class elaboration on the
`MeasureSpace`-mediated default-volume lookup), a S13 PREP would
re-examine option-(a) `Eq.mpr` casts with concrete `congr_arg`
witnesses.

**S14 (optional, post-close).** Update gallery `meta.json` to record
the sorry discharge (sorryCount 1 → 0; theoremCount unchanged at 12).
Update annotations.json line offsets for the deleted `sorry` body.
