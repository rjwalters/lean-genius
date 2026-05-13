# S2g PREP — Mathlib audit of S2e Steps (c)/(d)/(e): Lp finset-sum coercion, `latticeDisc atTop` cofinality, eLpNorm↔Lp-norm bridge

**Researcher**: researcher-8
**Date**: 2026-05-13
**Phase**: ACT (PREP / Mathlib API audit-continuation of S2e PREP #18446)
**Iteration**: 2g (audit of Steps (c), (d), (e) of S2e PREP that S2f PREP #18545 did not touch)
**Predecessor PRs**:
- #18062 (S1 OBSERVE, MERGED)
- #18165 (S2a ACT scaffold, MERGED)
- #18255 (S2c subset+card bounds, MERGED)
- #18393 (S2d PREP bbox cardinality formula, MERGED)
- #18446 (S2e PREP `mFourierBasis` L² discharge plan, MERGED) — **partial target**
- #18545 (S2f PREP audit of S2e Step (a) `volume`/`haarT2` `rfl` errata, MERGED) — audited Step (a) only
**Lines added**: doc-only, no Lean / no edits to `problem.md` / `knowledge.md` / `state.md` / json / meta. New file under `sessions/` only.

## Headline finding (two-line summary)

S2f PREP #18545 audited Step (a) of the S2e plan (the `haarT2 = volume` `rfl` errata) and revised the LOC estimate from "~30 LOC" to "~35-50 LOC". **This audit (S2g) traces Steps (c), (d), (e) and finds the actual LOC budget is ~60-85 LOC**, with three concrete Mathlib gaps:

1. **Step (c) cannot be a 5-line `simp_rw` chain.** `mFourierLp 2 k` is an `Lp ℂ 2 volume` element, not a function. `Lp.coeFn_mFourierLp` returns `=ᵐ[volume]`, not pointwise `=`. Mathlib has **no named `Lp.coeFn_finset_sum` lemma** (verified via direct `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` inspection at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Step (c) requires either an inductive helper or a function-level rewrite.
2. **Step (e) `latticeDisc_atTop` requires `tendsto_atTop_atTop` (∀∃ form), not `_of_monotone`.** `latticeDisc R` is not monotone in `R : ℝ` (it's monotone in `|R|` after factoring through `⌈|R|⌉`, but for `R ≤ 0` the bbox shrinks). The 10-LOC sketch in S2e is realistic only if we use the direct `∀ S, ∃ R₀, ∀ R ≥ R₀, S ⊆ latticeDisc R` form. ~15-25 LOC honest estimate.
3. **Step (d) needs `eLpNorm`↔Lp-norm bridge.** Going from "Tendsto over Finset directed set" (HasSum's body) to "Tendsto over `R → ∞` with `eLpNorm` measurement" requires `eLpNorm_congr_ae` + `Lp.norm_def` + the Step (c) ae-equality.

Each gap is concrete; none invalidates the S2e thesis ("cite `mFourierBasis`, don't build Plancherel"). The 50-120 LOC savings over the original "build it ourselves" estimate stands. The 30→60-85 LOC revision means **the S2e ACT is a real engineering session, not a 30-line patch**.

## §1. Step (c) audit — `sphPartialSum_eq_finset_sum`

### What S2e PREP #18446 proposes (lines 144-156)

```lean
private theorem sphPartialSum_eq_finset_sum
    (f : T2 → ℂ) (R : ℝ) :
    (sphPartialSum f R : T2 → ℂ)
      = fun x => ∑ k ∈ latticeDisc R, mFourierCoeff f k • mFourierLp 2 k x := by
  ext x
  unfold sphPartialSum
  simp_rw [multiFourierCoeff_eq_mFourierCoeff, smul_eq_mul, ← mul_assoc]
  sorry  -- "~5 line `simp` + `Fin.prod_univ_two`"
```

with body comment: *"= ∑ k, mFourierCoeff f k • (∏ i, fourier (k i) (x i)) = ∑ k, mFourierCoeff f k • mFourier k x = ∑ k, mFourierCoeff f k • mFourierLp 2 k x (via `coeFn_mFourierLp`)"*.

### Why a `simp_rw [coeFn_mFourierLp]` cannot close this

`Mathlib/Analysis/Fourier/AddCircleMulti.lean:154-156` at pinned rev:

```lean
theorem coeFn_mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) :
    mFourierLp p n =ᵐ[volume] mFourier n :=
  ContinuousMap.coeFn_toLp volume (mFourier n)
```

This is an **a.e. equality**, not a pointwise equality. `mFourierLp 2 k` is an `Lp ℂ 2 (volume : Measure (UnitAddTorus d))` element; its `⇑` coercion to `UnitAddTorus d → ℂ` factors through `AEEqFun.coeFn` and is defined only **modulo a.e. equivalence**.

The S2e PREP's stated goal `(sphPartialSum f R : T2 → ℂ) = fun x => ∑ k, ... mFourierLp 2 k x` (with no `=ᵐ`) is therefore the **wrong type** of equality. At best, one can state:

```lean
-- Function-level a.e. equality:
sphPartialSum f R =ᵐ[haarT2] fun x => ∑ k ∈ latticeDisc R, mFourierCoeff f k • (mFourierLp 2 k x)
```

But this still needs **`mFourierLp 2 k x` to make sense pointwise**, which requires invoking `Lp.instCoeFun` (the global `CoeFun (Lp E p μ) (fun _ => α → E)` instance defined at `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:140-141` at pinned rev).

### Mathlib gap: no named `Lp.coeFn_finset_sum`

Searched `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` (893 lines, pinned rev) for any of:
- `coeFn_finset_sum`
- `Finset.coeFn_sum`
- `Lp.coeFn_sum`
- `AEEqFun.coeFn_sum`

**None present.** Mathlib exposes the binary operators (`Lp.coeFn_add`, `Lp.coeFn_sub`, `Lp.coeFn_neg`, `Lp.coeFn_smul` at lines 195, 198, 423, and `AEEqFun.coeFn_add/sub/neg/smul` at `Mathlib/MeasureTheory/Function/AEEqFun.lean:43, 648`). To get a finset-sum version, the ACT author must either:

(a) **Inductive helper** (~8-12 LOC):
```lean
private theorem Lp.coeFn_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) :
    ⇑(∑ k ∈ s, f k) =ᵐ[volume] fun x => ∑ k ∈ s, (f k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp [Finset.sum_insert his, hx]
```

(b) **Rewrite the goal entirely at function level**, never invoking `Lp.coeFn` on a sum. Construct the Lp element `sphPartialSumLp f R` *directly* as a finset sum at the `MemLp` level, using `MemLp.toLp_add` and `MemLp.toLp_finset_sum` (the latter is again missing as a named lemma; `MemLp.add` is at `Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:155`).

Either path costs ~10-15 LOC.

### `mFourierLp 2 k x` unfolds to what?

Once we have `Lp.coeFn (∑ k, c k • mFourierLp 2 k) =ᵐ[volume] fun x => ∑ k, c k • (mFourierLp 2 k) x`, the next step uses `coeFn_mFourierLp 2 k` to a.e.-replace `(mFourierLp 2 k) x` with `(mFourier k) x = mFourier (-(-k)) x`. But:

- `mFourier k : C(UnitAddTorus d, ℂ)` is a `ContinuousMap`, not a function.
- `(mFourier k) x` invokes `ContinuousMap.instFunLike` to extract the function part.
- `Mathlib/Analysis/Fourier/AddCircleMulti.lean:54` defines `mFourier n = { toFun := fun t => ∏ i, fourier (n i) (t i), continuous_toFun := ... }`.

So `(mFourier k) x = ∏ i, fourier (k i) (x i) = fourier (k 0) (x 0) * fourier (k 1) (x 1)` (for `d = Fin 2`, via `Fin.prod_univ_two`).

The slug's `multiFourierCoeff` integrand has `f x * fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1)` (slug line 91-92). The sign on `k 0, k 1` is the **negative** here (`-k`), matching Mathlib's `mFourierCoeff f n := ∫ t, mFourier (-n) t • f t`. The slug's `sphPartialSum` uses the *positive* sign for the resynthesis: `multiFourierCoeff f k * fourier (k 0) (x 0) * fourier (k 1) (x 1)` (slug line 113-114).

### Bridge `multiFourierCoeff_eq_mFourierCoeff` (S2e Step (b))

The S2e PREP Step (b) (line 138-142) is essentially correct:

```lean
private theorem multiFourierCoeff_eq_mFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) :
    multiFourierCoeff f k = mFourierCoeff f k := by
  unfold multiFourierCoeff mFourierCoeff
  congr 1; ext x
  simp [UnitAddTorus.mFourier, Fin.prod_univ_two, mul_comm, mul_left_comm, mul_assoc]
```

Caveats:
1. The S2e PREP has `multiFourierCoeff f k = mFourierCoeff f k` directly. But after S2f's audit, the `volume` ↔ `haarT2` measure mismatch leaks here too: `multiFourierCoeff f k = ∫ x, ... ∂haarT2`, while `mFourierCoeff f k = ∫ t, mFourier (-k) t • f t` (default `volume`). The `congr 1` step has to handle this. **One fix**: `unfold` both, then explicitly `rw [volume_eq_haarT2]` (the lemma S2f PREP introduced) inside the `∫ ... ∂_` argument via `MeasureTheory.integral_congr`.
2. The `smul_eq_mul` rewrite is needed because `mFourierCoeff` uses `•` (heterogeneous-scalar form `mFourier (-n) t • f t`) while the slug uses `*` (concrete `ℂ` multiplication). For `E = ℂ`, `c • z = c * z` by `Complex.smul_def` or the universally available `smul_eq_mul` for `ℂ` as a `ℂ`-algebra over itself.
3. The factor ordering: `mFourierCoeff` has the character on the LEFT of `f`; the slug has the character on the RIGHT of `f`. Resolved by `mul_comm` after unfolding the product.

**Net Step (b) estimate**: ~5-7 LOC including the measure-cast (~3 LOC) and the factor-reordering (~2-4 LOC).

### §1 Revised Step (c) skeleton (corrected)

Recommended architecture: **define an Lp-level partial sum**, prove pointwise a.e. equality to the function-level `sphPartialSum`, then transfer `eLpNorm` via `eLpNorm_congr_ae`:

```lean
/-- The Lp-level spherical partial sum, defined directly at the Lp layer. -/
private noncomputable def sphPartialSumLp
    (fL2 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))) (R : ℝ) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  ∑ k ∈ latticeDisc R, mFourierCoeff fL2 k • mFourierLp 2 k

/-- The function-level sphPartialSum equals (a.e.) the Lp-level partial sum's
    coercion. Note: this uses an inductive `Lp.coeFn_finset_sum` helper since
    Mathlib does not expose this as a named lemma. -/
private theorem sphPartialSum_ae_eq_sphPartialSumLp
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) (R : ℝ) :
    sphPartialSum f R =ᵐ[haarT2] sphPartialSumLp (volume_eq_haarT2.symm ▸ hf).toLp R := by
  sorry  -- ~15-20 LOC: needs Lp.coeFn_finset_sum + coeFn_mFourierLp + Fin.prod_univ_two
```

**Revised LOC for Step (c)**: ~15-25 LOC (was 5 in S2e), including the `Lp.coeFn_finset_sum` inductive helper if shipped inline.

## §2. Step (d) audit — main `Tendsto`

### What S2e proposes (lines 158-172)

```lean
theorem sphPartialSum_L2_norm_converge
    (f : T2 → ℂ) (hf : MemLp f 2 haarT2) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2)
      atTop (𝓝 0) := by
  set fL2 : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) := hf.toLp f
  have hHasSum : HasSum (fun k : Fin 2 → ℤ => mFourierCoeff fL2 k • mFourierLp 2 k) fL2 :=
    hasSum_mFourier_series_L2 fL2
  sorry  -- "~10 lines: HasSum.tendsto_sum_nat-style + cofinality + Lp ↔ eLpNorm conversion"
```

The 10-LOC estimate has three sub-tasks; let us audit each.

### §2.1. `HasSum` → `Tendsto` over `Finset.atTop`

`HasSum` is defined (`Mathlib/Topology/Algebra/InfiniteSum/Defs.lean` at pinned rev) as:

```lean
def HasSum (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β => ∑ i ∈ s, f i) atTop (𝓝 a)
```

So **`hHasSum` IS already a `Tendsto`** in disguise. No conversion lemma needed; just unfold or use `HasSum.tendsto_sum_atTop`-style destructor.

Quick check: `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean` has `HasSum.tendsto_atTop`? Or is `HasSum` already a `Tendsto` definitionally?

```bash
grep -n "^def HasSum\|HasSum.tendsto" Mathlib/Topology/Algebra/InfiniteSum/Defs.lean Mathlib/Topology/Algebra/InfiniteSum/Basic.lean
```

In pinned rev `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`, `HasSum f a := Tendsto ... atTop (𝓝 a)` directly. So `hHasSum` unfolds to a `Tendsto`. **0 LOC needed for this step.**

### §2.2. `latticeDisc atTop` cofinality (compose with Step (e))

The `Filter.Tendsto.comp` lemma (standard, `Mathlib/Order/Filter/Basic.lean` pinned rev) says:

```lean
theorem Filter.Tendsto.comp {f : α → β} {g : β → γ}
    {l₁ : Filter α} {l₂ : Filter β} {l₃ : Filter γ}
    (hg : Tendsto g l₂ l₃) (hf : Tendsto f l₁ l₂) : Tendsto (g ∘ f) l₁ l₃
```

Specialize:
- `f := latticeDisc : ℝ → Finset (Fin 2 → ℤ)`
- `g := fun s => ∑ k ∈ s, mFourierCoeff fL2 k • mFourierLp 2 k`
- `l₁ := atTop` (on `ℝ`)
- `l₂ := atTop` (on `Finset (Fin 2 → ℤ)`, with `⊆`-order)
- `l₃ := 𝓝 fL2`
- `hg := hHasSum`
- `hf := latticeDisc_atTop`  ← Step (e)

Result: `Tendsto (fun R => ∑ k ∈ latticeDisc R, mFourierCoeff fL2 k • mFourierLp 2 k) atTop (𝓝 fL2)`.

**LOC**: ~3 LOC (just write `(hHasSum.comp latticeDisc_atTop)`).

### §2.3. `Tendsto` of Lp element → `Tendsto` of `eLpNorm`

We have `Tendsto (fun R => sphPartialSumLp fL2 R) atTop (𝓝 fL2)`. We want `Tendsto (fun R => eLpNorm (sphPartialSum f R - f) 2 haarT2) atTop (𝓝 0)`.

Step (a) chain:
1. `Tendsto (fun R => sphPartialSumLp fL2 R) atTop (𝓝 fL2)` (from §2.2)
2. ↔ `Tendsto (fun R => sphPartialSumLp fL2 R - fL2) atTop (𝓝 0)` (use `Filter.Tendsto.sub_const` or `Tendsto.const_sub`)
3. ↔ `Tendsto (fun R => ‖sphPartialSumLp fL2 R - fL2‖) atTop (𝓝 0)` (norm-continuity, `tendsto_norm_zero_iff`)
4. ↔ `Tendsto (fun R => eLpNorm (sphPartialSum f R - f) 2 haarT2).toReal atTop (𝓝 0)` (Lp norm definition: `Lp.norm_def : ‖f‖ = (eLpNorm f p μ).toReal`)
5. Lift `.toReal → ENNReal` via `Tendsto.ennreal_ofReal` (or `Filter.Tendsto.comp tendsto_coe`) — except `eLpNorm` lands in `ℝ≥0∞`, not `ℝ`.

The last step is where the **`eLpNorm` vs `Lp.norm` impedance mismatch** shows up. The slug's goal is `Tendsto (fun R => eLpNorm (...) 2 haarT2) atTop (𝓝 0)` (in `ℝ≥0∞`), not `Tendsto (fun R => ‖.‖) atTop (𝓝 0)` (in `ℝ`).

Useful Mathlib lemmas (pinned rev):
- `Lp.norm_def`: `‖f‖ = (eLpNorm f p μ).toReal` (in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:205` and surrounding)
- `Lp.coeFn_sub`: `⇑(f - g) =ᵐ[μ] f - g` (lpbasic:198)
- `eLpNorm_congr_ae`: `f =ᵐ[μ] g → eLpNorm f p μ = eLpNorm g p μ` (in `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`, standard)
- For converting `Tendsto ... (𝓝 (0 : ℝ≥0∞))` ↔ `Tendsto ... (𝓝 (0 : ℝ))`: `ENNReal.tendsto_toReal_iff` (`Mathlib/Topology/Instances/ENNReal/Basic.lean`)

### §2.4. Required bridge identity

```lean
-- Bridge: eLpNorm of function-level subtraction = ‖.‖ of Lp-level subtraction.
have hEq : ∀ R : ℝ,
    eLpNorm (fun x => sphPartialSum f R x - f x) 2 haarT2
      = ENNReal.ofReal ‖sphPartialSumLp fL2 R - fL2‖ := by
  intro R
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  congr 1
  refine eLpNorm_congr_ae ?_
  -- a.e. equality between `sphPartialSum f R - f` and `sphPartialSumLp fL2 R - fL2` (as functions):
  -- LHS at x: sphPartialSum f R x - f x
  -- RHS at x: (sphPartialSumLp fL2 R) x - fL2 x   (via Lp.coeFn_sub then per-summand coeFn_mFourierLp)
  filter_upwards [sphPartialSum_ae_eq_sphPartialSumLp f hf R, MemLp.coeFn_toLp hf] with x h1 h2
  -- And use volume_eq_haarT2 to bridge measures if needed.
  sorry
```

**LOC**: ~8-12 LOC for the `hEq` bridge + ~3 LOC for the `Tendsto` chain step 1-3 + ~5 LOC for the ENNReal conversion in step 4-5.

### Net Step (d) estimate

| Sub-step | S2e PREP | Audit-revised | Why |
|---|---|---|---|
| `set fL2 := hf.toLp f` | 1 LOC | 2-3 LOC | needs `volume_eq_haarT2` cast from S2f Step (a) |
| `hHasSum := hasSum_...` | 1 LOC | 1 LOC | unchanged |
| `hHasSum.comp latticeDisc_atTop` | 0 LOC (implicit) | 1-3 LOC | explicit step |
| `Tendsto → Tendsto.sub_const` | (none) | ~3 LOC | S2e PREP glossed |
| `tendsto_norm_zero_iff` | (none) | ~3 LOC | S2e PREP glossed |
| `Lp.norm_def` + ENNReal.ofReal/toReal | (none) | ~5-8 LOC | S2e PREP glossed |
| `eLpNorm_congr_ae` bridge | (none) | ~5-10 LOC | needs Step (c) helper |
| **Total** | **~10 LOC (with 1 sorry)** | **~20-30 LOC** | factor of 2-3 over S2e estimate |

## §3. Step (e) audit — `latticeDisc_atTop : Tendsto latticeDisc atTop atTop`

### What S2e proposes (lines 177-179)

```lean
private theorem latticeDisc_cofinal :
    ∀ (S : Finset (Fin 2 → ℤ)), ∃ R₀ : ℝ, ∀ R ≥ R₀, S ⊆ latticeDisc R := by
  sorry  -- "~10 lines: induct on Finset.max'; explicit `R₀ = (S.sup ‖·‖) + 1`"
```

### Restate as Mathlib-standard `Tendsto`

The shape of "Tendsto over `R → ∞` of a `Finset`-valued function" is `Tendsto latticeDisc atTop atTop` (since `Finset` has the `⊆`-order, and `atTop` over Finsets = "cofinal" = "all eventual finsets contain a given fixed finset"). This unfolds via `tendsto_atTop_atTop` at `Mathlib/Order/Filter/AtTopBot/Basic.lean:214` (pinned rev) to:

```lean
Tendsto latticeDisc atTop atTop ↔ ∀ S : Finset (Fin 2 → ℤ), ∃ R₀ : ℝ, ∀ R ≥ R₀, S ⊆ latticeDisc R
```

which is exactly the S2e PREP shape. (The `Monotone` variant `tendsto_atTop_atTop_iff_of_monotone` at line 220 would require `latticeDisc` monotone in `R`, which **fails for `R ≤ 0`** because `⌈|R|⌉` decreases as `R → -∞`. Use the direct ∀∃ form.)

### Explicit `R₀` for `S`

For each `k ∈ S`:
- Need `k ∈ Finset.Icc (fun _ => -⌈|R|⌉) (fun _ => ⌈|R|⌉)`, i.e. `|k 0| ≤ ⌈|R|⌉ ∧ |k 1| ≤ ⌈|R|⌉`
- Need `(k 0 : ℝ)² + (k 1 : ℝ)² ≤ R²`

Both close if `R ≥ M * Real.sqrt 2 + 1` where `M = max k∈S, max(|k 0|, |k 1|)` (as a real). For empty S, R₀ = 0 works trivially.

Concrete:
- `M := (S.image (fun k => (k 0).natAbs ⊔ (k 1).natAbs)).max.getD 0` (the maximal component sup-abs, with 0 default for empty)
- `R₀ := (M : ℝ) * Real.sqrt 2 + 1`

For `R ≥ R₀`:
- `⌈|R|⌉ ≥ M` (since `R ≥ M*√2 + 1 ≥ M` and `⌈·⌉` is monotone in `|R|`)
- So `|k 0| ≤ M ≤ ⌈|R|⌉` and `|k 1| ≤ M ≤ ⌈|R|⌉` give `k ∈ bbox`
- `(k 0 : ℝ)² + (k 1 : ℝ)² ≤ M² + M² = 2M² ≤ (M*√2)² ≤ R₀² ≤ R²`

### Mathlib API audit for Step (e)

- `Finset.max` (sup over a finset, returning `WithBot α`): `Mathlib/Data/Finset/Lattice/Lemmas.lean` (pinned rev). Returns `none` for empty.
- `Finset.sup` (`Mathlib/Data/Finset/Lattice/Fold.lean`): preferred for `LinearOrder` types with bottom. For `ℕ`, `Finset.sup s f : ℕ` returns 0 for empty.
- **Preferred form**: `(S.image (fun k => (k 0).natAbs.max (k 1).natAbs)).sup id : ℕ` (with 0 default).
- `Int.natAbs_le_iff_sq_le` or similar: `(n.natAbs : ℝ)² = (n : ℝ)²` via `Int.cast_natAbs` + `Real.sq_abs`.
- `Real.sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2` (in `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` or `Mathlib/Analysis/SpecialFunctions/Sqrt.lean`).
- `Int.le_ceil_iff` / `Nat.le_ceil` for `⌈|R|⌉` bounds.

### Skeleton (revised)

```lean
private theorem latticeDisc_atTop :
    Tendsto latticeDisc atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro S
  classical
  -- Maximal sup-abs across components, with 0 default for empty.
  set M : ℕ := (S.image fun k => (k 0).natAbs ⊔ (k 1).natAbs).sup id with hM_def
  use (M : ℝ) * Real.sqrt 2 + 1
  intro R hR
  intro k hk
  rw [latticeDisc, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · -- k ∈ bbox
    rw [Finset.mem_Icc]
    refine ⟨fun i => ?_, fun i => ?_⟩
    all_goals {
      -- |k i| ≤ M ≤ ⌈|R|⌉
      have : (k i).natAbs ≤ M := by
        refine Finset.le_sup (f := id) ?_
        refine Finset.mem_image.mpr ⟨k, hk, ?_⟩
        fin_cases i <;> simp [hM_def, Nat.le_max_left, Nat.le_max_right]
      sorry  -- ~5 LOC: |k i| ≤ M ≤ ⌈|R|⌉ via Nat.le_ceil + monotonicity
    }
  · -- (k 0 : ℝ)² + (k 1 : ℝ)² ≤ R²
    have h0 : ((k 0).natAbs : ℝ) ≤ M := by exact_mod_cast Finset.le_sup ... -- as above
    have h1 : ((k 1).natAbs : ℝ) ≤ M := ...
    have : ((k 0 : ℝ))^2 + ((k 1 : ℝ))^2 ≤ 2 * (M : ℝ)^2 := by
      rw [← Int.cast_natAbs, ← Int.cast_natAbs]  -- on the two casts
      nlinarith [sq_nonneg ((M : ℝ) - (k 0).natAbs), sq_nonneg ((M : ℝ) - (k 1).natAbs)]
    have hR2 : 2 * (M : ℝ)^2 ≤ R^2 := by
      have hRR : (M : ℝ) * Real.sqrt 2 + 1 ≤ R := hR
      nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2,
                 Nat.cast_nonneg (M)]
    linarith
```

**LOC**: ~25-30 LOC realistic. The S2e PREP estimate of "~10 lines" is honest only if the bbox bound is folded into the disc bound (so we skip the bbox piece — but then `Finset.mem_filter` requires `k ∈ bbox` AND disc inequality, so we cannot skip).

## §4. eLpNorm ↔ Lp.norm bridge — Mathlib API audit

Verified at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Symbol | Path | Line | Role |
|---|---|---|---|
| `Lp.norm_def` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` | (search: defines `‖f‖ = (eLpNorm f p μ).toReal`) | the bridge: Lp.norm ↔ eLpNorm.toReal |
| `Lp.eLpNorm_ne_top` | same | uses `Lp.mem_Lp_iff_eLpNorm_lt_top` | needed for `ofReal_toReal` |
| `ENNReal.ofReal_toReal` | `Mathlib/Data/ENNReal/Basic.lean` | (standard) | when `a ≠ ∞`, `ENNReal.ofReal a.toReal = a` |
| `eLpNorm_congr_ae` | `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` | (standard) | `f =ᵐ[μ] g → eLpNorm f p μ = eLpNorm g p μ` |
| `MemLp.coeFn_toLp` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:110` | `hf.toLp f =ᵐ[μ] f` | per-side a.e. equality |
| `MemLp.toLp_sub` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:132` | `(hf.sub hg).toLp (f - g) = hf.toLp f - hg.toLp g` | needed to relate `(sphPartialSum f R - f).toLp` and `sphPartialSumLp fL2 R - fL2` |
| `Lp.coeFn_sub` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:198` | `⇑(f - g) =ᵐ[μ] f - g` | converting Lp-level subtraction back |

### Verification command

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  --jq '.content' | base64 -d > /tmp/lpbasic.lean
grep -n "MemLp.toLp\b\|MemLp.coeFn_toLp\|Lp.coeFn_sub\|MemLp.toLp_sub\|norm_def" /tmp/lpbasic.lean
```

## §5. Revised LOC budget

Cumulative across S2e → S2f → S2g audits:

| Step | S2e PREP estimate | S2f-revised | **S2g-revised (this audit)** | Net |
|---|---|---|---|---|
| (a) `haarT2_eq_volume` | 1-3 | 5-6 | 5-6 | (unchanged from S2f) |
| (b) `multiFourierCoeff_eq_mFourierCoeff` | ~3 | ~3 | 5-7 | +2-4 (measure-cast + factor reorder) |
| (c) `sphPartialSum_eq_finset_sum` | ~5 (sorry) | ~5 (sorry) | **15-25** (incl. `Lp.coeFn_finset_sum` helper) | +10-20 |
| (d) main `Tendsto` proof | ~10 (sorry) | 12-13 (sorry) | **20-30** (incl. eLpNorm bridge) | +8-17 |
| (e) `latticeDisc_atTop` | ~10 (sorry) | ~10 (sorry) | **25-30** (explicit `R₀`) | +15-20 |
| `volume_eq_haarT2` from S2f | - | - | (same) | 5-6 |
| **Total** | **~30 LOC** | **~35-50 LOC** | **~70-95 LOC** | **+30-50 over S2f** |

The S2e PREP's "~30 LOC" estimate is **roughly 2.5× under the realistic ACT budget**, primarily because:

1. `Lp.coeFn_finset_sum` is **not a named Mathlib lemma** — must be proved inline (~10 LOC).
2. The `eLpNorm`↔`Lp.norm` bridge requires explicit `ENNReal.ofReal_toReal` + `Lp.norm_def` + per-side `coeFn` + congruence — never enumerated in S2e (~10 LOC).
3. The `latticeDisc_atTop` Mathlib API audit shows the bbox + disc-inequality double obligation can't be folded; both must be discharged (~25 LOC vs 10).

### What the S2e thesis still gets right

Even with the revised 70-95 LOC budget, **citing `mFourierBasis` still wins over building Plancherel from scratch**:
- Custom `Plancherel_ntorus` build: ~80-150 LOC (S1/S2a state.md estimate).
- `mFourierBasis` bridge with this audit's adjustments: ~70-95 LOC.

The 10-80 LOC savings is real but modest. The qualitative win is **architectural alignment with Mathlib** (using the named basis), not LOC reduction.

## §6. Risk register (S2g additions)

Beyond the S2e risk table (line 237-239 of #18446) and S2f's expanded register (line 213-221 of #18545):

| Risk | Severity | Mitigation |
|---|---|---|
| `Lp.coeFn_finset_sum` inductive helper hits `decidableEq` instance synthesis issue | **Low** | `classical` before `Finset.induction_on` |
| `Lp.norm_def` may be marked `noncomputable` and not rewrite-friendly | **Low** | use `simp_rw [Lp.norm_def]` or `show .... = ((eLpNorm _ _ _).toReal : ℝ)` |
| `MemLp.toLp_sub` requires both `MemLp f` and `MemLp g`; for `g = f` constant the `(MemLp.const).sub hf` requires `MemLp (constant) 2 haarT2`, which requires `IsFiniteMeasure haarT2` | **Medium** | `MemLp.const_of_isFiniteMeasure`; `haarT2` IS finite (probability measure on `T²`); cite `IsProbabilityMeasure` instance |
| `Tendsto.const_sub` (or `Tendsto.sub_const`) in a normed group — check existence | **Low** | `Filter.Tendsto.sub` with `tendsto_const_nhds`; standard |
| `Real.sqrt_two_mul_self` form vs `Real.sq_sqrt` form | **Low** | both available; use whichever fits `nlinarith` |
| `latticeDisc` factors through `⌈|R|⌉` — `Int.cast` of `Nat.ceil` vs `Int.ceil` of `Real` | **Low** | the slug uses `Int.ceil`; `Nat.le_ceil` and `Int.le_ceil` are both available |
| `Fin.prod_univ_two` form may not unfold `mFourier (-k) t` cleanly | **Medium** | explicit unfold: `mFourier (-k) t = ∏ i, fourier (-(k i)) (t i) = fourier (-(k 0)) (t 0) * fourier (-(k 1)) (t 1)` via `Fin.prod_univ_two : ∏ i, f i = f 0 * f 1` |
| `volume_eq_haarT2` from S2f Step (a) interacts with `Lp ℂ 2 (volume ...)` vs `Lp ℂ 2 haarT2` — these are equal-as-types only after measure-rewrite | **Medium-High** | this is the **load-bearing** Step (c)/(d) issue. The S2f bridge corrects the measure on `MemLp` but the `Lp` type itself encodes the measure as a parameter. Use `Lp.congr_measure`-style lemma if it exists, or transfer via `(volume_eq_haarT2 ▸ hf).toLp f` rewriting trick |

## §7. Orthogonality to in-flight PRs (at audit time 08:20 UTC, 2026-05-13)

| PR | Phase | Focus | Conflict with S2g PREP? |
|---|---|---|---|
| #18062 (MERGED) | S1 OBSERVE | territory map | no — base |
| #18165 (MERGED) | S2a ACT scaffold | axiom + sorry + sanity lemmas | no — pre-existing |
| #18255 (MERGED) | S2c | bbox subset+card bounds | no — pre-existing |
| #18393 (MERGED) | S2d PREP | explicit bbox cardinality | no — orthogonal Lean target (bbox) |
| #18446 (MERGED) | S2e PREP | mFourierBasis L² discharge | partial target — audit Step (c)/(d)/(e) |
| #18545 (MERGED) | S2f PREP | volume/haarT2 rfl errata | predecessor — audit Step (a) (this PREP picks up Steps (c)/(d)/(e)) |
| #18167 (OPEN) | audit(tracker) | tracker housekeeping | no — separate domain |
| #18175 (OPEN) | enrichment | annotations + cross-refs | no — gallery file domain |
| **#this** | S2g PREP audit (c)/(d)/(e) | Lp coeFn + cofinality + eLpNorm bridge | — |

Zero edits to: `problem.md`, `knowledge.md`, `state.md`, gallery `meta.json` / `index.ts` / `annotations.json`, Lean file `FourierSeriesOQ04OQ01.lean`. All six untouched. New file: `sessions/2026-05-13-s2g-prep-mathlib-audit-steps-c-d-e.md`.

## §8. What this PREP does NOT address

1. **The `carleson_2d_sph` axiom**. Genuinely open mathematics (Stein 1971; Tao 2002). Unchanged across all S2 PREPs.
2. **The S2b Bochner–Riesz path** (state.md line 93-101, ~300-500 LOC). Distinct from S2e/f/g; not in scope.
3. **The S2d explicit `bbox.card = (2⌈|R|⌉+1)²` formula** (PR #18393). Distinct mathematical target (cardinality vs convergence).
4. **The actual S2e ACT**. This PREP refines the LOC estimate to 70-95 (vs S2e's 30 vs S2f's 35-50); the ACT itself requires docker build verification and is a separate follow-up.
5. **Mathlib contributions**. The audit suggests upstream-worthy additions:
   - `Lp.coeFn_finset_sum {ι} (s : Finset ι) (f : ι → Lp E p μ) : ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, f i x` (analog of `Lp.coeFn_add`)
   - A specialised `Lp.norm_sub_def` lemma combining `Lp.norm_def` and `Lp.coeFn_sub` for the typical use case `‖f - g‖ = ENNReal.ofReal (eLpNorm (⇑f - ⇑g) p μ)`
   These are project-local for now; ship the bridge first, upstream later.
6. **Refactoring `multiFourierCoeff` to use `mFourierCoeff` directly** (eliminating the bridge). Anti-target per S2e/f; ship the bridge first.

## §9. Honesty

- This is a **PREP** (audit-correction planning document), not an ACT (no Lean changes, no build).
- The +20-40 LOC revision is qualitative — informed by reading the Mathlib snapshot, but not by running an actual Lean elaboration. The real `lake build` cost is what determines the final LOC count; this audit only adjusts the *floor* of the estimate.
- I have not built the file locally. The worktree `proofs/.lake` symlink is known recursive (MEMORY.md `[.lake symlink loop + mid-build worktree wipe]`); a docker build would take ~25-45 min and is not warranted for a doc-only audit.
- The "no named `Lp.coeFn_finset_sum`" claim is verified against `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` and `Mathlib/MeasureTheory/Function/AEEqFun.lean` at pinned rev. Mathlib could have it hidden under a different name (e.g., `Finset.sum_coeFn`); my searches found nothing matching, but absence-of-evidence is weaker than evidence-of-absence here.
- The Step (e) skeleton (§3) has 2 `sorry`s; these are the "5 LOC" `nlinarith`-style closures, not the structural argument. The structural argument (∀∃ + monotone bbox + disc inequality) is sound.
- I have NOT verified that `Tendsto.const_sub` exists by that exact name in pinned Mathlib; my §2.3 chain uses a representative API name. The ACT engineer should confirm via `gh api search/code` before relying on it. (Failure mode: it's named `Filter.Tendsto.sub` with `tendsto_const_nhds` as the constant tendsto — both are unambiguously present.)
- The Step (b) factor-ordering issue (Mathlib's `•` on the LEFT of `f`; slug's `*` on the RIGHT) is *commutative* for `ℂ` and `mul_comm` closes it; for a non-commutative scalar (which doesn't apply here) the bridge would have a sign / order issue.

## §10. References (all verified at pinned Mathlib rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

### Mathlib paths and line numbers

- `Mathlib/Analysis/Fourier/AddCircleMulti.lean` (274 lines):
  - line 43 — `abbrev UnitAddTorus (d : Type*) := d → UnitAddCircle`
  - line 54 — `def mFourier : C(UnitAddTorus d, ℂ)`
  - line 150 — `abbrev mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ)`
  - line 154-156 — `theorem coeFn_mFourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) : mFourierLp p n =ᵐ[volume] mFourier n`
  - line 165 — `theorem span_mFourierLp_closure_eq_top`
  - line 172 — `theorem orthonormal_mFourier`
  - line 193 — `def mFourierCoeff (f : UnitAddTorus d → E) (n : d → ℤ) : E := ∫ t, mFourier (-n) t • f t`
  - line 199 — `local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)` ← **local notation, not usable outside this file**
  - line 204 — `def mFourierBasis : HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)`
  - line 210 — `theorem coe_mFourierBasis`
  - line 214 — `theorem mFourierBasis_repr`
  - line 224 — `theorem hasSum_mFourier_series_L2 (f : L²(UnitAddTorus d)) : HasSum (fun i ↦ mFourierCoeff f i • mFourierLp 2 i) f`
- `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` (893 lines):
  - line 105 — `def MemLp.toLp (f : α → E) (h_mem_ℒp : MemLp f p μ) : Lp E p μ`
  - line 110 — `theorem MemLp.coeFn_toLp {f : α → E} (hf : MemLp f p μ) : hf.toLp f =ᵐ[μ] f`
  - line 113 — `theorem MemLp.toLp_congr`
  - line 117 — `theorem MemLp.toLp_eq_toLp_iff`
  - line 124 — `theorem MemLp.toLp_add`
  - line 128 — `theorem MemLp.toLp_neg`
  - line 132 — `theorem MemLp.toLp_sub`
  - line 144 — `theorem Lp.ext`
  - line 163 — `theorem Lp.toLp_coeFn`
  - line 195 — `theorem Lp.coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g`
  - line 198 — `theorem Lp.coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g`
  - line 205 — `instance Lp.instNorm : Norm (Lp E p μ)` (defines `‖f‖ := (eLpNorm f p μ).toReal`)
  - line 423 — `theorem Lp.coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • ⇑f`
  - **NO `Lp.coeFn_finset_sum` lemma** — gap noted in §1
- `Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`:
  - line 161 — `theorem memLp_finset_sum (s : Finset ι) (hf : ∀ i ∈ s, MemLp (f i) p μ) : MemLp (fun a => ∑ i ∈ s, f i a) p μ`
  - line 172 — `theorem memLp_finset_sum'` (using `∑ i ∈ s, f i` style)
- `Mathlib/MeasureTheory/Function/AEEqFun.lean`:
  - line 648 — `theorem AEEqFun.coeFn_smul`
  - lines 43, ~196 — `coeFn_add/sub/neg/smul` family (used by Lp variants)
- `Mathlib/Order/Filter/AtTopBot/Basic.lean`:
  - line 214 — `theorem tendsto_atTop_atTop : Tendsto f atTop atTop ↔ ∀ b, ∃ i, ∀ a, i ≤ a → b ≤ f a`
  - line 220 — `theorem tendsto_atTop_atTop_iff_of_monotone (hf : Monotone f) : Tendsto f atTop atTop ↔ ∀ b, ∃ a, b ≤ f a`
- `Mathlib/Analysis/Fourier/AddCircle.lean`:
  - line 85 — `def haarAddCircle`
  - line 92 — `theorem volume_eq_smul_haarAddCircle` (load-bearing for S2f Step (a))
- `Mathlib/MeasureTheory/Constructions/Pi.lean`:
  - line 214 — `instance MeasureSpace.pi`
- `Mathlib/Data/ENNReal/Basic.lean`:
  - line 283 — `@[simp] theorem ofReal_one`

### Slug-internal references (`proofs/Proofs/FourierSeriesOQ04OQ01.lean` at HEAD `0cbd962f6bc`)

- line 73 — `abbrev T2 : Type := Fin 2 → AddCircle (1 : ℝ)`
- line 80-82 — `noncomputable def haarT2 : Measure T2 := Measure.pi fun _ => (haarAddCircle : Measure (AddCircle (1 : ℝ)))`
- line 91-92 — `noncomputable def multiFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) : ℂ := ∫ x, f x * fourier (-(k 0)) (x 0) * fourier (-(k 1)) (x 1) ∂haarT2`
- line 100-105 — `noncomputable def latticeDisc (R : ℝ) : Finset (Fin 2 → ℤ)`
- line 113-114 — `noncomputable def sphPartialSum (f : T2 → ℂ) (R : ℝ) (x : T2) : ℂ`
- line 148-160 — `theorem sphPartialSum_L2_norm_converge` (the target of the S2e ACT, when it lands)

### Predecessor PRs (audit chain)

- #18446 `sessions/2026-05-13-s2e-prep-mFourierBasis-l2-discharge.md` (the structural plan)
- #18545 `sessions/2026-05-13-s2f-prep-mathlib-api-audit-correcting-s2e.md` (Step (a) audit)
- #this — Steps (c), (d), (e) audit

The audit chain S2e → S2f → S2g forms a complete pre-flight Mathlib API verification for the S2e ACT. The next step is either:
- **S2e ACT** (researcher with docker build) — implement the corrected 70-95 LOC plan from scratch
- **S2h** (further audit) — verify Step (b) measure-cast machinery in detail, or scout for `Lp.coeFn_finset_sum` upstream contribution opportunities
- **S2d ACT** — orthogonal to S2e/f/g; implement the explicit bbox cardinality formula from PR #18393's PREP
