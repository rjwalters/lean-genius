# cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01: Riesz Lp Surjectivity via Radon-Nikodým

**Problem**: Can Mathlib's RN machinery (SignedMeasure.rnDeriv) prove that every φ ∈ (Lp)* is represented by integration against some g ∈ Lq?

**Status**: PROGRESS — 1 critical sorry remaining (holder_extremizer_lq_bound); indicator_lp_hasSum proved

**Lean file**: `Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`

---

## Session 2026-04-22 (Session 5) — indicator_lp_hasSum proved

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Proved `indicator_lp_hasSum`** (~80 lines) — the σ-additivity step for the Lp signed measure construction.

   The proof uses:
   - Identify each Lp term as `indicatorConstLp` via `Lp.ext` + `indicatorConstLp_coeFn`
   - Prove partial Lp sums = `indicatorConstLp` of biUnion via `Finset.indicator_biUnion_apply` (additive version of `Finset.mulIndicator_biUnion_apply`)
   - Convert `HasSum` to `Tendsto atTop` via definitional equality (from `@[simps] def unconditional : SummationFilter β where filter := atTop`)
   - Apply `tendsto_indicatorConstLp_set` to reduce to measure of symmetric differences
   - Use `symmDiff_of_le` + `Set.iUnion_subtype` + `measure_iUnion` to compute μ(symmDiff)
   - Close with `ENNReal.tendsto_tsum_compl_atTop_zero` for tail measure convergence

2. **Confirmed**: `rnDeriv_integrable_of_finite` is already proved at line 740 via `SignedMeasure.integrable_rnDeriv ν μ` (one-liner — no sorry).

3. **Updated assessment**: 2 sorries remain total:
   - `truncated_rn_deriv_lq_bound` (not on critical path, MARKED FALSE)
   - `holder_extremizer_lq_bound` (1 critical sorry)

### Key Findings

- `HasSum` is definitionally `Tendsto (fun S => ∑ i ∈ S, f i) atTop (nhds a)` because `(unconditional β).filter = atTop` by `@[simps]` definition. Use `show Tendsto ... atTop ...` to expose this.
- `Finset.indicator_biUnion_apply` is the additive analogue of `Finset.mulIndicator_biUnion_apply` — for pairwise disjoint sets, the indicator of a union = sum of indicators.
- `symmDiff_of_le` (in `Order/SymmDiff.lean:125`) says `a ∆ b = b \ a` when `a ≤ b` (i.e., a ⊆ b). Key for computing `symmDiff (⋃ i ∈ S, f i) (⋃ i, f i) = ⋃ i ∉ S, f i`.
- `Set.iUnion_subtype` rewrites `⋃ i : {x // P x}, t i = ⋃ x, ⋃ hx : P x, t ⟨x, hx⟩` — needed to convert `⋃ i ∉ S, f i` to a form where `measure_iUnion` applies.

### Remaining Sorry

**`holder_extremizer_lq_bound`** (1 critical sorry):
- Goal: `eLpNorm (clamp(ν.rnDeriv μ, -n, n)) q μ ≤ ENNReal.ofReal ‖φ‖`
- Mathematical approach: extremizer h = sign(gₙ)|gₙ|^{q-1} in Lp (bounded, finite measure)
  - ‖gₙ‖_q^q = ∫ h·gₙ ≤ ∫ h·g = φ(h) ≤ ‖φ‖·‖h‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
  - → ‖gₙ‖_q ≤ ‖φ‖ (algebra using q - q/p = 1)
- Hard step: proving φ(h) = ∫ h·g for bounded h (need simple-fn approx + DCT)
  - Tools: `SimpleFunc.approxOn`, `SimpleFunc.tendsto_approxOn` (pointwise), `tendsto_approxOn_Lp_eLpNorm` (Lp), `tendsto_integral_of_dominated_convergence` (DCT with bound n^{q-1}·|g| ∈ L1)
  - Simple function case: φ(∑ cᵢ 1_{Eᵢ}) = ∑ cᵢ φ(1_{Eᵢ}) = ∑ cᵢ ∫_{Eᵢ} g (by hν_eq + rnDeriv_integral_eq)

### Files Modified

- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` (indicator_lp_hasSum sorry→proof; assessment updated)

### Next Steps

1. Prove `holder_extremizer_lq_bound`:
   - Build h_n = sign(gₙ)|gₙ|^{q-1} as Lp element (Memℒp.of_bound)
   - Prove φ(s) = ∫ s·g for simple functions s (SimpleFunc.induction + hν_eq + rnDeriv_integral_eq)
   - Extend to bounded h via DCT (tendsto_integral_of_dominated_convergence)
   - Chain: ‖gₙ‖_q^q ≤ ‖φ‖·‖gₙ‖_q^{q/p} → ‖gₙ‖_q ≤ ‖φ‖ (ENNReal rpow arithmetic)

---

## Session 2026-04-21 (Session 4) — Main theorem assembled, 3 focused helpers remain

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Built `signedMeasureOfFunctional`** (0 sorries): proper `SignedMeasure` structure with all fields:
   - `measureOf E = if MeasurableSet E then φ(1_E) else 0`
   - `empty`: via `functionalSetFn_null` (μ(∅)=0 → indicator = 0 in Lp)
   - `not_measurable`: `simp [dif_neg hE]`
   - `m_iUnion`: via `functional_hasSum_parts` + `HasSum.map` (CLM continuity)

2. **Proved `signedMeasureOfFunctional_ac`** (0 sorries):
   - `μ(E) = 0 → φ(1_E) = 0` via `functionalSetFn_null`

3. **Proved `rnDeriv_integral_eq`** (depends on 1 sorry):
   - `∫_E g dμ = ν(E)` via `withDensityᵥ_apply` + `rn_reconstruction`

4. **Assembled `riesz_lp_surjective_from_rn`** (0 sorries in main theorem):
   - Step 1: construct `ν = signedMeasureOfFunctional`
   - Step 2: get `g = ν.rnDeriv μ`
   - Step 3: `hagree`: `φ(1_E) = ∫_E g dμ` (via `rnDeriv_integral_eq`)
   - Step 4: `g ∈ Lq` via `rn_deriv_memLq_from_trunc` + `holder_extremizer_lq_bound`
   - Step 5: `integral_representation` closes the goal

### Key Findings

- `HasSum.map` is the key: CLM continuity converts indicator Lp convergence → functional value convergence
- `signedMeasureOfFunctional_ac` proved without sorry: `μ(E)=0` → `indicator_{E} = 0` in Lp → `φ(0) = 0`
- The proof architecture correctly bypasses the FALSE `truncated_rn_deriv_lq_bound` by using `holder_extremizer_lq_bound` (new, correct)
- `rnDeriv_integrable_of_finite` sketch: Jordan decomp → `Integrable.sub` with `Measure.integrable_rnDeriv` twice

### Files Modified

- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` (647→819 lines, 2→4 sorries but main theorem 0-sorry)
- `src/data/research/problems/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01.json` (phase OBSERVE→ACT)

### Remaining Sorries (3 focused helpers, ~130 lines total)

1. **`indicator_lp_hasSum`** (~60 lines): Lp partial sums 1_{f i} → 1_{⋃ f i} in norm; use `tendsto_measure_iUnion_atTop`
2. **`rnDeriv_integrable_of_finite`** (~20 lines): Jordan decomp + `Integrable.sub` + `Measure.integrable_rnDeriv`
3. **`holder_extremizer_lq_bound`** (~50 lines): build h_n = sign(gₙ)|gₙ|^{q-1} ∈ Lp, then norm computation

---

## Session 2026-04-14 (Session 3) — Restore hMCT proof (3→2 sorries)

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Restored hMCT proof** in `rn_deriv_memLq`:
   - PR #10765 proved this sorry; PR #10806 accidentally reverted it
   - Re-applied the exact proof from #10765 commit c0a5d8fe5c
   - Sub-lemmas: `abs_clamp` (3-case analysis on clamping), `sup_min` (⨆ n, min x n = x in ℝ≥0∞), `norm_gn_eq` (‖gₙ‖₊ = min ‖g‖₊ n as ENNReal), `ptwise_eq` (orderIsoRpow.map_iSup)
   - Assembly: lintegral_iSup with measurability + monotonicity + simp_rw
2. **Updated meta.json**: sorries 3→2, lineCount 524→570
3. **Architecture note**: `truncated_rn_deriv_lq_bound` has wrong hypotheses (set-function bound insufficient); `rn_deriv_memLq` depends on this sorry

### Key Findings
- `truncated_rn_deriv_lq_bound` as stated may be false: set-function bound |s(E)| ≤ M·μ(E)^{1/p} does not imply ‖gₙ‖_q ≤ M without extending to full Lp functional
- hMCT proof is sound; the sorry it proves is genuine mathematical content (monotone convergence for clamped functions)
- 2 sorries remain: `truncated_rn_deriv_lq_bound` (needs correct hypothesis or replacement) and `riesz_lp_surjective_from_rn` (full assembly)

### Files Modified
- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` (hMCT: sorry→proof, +46 lines)
- `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01/meta.json` (sorries 3→2)

### Next Steps
1. Fix `truncated_rn_deriv_lq_bound`: change hypothesis from set-function bound to direct functional bound ‖φ‖ ≤ M, then prove Hölder extremizer argument (~60 lines)
2. Alternatively: add `lq_norm_bound_from_functional` as a new intermediate lemma with the correct hypothesis
3. Once `truncated_rn_deriv_lq_bound` (or replacement) is proved, `rn_deriv_memLq` becomes sorry-free
4. Final target: prove `riesz_lp_surjective_from_rn` (~80 lines of signed measure construction + assembly)

---

## Session 2026-04-14 (Session 2) — MCT + rn_deriv_memLq_from_trunc

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Proved `hMCT`** in `rn_deriv_memLq`:
   - Goal: `∫⁻ a, ‖g a‖₊^q ∂μ = ⨆ n, ∫⁻ a, ‖gₙ a‖₊^q ∂μ`
   - Method: `lintegral_iSup` with:
     - Measurability: `(hg_meas.nnnorm.coe_nnreal_ennreal.min measurable_const).pow_const q.toReal`
     - Monotonicity: `min_le_min_left _ (Nat.cast_le.mpr hmn)` + `ENNReal.rpow_le_rpow`
     - Pointwise sup: `ENNReal.orderIsoRpow.map_iSup` + `sup_min` (⨆ min x n = x)
   - Key sub-lemmas: `abs_clamp` (|max(min r n, -n)| = min|r| n), `norm_gn_eq` (‖gₙ‖₊ = min ‖g‖₊ n)

2. **Added `rn_deriv_memLq_from_trunc`** (complete, 0 sorries):
   - Takes `hgn_snorm : ∀ n, eLpNorm (fun a => max(min(g a)(n:ℝ))(-(n:ℝ))) q μ ≤ ENNReal.ofReal M`
   - Returns `Memℒp g q μ` via MCT
   - Bypasses the FALSE `truncated_rn_deriv_lq_bound` pathway
   - This is the correct building block for `riesz_lp_surjective_from_rn`

3. **Identified `truncated_rn_deriv_lq_bound` as FALSE**:
   - Counterexample: g = x^{-1/q} on [0,1] with Lebesgue measure, p = q = 2
   - The set function bound |s(E)| ≤ M·μ(E)^{1/p} does NOT bound ‖gₙ‖_q
   - The correct bound comes from φ ∈ (Lp)* directly (via Hölder extremizer)

4. **Updated `riesz_lp_surjective_from_rn`** with detailed proof sketch:
   - σ-additive signed measure ν(E) = φ(1_E) (SORRY 1, hard)
   - Hölder extremizer: ‖gₙ‖_q ≤ ‖φ‖ (SORRY 2, hard)
   - Then apply `rn_deriv_memLq_from_trunc` and `integral_representation`

5. **Sorry count**: 3 → 2 (hMCT proved; `truncated_rn_deriv_lq_bound` kept as warning)

### Key Findings

- `lintegral_iSup` needs: (1) measurability of each integrand, (2) monotonicity in n, (3) write integrand as iSup
- The critical lemma chain: `abs_clamp` → `norm_gn_eq` → `ENNReal.orderIsoRpow.map_iSup` → MCT
- `ENNReal.orderIsoRpow` is an order isomorphism that commutes with iSup: perfect for raising norm_gn_eq to q-th power
- `truncated_rn_deriv_lq_bound` uses WRONG hypotheses — the correct version needs φ directly

### Files Modified

- Modified: `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`
  - Added `rn_deriv_memLq_from_trunc` (complete, ~70 lines)
  - Proved `hMCT` in `rn_deriv_memLq` (replacing sorry)
  - Updated `riesz_lp_surjective_from_rn` with proof sketch

### Next Steps

1. **Prove σ-additive signed measure construction** (~80 lines):
   - Define ν(E) = φ(1_E) for finite E
   - σ-additivity: use Lp-convergence `1_{∪ Eₙ} - Σ_{k≤N} 1_{Eₖ} → 0 in Lp` → continuity of φ
   - Absolute continuity: `functionalSetFn_null` already proved

2. **Prove Hölder extremizer bound** (~40 lines):
   - For each n: hₙ = sign(gₙ)|gₙ|^{q-1} ∈ Lp (bounded)
   - ‖gₙ‖_q^q = ∫ hₙ gₙ ≤ ∫ hₙ g = φ(hₙ) ≤ ‖φ‖·‖hₙ‖_p = ‖φ‖·‖gₙ‖_q^{q/p}
   - Divide: ‖gₙ‖_q ≤ ‖φ‖
   - Then call `rn_deriv_memLq_from_trunc p q hp1 hptop hpq g hg_meas ‖φ‖ hgn_bound`

3. **Once both done**: apply `integral_representation` for the final assembly
