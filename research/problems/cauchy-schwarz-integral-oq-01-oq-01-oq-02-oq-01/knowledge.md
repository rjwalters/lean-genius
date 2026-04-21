# cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01: Riesz Lp Surjectivity via Radon-Nikodým

**Problem**: Can Mathlib's RN machinery (SignedMeasure.rnDeriv) prove that every φ ∈ (Lp)* is represented by integration against some g ∈ Lq?

**Status**: PROGRESS — main theorem riesz_lp_surjective_from_rn has 0 sorries; 3 focused helper sorries remain

**Lean file**: `Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`

---

## Session 2026-04-21 (Session 5) — Eliminate all 3 sorries in holder_extremizer_lq_bound

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Proved `h_norm_q_eq`** (eLpNorm gₙ^q = ofReal(∫ hₙ*gₙ)):
   - Pointwise: `sign(gₙ)|gₙ|^{q-1} * gₙ = |gₙ|^q` via sign algebra + `Real.rpow_add`
   - Chain: `eLpNorm_eq_eLpNorm'`, `← lintegral_rpow_enorm_eq_rpow_eLpNorm'`, `lintegral_congr` with `enorm_eq_ofReal_abs + ofReal_rpow_of_nonneg`, then `← ofReal_integral_eq_lintegral_ofReal`
   - Needed: measurability, integrability, nonnegativity a.e. of `|gₙ|^q`

2. **Proved `h_hn_norm`** (‖hₙ‖_p = S^(q/p)):
   - Pointwise: `|hₙ|^p = |gₙ|^q` via `(q-1)*p = q` (`hpq.symm.sub_one_mul_conj`)
   - Equal lintegrals → `eLpNorm hₙ p μ ^ p = eLpNorm gₙ q μ ^ q`
   - Take (1/p)-th power via `congr_arg (· ^ p⁻¹)` + `ENNReal.rpow_mul + mul_inv_cancel₀`
   - Assembly: `Lp.norm_def + eLpNorm_congr_ae + ENNReal.toReal_rpow`

3. **Final ENNReal assembly** (eLpNorm gₙ q μ ≤ ofReal ‖φ‖):
   - `q/p = q-1` via `hpq.symm.div_conj_eq_sub_one`
   - Write `S^q = S * S^(q-1)` via `Real.rpow_add + Real.rpow_one`
   - Cancel `S^(q-1) > 0` via `mul_le_mul_right`
   - Convert to ENNReal via `ENNReal.ofReal_toReal + ENNReal.ofReal_le_ofReal`

4. **Fixed syntax error** in `riesz_lp_surjective_from_rn`:
   - Removed `[_ : Fact (1 ≤ p)]` (Lean 4 doesn't support `[_ : T]` in theorem signatures)
   - `haveI hp1' : Fact (1 ≤ p) := ⟨le_of_lt hp1⟩` inside body provides the instance

### Key Findings

- `hpq.symm.sub_one_mul_conj : (q-1)*p = q` (via `HolderConjugate.symm` on `p.HolderConjugate q`)
- `hpq.symm.div_conj_eq_sub_one : q/p = q-1` (key for reducing `S^(q/p)` to `S^(q-1)`)
- `ENNReal.toReal_rpow : (x^z).toReal = x.toReal^z` (forward direction to unwrap)
- `ofReal_integral_eq_lintegral_ofReal` direction: `ofReal(∫f) = ∫⁻ ofReal f`; use `.symm`
- `lintegral_rpow_enorm_eq_rpow_eLpNorm'` with `←` to convert `(eLpNorm')^p → ∫⁻ ‖f‖ₑ^p`

### Files Modified

- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` (+~180 lines, 3 sorries eliminated in `holder_extremizer_lq_bound`)

### Remaining Sorries (2 total)

1. **`indicator_lp_hasSum`** (line ~570): Lp partial sums 1_{⋃ Eₙ} convergence
2. **`rnDeriv_integrable_of_finite`** (line ~175): Jordan decomp → Integrable.sub
3. **`truncated_rn_deriv_lq_bound`** (line ~175): MARKED FALSE, kept as documented dead end

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
