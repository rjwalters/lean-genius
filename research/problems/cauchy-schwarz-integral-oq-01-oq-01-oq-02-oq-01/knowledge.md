# cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01: Riesz Lp Surjectivity via Radon-Nikodým

**Problem**: Can Mathlib's RN machinery (SignedMeasure.rnDeriv) prove that every φ ∈ (Lp)* is represented by integration against some g ∈ Lq?

**Status**: PROGRESS — hMCT re-proved (3→2 sorries); 2 hard sorries remain

**Lean file**: `Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`

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
