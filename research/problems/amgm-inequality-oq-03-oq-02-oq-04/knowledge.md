# Knowledge Base: amgm-inequality-oq-03-oq-02-oq-04

**Problem**: Formalize the extreme power mean limits:
- lim_{r→+∞} M_r(x) = max(x₁,...,xₙ)
- lim_{r→-∞} M_r(x) = min(x₁,...,xₙ)

---

## Session 2026-04-05 (Session 2)

**Outcome**: COMPLETE. `powerMean_tendsto_min` proved. 0 sorries, 0 axioms.

### What I Did

1. Proved `powerMean_tendsto_min` by duality with the max case:
   - Set `g = fun i => (x i)⁻¹`, proved `sup'(g) = (inf'(x))⁻¹` by inline antitone inversion
   - Applied `powerMean_tendsto_max g hg` → `Tendsto (powerMean g) atTop (nhds m⁻¹)`
   - Inverted via `.inv₀`: `Tendsto (fun r => (powerMean g r)⁻¹) atTop (nhds m)`
   - Identity `(powerMean g (-r))⁻¹ = powerMean x r` for r < 0 via `Real.inv_rpow` + `Real.rpow_neg` + `inv_inv`
   - Composed: `(h_inv.comp Filter.tendsto_neg_atBot_atTop).congr' h_ident`
2. Created gallery data in `src/data/proofs/amgm-inequality-oq-03-oq-02-oq-04/`

### Key Findings

- **`inv_le_inv_of_le` unknown**: Use inline calc `(x i)⁻¹ = (x i)⁻¹*(m*m⁻¹) ≤ (x i)⁻¹*(x i*m⁻¹) = m⁻¹` pattern from `AmgmInequalityPowerMeanLimits.lean`
- **`inv_ne_zero.mpr` unknown**: `inv_ne_zero` takes `a ≠ 0` directly, not an iff — use `inv_ne_zero hm_pos.ne'`
- **Outer inversion**: `((S/n)^(1/(-r)))⁻¹ = (S/n)^(1/r)` via `← Real.rpow_neg` + `congr 1; rw [div_neg, neg_neg]`
- **Sum identity**: `Σ (xᵢ⁻¹)^(-r) = Σ xᵢ^r` via `Real.inv_rpow` + `Real.rpow_neg` + `inv_inv`

### Files Modified

- `proofs/Proofs/AmgmInequalityOQ03OQ02OQ04.lean` (modified: filled `powerMean_tendsto_min`)
- `src/data/proofs/amgm-inequality-oq-03-oq-02-oq-04/` (created: meta.json, annotations.json, index.ts)

---

## Session 2026-04-03 (Session 1) — Max limit proved via squeeze theorem

**Mode**: FRESH
**Outcome**: progress

### What I Did

- Defined `powerMean` as `((∑ xᵢ^r)/n)^{1/r}` for `r ≠ 0`, geometric mean for `r = 0`
- Proved `tendsto_const_rpow_neg_inv_atTop`: c^(-1/r) → 1 as r→+∞ (via `tendsto_inv_atTop_zero.neg` and `Filter.Tendsto.rpow`)
- Proved `powerMean_le_sup`: upper bound M_r ≤ max(x) for r > 0
- Proved `sup_mul_pow_le_powerMean`: lower bound max(x)·n^(-1/r) ≤ M_r for r > 0
- Proved `powerMean_tendsto_max`: main max limit theorem via squeeze
- Left `powerMean_tendsto_min` as sorry

### Key Findings

- **`div_le_iff`/`div_le_div_right` unknown after `open Real`**: Use `le_of_mul_le_mul_left` + `mul_div_cancel₀` instead
- **`positivity` fails for `0 ≤ (∑ xᵢ^r)/n`**: Use `div_nonneg (Finset.sum_nonneg ...) (le_of_lt hn)` explicitly
- **`hrhs` identity** `M * n^(-1/r) = (M^r/n)^{r⁻¹}`: Proved via `div_rpow` + `← rpow_mul` + `mul_inv_cancel₀` + `rpow_one` + `rpow_neg` + `div_eq_mul_inv`
- **squeeze theorem**: Use `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (prime version) which takes `∀ᶠ` arguments; the non-prime version takes Pi-order
- **`Finset.single_le_sum`**: Takes 2 explicit args (hf, ha); don't pass extra `_`

### Files Modified

- `proofs/Proofs/AmgmInequalityOQ03OQ02OQ04.lean` (created)
  - 4 proved lemmas/theorems, 1 sorry (powerMean_tendsto_min)

### Next Steps

1. Prove `powerMean_tendsto_min` via reduction: `powerMean x r = 1/powerMean (1/x) (-r)` for r < 0, then apply max case
2. Alternative: direct squeeze with reversed rpow monotonicity for negative exponents
