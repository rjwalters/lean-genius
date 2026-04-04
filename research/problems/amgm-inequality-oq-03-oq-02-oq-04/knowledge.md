# Knowledge Base: amgm-inequality-oq-03-oq-02-oq-04

**Problem**: Formalize the extreme power mean limits:
- lim_{r→+∞} M_r(x) = max(x₁,...,xₙ)
- lim_{r→-∞} M_r(x) = min(x₁,...,xₙ)

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
