# Knowledge: stirling-formula-oq-01-wip-01 — Complete Higher-Order Stirling Expansion

**Problem**: Prove `stirling_first_correction` in `StirlingExpansion.lean`:
```lean
∃ C > 0, ∀ n : ℕ, 2 ≤ n →
  |stirlingSeq n / Real.sqrt π - (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2
```

The 1/(12n) correction coefficient is the key refinement of Stirling's approximation.

---

## Session 2026-05-06 (Session 1) — Log Bounds + Step Bounds

**Mode**: FRESH
**Outcome**: Progress — proved 4 lemmas, 1 sorry remaining (step formula ratio)

### What I Did

**Proved two log inequality lemmas** (via derivative monotonicity):
- `log_one_plus_le_cubic (x : ℝ) (hx : 0 < x) : Real.log (1 + x) ≤ x - x²/2 + x³/3`
  - Key: f(t) = t - t²/2 + t³/3 - log(1+t), f'(t) = t³/(1+t) ≥ 0, f(0)=0 → f(x)≥0
- `log_one_plus_ge_quartic (x : ℝ) (hx : 0 < x) : x - x²/2 + x³/3 - x⁴/4 ≤ Real.log (1 + x)`
  - Key: f(t) = log(1+t) - (t - t²/2 + t³/3 - t⁴/4), f'(t) = t⁴/(1+t) ≥ 0, f(0)=0 → f(x)≥0

**Proved step bounds** (conditional on step formula):
- `stirling_step_upper`: d_k ≤ 1/(12k²) + 1/(6k³) from log upper bound
- `stirling_step_lower`: 1/(12k²) - 1/(12k³) - 1/(8k⁴) ≤ d_k from log lower bound

**Left as sorry**:
- `stirling_step_formula`: d_k = (k+1/2)*log(1+1/k) - 1
  This is a pure algebraic computation from `stirlingSeq` definition.

### Key Findings

- **Proof strategy is complete**: step_formula → step_upper/lower → Σd_k bounds → first_correction
- **API used**: `monotoneOn_of_deriv_nonneg`, `ContinuousOn.log`, `hasDerivAt_pow`
- **Correct lower bound**: 1/(12k²) - 1/(12k³) - 1/(8k⁴) (not 1/(12k²) - 1/(8k³))
- The exact sum bound needed: 1/(12n) ≤ Σ_{k≥n} 1/(12k²) ≤ 1/(12(n-1))
  Combined with Σ (1/k³ + 1/k⁴) ≤ C/n² gives |Σ d_k - 1/(12n)| ≤ C/n² ✓

### Files Modified

- `proofs/Proofs/StirlingExpansion.lean` (new version on branch `research/stirling-formula-oq-01-wip-01`)

### Next Steps

1. **Prove `stirling_step_formula`**: Unfold stirlingSeq, use log arithmetic:
   ```
   log(stirlingSeq k / stirlingSeq(k+1))
   = log(k!/((k+1)!) * sqrt((k+1)/k) * ((k+1)/k)^k / e)
   = (k+1/2)*log((k+1)/k) - 1
   ```
   Key: `Real.log_div`, `Real.log_mul`, `Real.log_sqrt`, `Real.log_pow`, `Nat.factorial_succ`
   Note: `field_simp` + `ring` won't handle sqrt — need explicit rewrites.

2. **Prove the sum bound**: `|Σ_{k≥n} d_k - 1/(12n)| ≤ C/n²`
   Uses: integral comparison for Σ 1/k², Σ 1/k³, Σ 1/k⁴

3. **Convert log bound to ratio**: `|exp(log r) - (1 + 1/(12n))| ≤ C/n²`
   Uses: `Real.add_one_le_exp`, quadratic bound on exp
