# Knowledge: stirling-formula-oq-01-wip-01 — Complete Higher-Order Stirling Expansion

**Problem**: Prove `stirling_first_correction` in `StirlingExpansion.lean`:
```lean
∃ C > 0, ∀ n : ℕ, 2 ≤ n →
  |stirlingSeq n / Real.sqrt π - (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2
```

The 1/(12n) correction coefficient is the key refinement of Stirling's approximation.

---

## Session 2026-05-07 (Session 2) — Step Formula Proved + Telescoping Infrastructure

**Mode**: REVISIT
**Outcome**: Major progress — `stirling_step_formula` proved, full telescoping framework built

### What I Did

**Proved `stirling_step_formula`** (the only blocker from Session 1): expand `log(stirlingSeq n)` via `Real.log_div/mul/sqrt/pow/exp`, the difference telescopes to `(k+1/2)·(log(k+1)-log k)-1`. Key Lean 4 fix: `↑(k+1) ≠ (k:ℝ)+1` definitionally — add `have h_cast := by push_cast; ring` before log_div rewrites.

**5 arithmetic telescoping lemmas** (k ≥ 2): inv_sq_le_telescope, inv_cube_le_telescope, inv_harmonic_le_sq, inv_cube_le_telescope2, inv_quad_le_telescope. All close by nlinarith.

**Partial sum bounds by induction**: log_stirlingSeq_partial_upper and log_stirlingSeq_partial_lower using the telescoping lemmas + stirling_step_upper/lower.

**stirling_first_correction structure** (C=2): upper via le_of_tendsto', lower via le_of_tendsto_of_tendsto. Two remaining mechanical sorrys: (1) G(n+M)→0 and (2) |exp(L)-(1+L)| ≤ L²/2·exp(L) ≤ 1/n².

### Build Result

**CONFIRMED WORKING**: `⚠ [3083/3083] Replayed Proofs.StirlingExpansion` — compiles with NO errors, only minor style warnings + 2 intentional sorry warnings. PR #16442 ready for next session to fill the 2 remaining sorrys.

### Key Lean 4 API Learnings (Session 2)

**`div_le_div_iff`, `div_le_div_right` UNKNOWN in Lean 4.26** — Use `div_le_div_of_nonneg_right (h : a≤b) (hc : 0≤c) : a/c ≤ b/c` (confirmed in `Erdos487Problem.lean`). For showing `0 ≤ a/b - c/d`, use `div_nonneg` after `field_simp; ring`.

**Association mismatch in inductive proofs**: `↑((n+L)+1)` = `(n:ℝ)+↑L+1` [LEFT-assoc via left-assoc `+`] but bound's `(n:ℝ)+(↑L+1)` is RIGHT-assoc. These are DIFFERENT atoms for `linarith`. Fix: `simp only [← add_assoc] at ⊢` normalizes goal to left-assoc, then `rw [hnL1_sub]` (where `hnL1_sub : (n:ℝ)+↑L+1-1 = (n:ℝ)+↑L`).

**Build output filtering**: default `grep | head -30` is filled by `[Xs] Building...` timer lines. Use `grep -v "Downloaded|Building|info:..."` to filter noise, or use the error-only filter `grep -E "error:|sorry|..."` (no "Build" in pattern).

### Key Mathematical Result

`|L - 1/(12n)| ≤ 1/n²` via simultaneous telescoping: `Σ d_k ≤ F(n) = 1/(12(n-1))+1/(12(n-1)²) ≤ 1/(12n)+1/n²` and `G(n) ≤ Σ d_k` where `G(n) = 1/(12n)-1/(24(n-1)²)-1/(24(n-1)³) ≥ 1/(12n)-1/(2n²)`.

### Files Modified

- `proofs/Proofs/StirlingExpansion.lean` (PR #16442)

### Next Steps

1. Fill sorry 1: `tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop` for G(n+M)→0
2. Fill sorry 2: L ≤ 1/n → |exp(L)-(1+L)| ≤ L²·exp(1/2)/2 ≤ 1/n²

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
