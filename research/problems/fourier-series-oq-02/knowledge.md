# Knowledge Base: fourier-series-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Prove that Fourier coefficients of α-Hölder continuous functions on AddCircle T decay at rate O(1/|n|^α). The proof uses the half-period translation trick: shifting x → x + T/(2n) negates the n-th Fourier monomial, giving a difference formula that bounds the coefficient.

---

## Insights

### Proof Architecture (12 → 8 axioms)
- **fourier_norm_one**: `‖fourier n x‖ = 1` — trivial from `simp [fourier_apply]`, toCircle maps to unit circle
- **fourier_translate_halfperiod**: `fourier(-n)(x + T/(2n)) = -fourier(-n)(x)` — key identity via `fourier_neg + fourier_add_half_inv_index + map_neg`
- **holder_translation_bound**: `‖f(x) - f(x + T/(2n))‖ ≤ C·(T/(2|n|))^α` — via `HolderWith.dist_le_of_le` + `quotient_norm_mk_le'`
- **integral_product_bound**: `‖∫ (f(x)-f(x+s))·e_{-n}(x) dx‖ ≤ C·(T/(2|n|))^α` — via `norm_integral_le_integral_norm` + `integral_mono_of_nonneg` + `IsProbabilityMeasure`

### Key Mathlib Lemmas Used
- `quotient_norm_mk_le' : ‖(s : M ⧸ S)‖ ≤ ‖s‖` — quotient norm ≤ original norm, gives `dist(x, x+↑s) ≤ |s|` on AddCircle
- `HolderWith.dist_le_of_le : dist x y ≤ d → dist (f x) (f y) ≤ C * d ^ α` — core Hölder bound
- `norm_integral_le_integral_norm : ‖∫ f ∂μ‖ ≤ ∫ ‖f‖ ∂μ` — triangle inequality for integrals
- `integral_mono_of_nonneg : 0 ≤ f → Integrable g → f ≤ g a.e. → ∫ f ≤ ∫ g` — monotonicity
- `IsProbabilityMeasure.measure_univ` — haarAddCircle total mass = 1
- `integral_add_right_eq_self` — Haar measure translation invariance (works without integrability)

### Distance on AddCircle
- `dist(x, x + ↑s) = ‖(x + ↑s) - x‖ = ‖↑s‖` (via `dist_comm + dist_eq_norm + add_sub_cancel_right`)
- `‖↑s : AddCircle T‖ ≤ |s|` (via `quotient_norm_mk_le'`)
- For exact computation: `AddCircle.norm_coe_eq_abs_iff` gives `‖↑s‖ = |s|` when `|s| ≤ |T|/2`
- `|T/(2n)| = T/(2|n|)` via `abs_div + abs_of_pos`

---

## Dead Ends

### fourierCoeff_difference_formula via integral_sub
- **Problem**: `integral_sub` requires `Integrable` for both terms, but the axiom has no integrability hypothesis
- **Impact**: Cannot decompose `∫ (a - b) = ∫ a - ∫ b` without proving integrability
- **Partial workaround**: `integral_add_right_eq_self` works without integrability, so translation invariance is available
- **Possible fix**: Case-split on integrability of `fun x => fourier (-n) x • f x`. If integrable, use integral_sub. If not, both sides are 0.

---

## Current State (2026-03-24, updated)

**File**: 430 lines, 4 axioms, 15 theorems, 1 sorry

### Remaining Axioms (4 — all deep)
1. `holder_decay_is_optimal` — optimality via Weierstrass function
2. `decay_implies_regularity` — Sobolev embedding on circle
3. `fourierCoeff_smooth_decay` — C^k decay via integration by parts
4. `fourierCoeff_analytic_decay` — analytic exponential decay

### Remaining Sorries (1)
1. `fourierCoeff_sq_summable_of_holder` (line ~275) — square-summability for α > 1/2

### Proved This Session
1. `riemannLebesgue_of_holder` — **FULLY PROVED** (both internal sorries filled)
   - `h_rpow`: `Real.zero_rpow + Tendsto.rpow_const (Or.inr hα_pos.le)` — rpow composition at 0
   - `h_frac_le`: `div_le_div_of_nonneg_left + Nat.cast_natAbs + Int.cast_abs` — fraction comparison

---

## Session: researcher-4 (2026-03-24) — Proof Strategy Analysis

### riemannLebesgue_of_holder — Detailed Proof Strategy

**Goal after existing setup:**
```
⊢ Set.Finite {n : ℤ | ¬‖fourierCoeff f n‖ < ε}
```

**Proof approach:**
1. Case split on `C = 0` vs `C > 0`:
   - **C = 0**: Bound is 0 for all n ≠ 0, so bad set ⊆ {0} which is finite.
   - **C > 0**: The bound `(C/2)(T/(2(k+1)))^α` tends to 0 as k → ∞.
2. For C > 0, show the bound sequence tends to 0:
   - `T / (2*(k+1)) → 0` via `tendsto_const_nhds.div_atTop` (denom → ∞)
   - `x^α → 0` as `x → 0` via `Filter.Tendsto.rpow_const` with `Or.inr hα_pos.ne'`
   - Multiply by constant C/2
3. Extract N₀ from the convergence via `Filter.eventually_atTop`
4. Show bad set ⊆ `Set.Icc (-(N₀+1)) (N₀+1)` which is finite
5. For n with `n.natAbs > N₀+1` and n ≠ 0: use rpow monotonicity + decay bound < ε

**Key Lean API needed:**
- `tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop` — for k+1 → ∞
- `Filter.Tendsto.atTop_mul_const` — for 2*(k+1) → ∞
- `tendsto_const_nhds.div_atTop` — for T/(2*(k+1)) → 0
- `Filter.Tendsto.rpow_const` — for x^α composition with filter
- `Real.zero_rpow hα_pos.ne'` — for 0^α = 0 when α > 0
- `Real.rpow_le_rpow` — for rpow monotonicity (smaller base → smaller rpow)
- `div_le_div_left` — for T/c ≤ T/b when b ≤ c (larger denom → smaller fraction)
- `Set.finite_Icc` — bounded integer intervals are finite

**Main difficulty**: The rpow monotonicity step requires careful handling of:
- `0 ≤ T/(2|n|)` (nonneg base for rpow_le_rpow)
- `T/(2|n|) ≤ T/(2(N₀+1))` (base comparison)
- `0 ≤ α` (nonneg exponent)
- Converting between `n.natAbs` (ℕ) and `|↑n|` (ℝ) via `Int.abs_cast_natAbs`

**Blocker**: Many small positivity/cast obligations. Recommend using `positivity` where possible and `push_cast` + `omega` for ℤ ↔ ℕ conversions.

### fourierCoeff_sq_summable_of_holder — Detailed Proof Strategy

**Goal:** `Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)`

**Proof approach:**
1. For n ≠ 0: `‖ĉ_n‖² ≤ ((C/2)(T/(2|n|))^α)² = K * |n|^{-2α}` where K = (C²/4)(T/2)^{2α}
2. Σ K/|n|^{2α} converges since 2α > 1 (hypothesis)
3. Use `Summable.of_nonneg_of_le` for comparison
4. Handle ℤ → ℕ conversion for the sum

**Key API:**
- `Real.summable_nat_rpow_inv.mpr` — p-series convergence for p > 1
- `Summable.of_nonneg_of_le` — comparison test (available in codebase, widely used)
- Squaring the rpow bound: `(x^α)² = x^{2α}` via `rpow_natCast` or manual
- ℤ summability: split into positive and negative parts

**Difficulty**: Converting between ℤ-indexed sums and ℕ-indexed sums, and the rpow algebra for squaring the bound.

### General Observations
- The 4 remaining axioms are genuinely deep (require Weierstrass functions, Sobolev embedding, integration by parts, complex analysis)
- No axioms are "routine" enough to eliminate from Mathlib alone

---

## Session: researcher-4 (2026-03-24) — riemannLebesgue Proof + sq_summable Investigation

### riemannLebesgue_of_holder — COMPLETED

Both internal sorries filled:
1. **h_rpow** (rpow of converging sequence → 0): `Real.zero_rpow hα_pos.ne'` rewrites target, then `h_base.rpow_const (Or.inr hα_pos.le)` composes.
   - Key: `Tendsto.rpow_const` has hypothesis `0 ≤ a ∨ 0 ≤ p` (NOT `p ≠ 0`)
2. **h_frac_le** (fraction comparison): `div_le_div_of_nonneg_left hT.out.le (by positivity) h_denom_le`
   - Key: `hT.out.le` needed (not `hT.out`) — `div_le_div_of_nonneg_left` takes `0 ≤ T`
   - Cast chain: `Nat.cast_natAbs` + `Int.cast_abs` converts `↑(n.natAbs : ℕ)` to `|(↑n : ℝ)|`

### fourierCoeff_sq_summable_of_holder — Strategy (BLOCKED on API)

**Best approach: Parseval's theorem** (not explicit p-series comparison!)

The Parseval approach is much cleaner than explicit comparison:
1. `Continuous f` (from Hölder) → `f ∈ L²(haarAddCircle)` (compact space + finite measure)
2. `hasSum_sq_fourierCoeff F` where `F : Lp ℂ 2 haarAddCircle`
3. Transfer via a.e. equality: `fourierCoeff (⇑F) n = fourierCoeff f n`

**Blocker**: `Memℒp` identifier not found in this Mathlib version (v4.26.0, mathlib4 rev 2df2f015).
- `Continuous.memℒp` also missing
- Likely renamed: try `MemLp`, `MeasureTheory.MemLp`, or find via `#check @MeasureTheory.Lp.mk`
- Alternative: `ContinuousMap.toLp` or construct Lp element via `AEEqFun`

**Next step**: Search for the correct Lp constructor API:
```lean
-- Try these to find the right name:
#check @MeasureTheory.Lp.mk
#check @MeasureTheory.MemLp
#check @ContinuousMap.toLp
-- Or construct directly:
-- snorm f 2 haarAddCircle < ⊤ from continuous on compact + finite measure
```

**Why Parseval over comparison**: The comparison approach requires ℤ-sum splitting, rpow algebra for squaring, and 50+ lines. Parseval reduces to 10 lines once you have the Lp API.
