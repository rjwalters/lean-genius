# Knowledge: erdos-1151-oq-04

## Problem Summary

**Goal**: Prove `erdos_1941_divergence` (axiom in `Erdos1151Problem.lean`) by formalizing
that the Chebyshev Lebesgue function Λₙ(cos(πp/q)) → ∞ for odd p, q, and then
constructing a continuous function whose Chebyshev interpolation diverges.

**Axiom to eliminate**:
```lean
axiom erdos_1941_divergence (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    let x := Real.cos (p * Real.pi / q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterpSeq f x n
```

This says: for x = cos(πp/q), there EXISTS a continuous f such that Lₙf(x) → +∞ (full
sequence diverges to +∞, not just a subsequence).

## Architecture (Erdos1151OQ04.lean)

**Main reduction theorem** (COMPLETE, no sorry):
```
chebyshev_lebesgue_growth [sorry] + divergence_from_lebesgue_growth [sorry]
  → erdos_1941_divergence_from_growth [PROVED]
```

**Proved lemmas (no sorry)**:
- `lebesgue_upper_bound`: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x)
- `chebyshevInterp_add`, `chebyshevInterp_smul`: linearity
- `chebyshev_T_at_cos`: T_n(cos θ) = cos(nθ) [from Mathlib T_real_cos]
- `cos_int_pi`: cos(kπ) = (-1)^k [from Mathlib cos_int_mul_pi]
- `cos_rational_pi_at_multiples`: cos(mq·πp/q) = cos(mπp)
- `cos_rational_pi_nonzero_along_multiples`: along n = mq, cos(nπp/q) ≠ 0
- `chebyshevNode_mem_Icc`: nodes lie in [-1, 1]
- `abs_cos_int_pi_mul`: |cos(kπ)| = 1
- **chebyshevNode_is_root** (PROVED this session): T_n(cos φₖ) = 0
- **chebyshevNode_injective** (PROVED this session): Chebyshev nodes are distinct

**Aristotle companion (Erdos1151OQ04Aristotle.lean)** — all sorries CLOSED this session:
- `cos_odd_half_pi`: cos((2k+1)π/2) = 0
- `chebyshevNode_is_root`: T_n at Chebyshev nodes = 0
- `chebyshevNode_injective`: nodes are distinct
- `n_mul_chebyshevAngle`, `chebyshevAngle_pos`, `chebyshevAngle_lt_pi`, etc. [arithmetic helpers]

## Sorries Remaining (3 in main file, as of 2026-04-25)

### 0. `trig_sum_lb_of_cos_eq_neg_one` (line ~850) — HARD, strategy known
**Goal**: (1/(2π))·n·log(n+1) ≤ Σₖ sin(φₖ)/|(-1) - cos φₖ|

This handles the x = -1 sub-case (e.g., p = q = 1 giving cos(π) = -1).

**Proof strategy**:
- `sum_term_eq_tan_half_angle`: each term = tan(φₖ/2) = sin(φₖ/2)/cos(φₖ/2)
- For k = n-1-j (j = 0,...,⌊n/4⌋-1): φₖ = π - (2j+1)π/(2n), so φₖ/2 = π/2 - (2j+1)π/(4n)
- tan(φₖ/2) = cot((2j+1)π/(4n)) ≥ 1/(2·(2j+1)π/(4n)) = 2n/(π(2j+1)) by `cot_ge_inv_two_mul`
- Sub-sum: Σⱼ₌₀^{⌊n/4⌋-1} 2n/(π(2j+1)) ≥ (n/π)·log(⌊n/4⌋+1) ≥ C·n·log(n+1)

### 1. `chebyshev_trig_sum_lb` (line ~879) — HARD, strategy known
**Goal**: ∃ C₂ > 0, ∀ n ≥ 1, C₂·n·log(n+1) ≤ Σₖ sin(φₖ)/|x - cos φₖ|

**CORRECTION**: Previous analysis incorrectly claimed x = cos(πp/q) ≠ ±1 for odd p,q.
In fact, p = q = 1 gives x = cos(π) = -1. The proof requires two cases:

**Case 1: x = -1** (p/q is an odd integer, e.g., p = q = 1):
- Use `trig_sum_lb_of_cos_eq_neg_one` directly

**Case 2: x ∈ (-1, 1)** (p/q ∉ ℤ, equivalently sin(πp/q) ≠ 0):
- Let s = |sin(πp/q)| > 0
- Nearest node k₀: choose k₀ with |θ - φₖ₀| ≤ π/(2n) where θ = πp/q
- Lipschitz: |cos θ - cos φₖ| ≤ |θ - φₖ| ≤ j·π/n for k = k₀ + j
- sin(φₖ) ≥ s/2 for nodes within distance π/(s·n) from k₀
- Harmonic sum: S_n ≥ (s·n/(2π))·Hₘ ≥ (s·n/(2π))·log(⌊n·s/(2π)⌋+1) ≥ C₂·n·log(n+1)
- Take C₂ = s²/(4π²)

**Mathlib tools available**:
- `Real.log_add_one_le_harmonic` for harmonic bound
- `Real.sin_pos_of_pos_of_lt_pi` for sin(φₖ) > 0

### 2. `divergence_from_lebesgue_growth` (line 838) — OPEN, fundamental gap
**Goal**: Λₙ(x) → +∞ ⟹ ∃ continuous f, Lₙf(x) → +∞ (full sequence)

**Fundamental gap**: Banach-Steinhaus / UBP gives `∃ f continuous, lim sup_n |Lₙf(x)| = ∞`,
NOT `lim_n Lₙf(x) = +∞` (signed, full sequence).

**Lacunary construction issues**: f = Σₖ (1/k²) fₙₖ where fₙₖ chosen so Lₙₖ(fₙₖ)(x) = Λₙₖ(x).
Cross terms: Lₙₖ(fₙⱼ)(x) for j ≠ k could dominate. Need |Lₙₖ(fₙⱼ)(x)| << Λₙₖ(x)/k² for all j < k,
which requires precise control on how Chebyshev interpolation at degree nₖ sees basis functions
for nⱼ << nₖ. This is ~300+ lines of analysis.

**Recommended action**: Weaken the sorry statement to lim sup version:
```lean
-- Weaker (provable by Baire/UBP):
theorem divergence_from_lebesgue_growth' (x : ℝ) (...) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      Filter.Tendsto (fun n => ‖chebyshevInterp n f x‖) Filter.atTop Filter.atTop
-- This follows from Banach-Steinhaus directly
```
The current statement with `M < Lₙf(x)` (signed divergence) may require full lacunary argument.

## Session 2026-04-22 — Results (archived)

**Outcome**: progress  
**Sorries closed**: 5 (chebyshevNode_is_root ×2, chebyshevNode_injective ×2, cos_odd_half_pi)
**Companion file**: now 0 sorries  
**Main file**: 4 sorries → 2 sorries (sessions 5-11 progress restored in PR #12153)

## Session 2026-04-24 (this session) — Analysis

**Outcome**: documented (no proof changes)  
**Mode**: Deep analysis of 2 remaining sorries

### What I Did
- Read Erdos1151OQ04.lean lines 740–850 to understand current proof structure
- Confirmed chebyshev_lebesgue_growth is PROVED (wraps chebyshev_lebesgue_lb which uses sorry #1)
- Analyzed sorry #1 (chebyshev_trig_sum_lb): proof strategy is clear, ~200 lines, no fundamental blocks
- Analyzed sorry #2 (divergence_from_lebesgue_growth): identified fundamental gap in axiom statement
  - UBP gives lim sup = ∞, not lim = +∞ (signed)
  - Lacunary construction requires cross-term de-correlation (~300+ lines)
  - Recommended weakening the sorry to lim sup version

### Key Findings
- Proof of sorry #1 is TRACTABLE but requires careful case analysis and harmonic sum estimates
- Sorry #2 has a genuine mathematical gap: the current statement may be stronger than what UBP gives
- **CORRECTION**: p, q both odd does NOT imply cos(πp/q) ∉ {±1}. Example: p = q = 1 gives cos(π) = -1.
  The proof needs two cases: x = -1 (use cot/tan bound) and x ∈ (-1,1) (use Lipschitz + sin bound)
- The main theorem `erdos_1941_divergence_from_growth` is proved — only intermediate lemmas remain

### Next Steps
1. Prove `trig_sum_lb_of_cos_eq_neg_one`: harmonic sum via cot ≥ 1/(2t) bound
2. Prove `chebyshev_trig_sum_lb` using the two-case strategy documented in the file
3. For sorry #2 (`divergence_from_lebesgue_growth`): weaken to lim sup = ∞ first (provable by UBP)

## Session 2026-04-25 — Helper Lemmas Added

**Outcome**: progress — 5 new proved lemmas, corrected x=-1 analysis  
**Sorries changed**: 2 → 3 (added `trig_sum_lb_of_cos_eq_neg_one` as an intermediate sorry; structural progress)

### What I Did
- Corrected mathematical error: x = cos(πp/q) = -1 IS possible (p = q = 1). Two-case proof needed.
- Added auxiliary lemmas section to `Erdos1151OQ04.lean` (worktree: `feature/researcher-10`):
  - `cos_ge_half_of_le_pi_div_three`: cos(t) ≥ 1/2 for t ∈ [0, π/3] — from antitoneOn_cos
  - `cot_ge_inv_two_mul`: cot(t) ≥ 1/(2t) for t ∈ (0, π/3] — from sin(t) ≤ t and cos(t) ≥ 1/2
  - `sin_div_one_add_cos`: sin(φ)/(1+cos φ) = tan(φ/2) for φ ∈ (0, π) — half-angle formula
  - `chebyshevAngle_pos_lt_pi`: φₖ = (2k+1)π/(2n) ∈ (0, π) — simple arithmetic
  - `sum_term_eq_tan_half_angle`: sin(φₖ)/|(-1)-cos(φₖ)| = tan(φₖ/2) — key reduction for x=-1
  - `trig_sum_lb_of_cos_eq_neg_one` [sorry]: lower bound for x=-1 case
- Fixed sign error from previous session: |(-1)-cos φ| = 1+cos φ (not 1-cos φ); result is tan (not cot)

### Key Findings
- `cot_ge_inv_two_mul`: 1/(2t) ≤ cos(t)/sin(t) for t ≤ π/3. Proved via sin(t)≤t and cos(t)≥1/2.
- `sum_term_eq_tan_half_angle` proof: abs_of_neg + half-angle formula. The `set` tactic was avoided
  to allow `ring` to close the argument equality `φ/2 = (2k+1)π/(4n)` after `rw [harg]`.
- Note: `congr 1 <;> ring` does NOT work on sin/cos goals; need explicit `have harg` + `rw [harg]`.

## Session 2026-04-25 — Case Split Structure (Session 14)

**Outcome**: progress — 1 new proved lemma, case split structure for chebyshev_trig_sum_lb  
**Sorries**: still 3 (unchanged count, but x=-1 case now PROVED modulo trig_sum_lb_of_cos_eq_neg_one)

### What I Did
- Proved `cos_pi_mul_odd_ne_one`: cos(πp/q) ≠ 1 when p is odd and q > 0
  - Uses `Real.cos_eq_one_iff`: cos(θ) = 1 ↔ ∃ n : ℤ, n * (2π) = θ
  - If πp/q = 2nπ then p = 2nq (clear π and q), making p even → contradiction via `omega`
  - Key: `field_simp [pi_ne, q_ne] at hn; linarith` gives `(p : ℝ) = 2 * n * q`
  - Then `exact_mod_cast` lifts to ℤ, `omega` closes the parity contradiction
- Restructured `chebyshev_trig_sum_lb` with explicit case split:
  - Case x = -1: PROVED (C₂ = 1/(2π)); connects to `trig_sum_lb_of_cos_eq_neg_one` via `Finset.sum_congr` + `simp only [hx, chebyshevNode]`
  - Case x ∈ (-1,1): sorry with C₂ = sin²(πp/q)/(8π²); proved sin²(πp/q) > 0 from x ≠ ±1

### Key Findings
- Case x=-1 in `chebyshev_trig_sum_lb` is NOW PROVED structurally (modulo `trig_sum_lb_of_cos_eq_neg_one`)
- `cos_pi_mul_odd_ne_one` uses `Real.cos_eq_one_iff` (confirmed in Mathlib4 `Trigonometric/Basic.lean:528`)
- `exact_mod_cast` from `(p : ℝ) = 2 * (n : ℤ) * (q : ℕ)` to ℤ should work via norm_cast chain
- `omega` handles `2 * n * q = 2 * m + 1 → False` over ℤ via parity argument

### Next Steps
1. Prove `trig_sum_lb_of_cos_eq_neg_one` Step 2: sub-sum over last n/2 nodes (k ↦ n-1-k bijection)
2. Prove `chebyshev_trig_sum_lb` case x∈(-1,1): Lipschitz + nearest-node + harmonic sum
3. For `divergence_from_lebesgue_growth`: weaken to lim sup = ∞ (Baire/UBP)

## Session 2026-04-25 — Full Proof Attempt for trig_sum_lb_of_cos_eq_neg_one (Session 15)

**Outcome**: progress — ~170-line proof attempt replaces sorry (pending Docker build verification)
**Sorries**: 3 → 2 (if proof compiles)

### What I Did
- Wrote full proof of `trig_sum_lb_of_cos_eq_neg_one`:
  - **hS_cot** (∑tan = ∑cot): involution k↦n-1-k via `Equiv.sum_comp`, complementary angle
    θ(n-1-k) = π/2 - θ(k) proved via `rw [Nat.cast_sub hkle, Nat.cast_sub hn]` + `field_simp; ring`
    Then `Real.cos_pi_div_two_sub` + `Real.sin_pi_div_two_sub` swap sin↔cos
  - **h2S** (2*∑tan = ∑2/sin): `linarith [hS_cot]` gives 2*S = S + ∑cot; `← Finset.sum_add_distrib`
    combines; `field_simp; ring` proves tan+cot = 2/sin via double-angle `hsin2_eq`
  - **hS_inv_sin** (∑tan = ∑1/sin): `h2S_rw` (2*∑1/sin = ∑2/sin via `Finset.mul_sum`) + `linarith`
  - **hodd_harm_lb** ((1/2)*harmonic_n ≤ ∑1/(2k+1)): prove in ℚ first (avoid ℚ→ℝ cast issues),
    then lift to ℝ via `exact_mod_cast`. Each term: (1/2)/(k+1) ≤ 1/(2k+1) by `div_le_div_iff`
  - **hS_log_lb**: chains log(n+1) ≤ harmonic_n (`log_add_one_le_harmonic`) → ≤ 2*∑1/(2k+1) → ≤ ∑1/sin

### Key Lean Techniques Discovered
- **Bug fix**: `rw [two_mul, ← hS_cot, ← Finset.sum_add_distrib]` is wrong (← hS_cot finds no ∑cot match).
  Correct: `linarith [hS_cot]` for equality derivation from ∑tan = ∑cot, then `← Finset.sum_add_distrib`
- **ℚ→ℝ harmonic cast**: Prove equality in ℚ first (`simp only [harmonic]; rw [← Finset.sum_fin_eq_sum_range]; congr 1; ext k; push_cast; ring`), then `exact_mod_cast` lifts to ℝ
- **hS_inv_sin equality**: From `2*∑tan = ∑2/sin` and `2*∑1/sin = ∑2/sin`, derive `∑tan = ∑1/sin` via `linarith` (equality from two linear equalities is linear arithmetic)
- `Nat.cast_sub hn` with `hn : 0 < n` works as `1 ≤ n` in ℕ (definitionally equal)
- `div_le_div_iff` cross-multiplies `a/c ≤ b/d` to `a*d ≤ b*c`

Replaced the `sorry` for `h_harm_chain` with a complete 5-step proof:

**A. Angle bound**: `(2j+1)π/(4n) ≤ π/3` for j < m = √n.
   - Key: `3*(2j+1) ≤ 4n`. Follows from j+1 ≤ m, m^2 ≤ n (`Nat.sqrt_le' n`), and 4m^2-6m+3 > 0 always.
   - Proof: `have haux : 6*m ≤ 4*m^2 + 3 := by nlinarith [hm_pos, sq_nonneg m]; nlinarith [hm_sq]`

**B. Cot lower bound**: `cos(t_j)/sin(t_j) ≥ 2n/(π(2j+1))` from `cot_ge_inv_two_mul`.
   - Identity: `2n/(π(2j+1)) = 1/(2 * (2j+1)π/(4n))`. After `rw [h_eq]; exact hcot`. ✓

**C. Inv inequality**: `2n/(π(2j+1)) ≥ n/(π(j+1))` since 2j+1 ≤ 2j+2. `nlinarith`. ✓

**D/E. Sum and factoring**: `Σ cot ≥ Σ n/(π(j+1)) = (n/π) * Σ (j+1)⁻¹`. ✓

**F. Harmonic cast**: `(harmonic m : ℝ) = ∑ j : Fin m, (j+1 : ℝ)⁻¹`:
   - `simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]`
   - `Finset.Icc 1 m = (range m).image (·+1)` (by `omega`)
   - `← Fin.sum_univ_eq_sum_range` + `push_cast; ring`

**G. Log bound**: `log(m+1) ≥ (1/2)log(n+1)` from n+1 ≤ (m+1)^2 (`hsucc_sq`) + `Real.log_pow`.

### Key Mathlib Lemma Names Confirmed

- `Nat.sqrt_le' n : Nat.sqrt n ^ 2 ≤ n` ✓
- `Nat.lt_succ_sqrt n : n < (Nat.sqrt n + 1) ^ 2` ✓
- `log_add_one_le_harmonic n : Real.log ↑(n+1) ≤ harmonic n` (no namespace prefix needed) ✓
- `harmonic_eq_sum_Icc : harmonic n = ∑ i ∈ Finset.Icc 1 n, (↑i)⁻¹` ✓
- `Fin.sum_univ_eq_sum_range f n : ∑ i : Fin n, f i = ∑ i ∈ Finset.range n, f i` ✓

### Remaining Sorries (3→2 focused)

1. `chebyshev_trig_sum_lb` Case 2: monolithic sorry → 2 focused sub-sorries (Session 25):
   a. `hS_floor`: S_n ≥ 2/π via nearest-node + Jordan's inequality
   b. `hS_harm`: S_n ≥ (s/4π)*n*log(n+1) for n ≥ N₀ (harmonic sub-sum, mirrors Case 1)
2. `divergence_from_lebesgue_growth` — lacunary construction / UBP gap

### Next Steps
1. Prove `hS_floor`: ~50 lines, k*=Nat.floor(n*θ/π-1/2) + pigeonhole + Jordan's
2. Prove `hS_harm`: ~150 lines, adapt Case 1 (trig_sum_lb_of_cos_eq_neg_one) with θ-centered nodes
3. For sorry #2: weaken to lim sup = ∞ (provable by Banach-Steinhaus)

## Session 2026-04-26 (Session 25) — Case 2 structure for chebyshev_trig_sum_lb

**Mode**: REVISIT (RICH knowledge tier)
**Outcome**: PROGRESS — monolithic Case 2 sorry → structured proof with 2 focused sub-sorries

### What I Did
- Proved x > -1 (neg_one_le_cos + hx_neg ≠ -1)
- Proved x < 1: cos(πp/q) = 1 → p = 2kq even, contradicts odd p (Real.cos_eq_one_iff)
- Set up θ = arccos(x) ∈ (0,π): Real.arccos_pos.mpr hx_lt_1, Real.arccos_eq_pi for upper bound
- s = sin(θ) > 0 via Real.sin_pos_of_pos_of_lt_pi
- Found N₀ via exists_nat_gt(π²/s²), proved N₀ > 0
- Constructed C₂ = min(s/(4π), (2/π)/(N₀*log(N₀+1))), proved C₂ > 0 completely
- Case split: n ≥ N₀ uses hS_harm; n < N₀ uses hS_floor with monotonicity bound

### Key Insights
- Jordan's inequality (Real.mul_le_sin): 2/π * x ≤ sin x for x ∈ [0,π/2]
  → sin(π/(2n)) ≥ 1/n → nearest node term ≥ (1/n)/(π/(2n)) = 2/π
- Two-part C₂ argument handles ALL n ≥ 1 uniformly without computing N₀ explicitly
- div_mul_cancel₀ cleanly resolves N₀*log(N₀+1) cancellation

### Files Modified
- `proofs/Proofs/Erdos1151OQ04.lean`: lines 1067-1200 (86 new lines replacing 1 sorry)
