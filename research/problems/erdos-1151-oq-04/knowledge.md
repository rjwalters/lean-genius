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

## Session 2026-04-26 — Proof Structure for trig_sum_lb_of_cos_eq_neg_one

**Outcome**: progress — `trig_sum_lb_of_cos_eq_neg_one` partially structured (4 components proved inline)
**Sorry count**: 3 (unchanged), but sorry #0 now has most structure in place

### What I Did

Replaced the single `sorry` in `trig_sum_lb_of_cos_eq_neg_one` with a structured proof that has
only one sorry remaining (`h_harm_chain`). Proved inline:

1. **`hf_nn`** (nonnegativity): All tan terms ≥ 0 since angles in (0, π/2). Uses
   `Real.sin_nonneg_of_nonneg_of_le_pi` and `Real.cos_pos_of_mem_Ioo`. ✓

2. **`h_comp`** (complementary angle identity): For j : Fin m (m = Nat.sqrt n), the index
   n-1-j gives angle (2*(n-1-j)+1)π/(4n) = π/2 - (2j+1)π/(4n). Uses `Nat.cast_sub` for
   the nat subtraction cast, then `Real.sin_pi_div_two_sub` and `Real.cos_pi_div_two_sub`. ✓

3. **`h_sub_le`** (sub-sum ≤ full sum): Injection j ↦ ⟨n-1-j, ...⟩ maps Fin m → Fin n
   injectively. Uses `Finset.sum_image` + `Finset.sum_le_sum_of_subset_of_nonneg`. ✓

4. **Calc chain**: lb ≤ cot-sum (h_harm_chain sorry) = tan-sub-sum (h_comp) ≤ full-sum (h_sub_le). ✓

### Key Findings

- **Nat subtraction cast**: `rw [show n-1-j = n-(j+1) from by omega]; push_cast [Nat.cast_sub h1]; ring`
  correctly handles `(n-1-j : ℕ) : ℝ = n - j - 1` by rewriting to avoid double subtraction.
- **Sub-sum via injection**: `Finset.sum_image (fun j _ j' _ h => hg_inj h)` + `Finset.sum_le_sum_of_subset_of_nonneg`
  gives the correct sub-sum inequality.
- **Complementary angle**: After proving `harg`, a single `rw [harg, sin_pi_div_two_sub, cos_pi_div_two_sub]`
  closes the equality.

### Remaining Sorry (`h_harm_chain`)

**Goal**: (1/(2π))*n*log(n+1) ≤ Σ_{j<√n} cos((2j+1)π/(4n)) / sin((2j+1)π/(4n))

**Strategy** (documented in inline comments):
1. Each term cot((2j+1)π/(4n)) ≥ 2n/(π(2j+1)) by `cot_ge_inv_two_mul`
   - Angle bound: (2j+1)π/(4n) ≤ π/3 needs (Nat.sqrt n)^2 ≤ n (needs Mathlib lemma name for this)
   - Then 3*(2j+1) ≤ 4n follows from 6j-3 ≤ 4m^2 ≤ 4n (quadratic m^2 ≤ n: always positive)
2. Σ_{j<m} 2n/(π(2j+1)) ≥ (n/π)*harmonic(m) (since 1/(2j+1) ≥ (1/2)/(j+1))
3. harmonic(m) ≥ log(m+1) from `log_add_one_le_harmonic` (Mathlib)
4. log(m+1) ≥ (1/2)*log(n+1) since (m+1)^2 ≥ n+1 from `Nat.lt_succ_sqrt n : n < (m+1)^2`
5. Net: ≥ (n/π)*(1/2)*log(n+1) = (1/(2π))*n*log(n+1) ✓

**Key Mathlib gap**: Need `(Nat.sqrt n)^2 ≤ n` — likely `Nat.sqrt_le'` or similar (exact name TBD).

### Next Steps
~~1. Find correct Lean4 Mathlib name for `(Nat.sqrt n)^2 ≤ n` (try `Nat.sqrt_le'`, `Nat.le_sqrt`)~~
~~2. Prove `h_harm_chain` via the 5-step strategy above~~
→ COMPLETED in Session 2026-04-26b (see below)

## Session 2026-04-26b — h_harm_chain Proved

**Outcome**: progress — sorry count 3 → 2  
**Sorries closed**: `h_harm_chain` inside `trig_sum_lb_of_cos_eq_neg_one`

### What I Did

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

### Remaining Sorries (2)

1. `chebyshev_trig_sum_lb` — x ∈ (-1,1) Lipschitz/harmonic argument
2. `divergence_from_lebesgue_growth` — lacunary construction / UBP gap

### Next Steps
1. Attempt `chebyshev_trig_sum_lb`: use sin(φₖ) ≥ s/2 near k₀ + harmonic sum
2. For sorry #2: weaken to lim sup = ∞ (provable by Banach-Steinhaus)
