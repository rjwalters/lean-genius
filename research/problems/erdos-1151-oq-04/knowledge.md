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
- `chebyshevNode_is_root` (Session 2): T_n(cos φₖ) = 0
- `chebyshevNode_injective` (Session 2): Chebyshev nodes are distinct
- **`T_ofNat_ne_zero`** (Session 3): T_n ≠ 0 for n : ℕ
- **`natDegree_T_ofNat`** (Session 3): natDegree(T_n) = n for n : ℕ (by induction)
- **`leadingCoeff_T_ofNat`** (Session 3): leadingCoeff(T_n) = 2^{n-1} for n ≥ 1 (by induction)

**Aristotle companion (Erdos1151OQ04Aristotle.lean)** — all sorries CLOSED (Session 2):
- `cos_odd_half_pi`: cos((2k+1)π/2) = 0
- `chebyshevNode_is_root`: T_n at Chebyshev nodes = 0
- `chebyshevNode_injective`: nodes are distinct
- `n_mul_chebyshevAngle`, `chebyshevAngle_pos`, `chebyshevAngle_lt_pi`, etc. [arithmetic helpers]

## Hard Sorries Remaining (4 in main file)

### Remaining Sorries (2, as of Session 6)

### 1. `chebyshev_lebesgue_growth` [OPEN - harmonic sum lower bound]
Main result: Λₙ(cos(πp/q)) → ∞ for all n.
Key insight from Session 6: cos(πp/q) is NEVER a Chebyshev node when q is odd (x_not_chebyshev_node).
So `chebyshev_lebesgue_eq_all_n` applies for ALL n.
Formula: Λₙ = |cos(nπp/q)| / n · Σₖ sin(φₖ) / |cos(πp/q) - cos φₖ|.
Remaining: show Λₙ → ∞. Key step: the trig sum S(n) ≥ C·n·log(n) (harmonic lower bound).
For the full sequence: cos(nπp/q) can vanish for some n, so need a more refined argument.

### 2. `divergence_from_lebesgue_growth` [OPEN - fundamental gap]
Statement: Λₙ(x) → ∞ ⟹ ∃ continuous f, Lₙf(x) → +∞ (full sequence).
**Gap**: Banach-Steinhaus gives lim sup |Lₙf(x)| = ∞ (NOT lim = +∞).
Lacunary construction fails: cross terms from earlier n_j dominate n_k contribution.
May need to weaken axiom statement to lim sup = ∞ or find explicit construction specific to Chebyshev nodes.

## Session 2026-04-23 — Results (Session 6)

**Outcome**: progress
**Sorries closed**: 0 (new helper lemmas, no sorry reduction this session)
**New lemmas added**:
- `x_not_chebyshev_node (p q n k)`: For odd p, q, cos(πp/q) ≠ chebyshevNode n k for ALL n, k.
  Proof: parity argument — cos(πp/q) = cos((2k+1)π/(2n)) requires q*(2k+1) = even, but LHS is odd (q odd, 2k+1 odd). Contradiction.
- `chebyshev_lebesgue_eq_all_n`: applies lebesgue_eq for ALL n ≥ 1 when p, q odd.
  Direct consequence of x_not_chebyshev_node + chebyshev_lebesgue_eq.

**Key insight discovered**: For q ODD, x = cos(πp/q) is NEVER a Chebyshev node of any degree. This is because the node condition q*(2k+1) = 4j*n*q ± 2n*p requires an odd integer to equal an even integer. This means `chebyshev_lebesgue_eq` (the trigonometric sum formula) applies for ALL n (not just the n = mq subsequence as previously thought).

**Remaining blockers**: 
1. Harmonic sum lower bound for `chebyshev_lebesgue_growth`
2. `divergence_from_lebesgue_growth` may require weakening (lim sup = ∞ instead of lim = +∞)

**PR**: TBD (this session)

## Session 2026-04-23 — Results (Session 5)

**Outcome**: progress
**Sorries closed**: 2 (lagrange_basis_chebyshev_formula ✓, chebyshev_lebesgue_eq ✓, from 4 → 2 sorries)
**New proofs added**:
- `chebyshev_product_formula`: T_n = 2^{n-1} · ∏(X - C(cos φₖ)) — key algebraic identity
  Proof: T_n - Q has degree < n and n distinct roots (Chebyshev nodes) → T_n - Q = 0
- `lagrange_basis_chebyshev_formula`: explicit Lagrange basis at Chebyshev nodes
  Uses product formula + T_derivative_eq_U + U_real_cos
- `chebyshev_lebesgue_eq`: Λₙ(cos θ) = |cos(nθ)|/n · Σ sin(φₖ)/|cos θ - cos φₖ|
  Direct from lagrange_basis_chebyshev_formula

**PR**: #11829 (merged)

## Session 2026-04-23 — Results (Session 4)

**Outcome**: progress
**Sorries closed**: 0 (build fixes — Session 3 lemmas now compile)
**Build errors fixed** (Mathlib v4.26.0 API changes + proof bugs):
- `natDegree_T_ofNat | (n+2)`: `apply natDegree_sub_eq_left_of_natDegree_lt` failed (conclusion `p.natDegree` doesn't unify with `n+2`); fixed using `have key + rw`
- `chebyshevNode_is_root`: `field_simp; ring` — field_simp closes goal, `ring` had no goals; fixed by removing `ring`
- `chebyshevNode_injective`: `div_lt_iff` renamed to `div_lt_iff₀` in Mathlib v4.26.0; `nlinarith` then needed `omega` + `exact_mod_cast` to convert ℕ→ℝ strict bound before `nlinarith` for nonlinear finish

**Key technique learned**:
- When `apply lemma` fails "could not unify conclusion", use `have key := lemma proof; rw [key, ...]` instead
- `linarith` cannot multiply inequalities by variables (nonlinear); use `nlinarith` or provide product as hint `mul_lt_mul_of_pos_right`
- ℕ strict inequality `j.val < n` gives only `(j.val : ℝ) < n`, NOT `2 * j.val + 1 < 2 * n` in ℝ; must use `omega` first on ℕ, then `exact_mod_cast`

**PR**: rjwalters/lean-genius#11646 — all 3 Session 3 lemmas now build clean

## Session 2026-04-23 — Results (Session 3)

**Outcome**: progress  
**Sorries closed**: 0 (foundation proofs, not closing sorries directly)
**New proofs added** (prerequisites for product formula):
- `T_ofNat_ne_zero (n : ℕ) : T ℝ (n : ℤ) ≠ 0` — by T_eval_one
- `natDegree_T_ofNat : ∀ n : ℕ, (T ℝ (n : ℤ)).natDegree = n` — by two-step induction
- `leadingCoeff_T_ofNat : ∀ n ≥ 1, (T ℝ (n : ℤ)).leadingCoeff = 2^(n-1)` — by two-step induction

**Key proof techniques**:
- `T_ofNat_ne_zero`: `simp [T_eval_one h]` — T_n(1) = 1 ≠ 0
- `natDegree_T_ofNat`: two-step match, `natDegree_sub_eq_left_of_natDegree_lt` since deg(T_n) < deg(2X·T_{n+1})
- `leadingCoeff_T_ofNat`: two-step match, `leadingCoeff_sub_of_degree_lt` + `leadingCoeff_mul`; `(2 : ℝ[X]) = C 2` via `C_ofNat`

**Product formula proof strategy** (for next session):
Let Q_n = 2^{n-1} · ∏_{k : Fin n} (X - C (cos φₖ)).
Then T_n - Q_n has:
- natDegree ≤ n-1 (leading coefficients both 2^{n-1} cancel)
- n distinct roots: each cos φₖ is a root of T_n (chebyshevNode_is_root) and of Q_n
- A polynomial of degree < n with n distinct roots is zero (by card_roots_le_degree)
Therefore T_n = Q_n.

## Session 2026-04-22 — Results (Session 2)

**Outcome**: progress  
**Sorries closed**: 5 (chebyshevNode_is_root ×2, chebyshevNode_injective ×2, cos_odd_half_pi)
**Companion file**: now 0 sorries
**Main file**: 4 sorries remain (all blocked by Chebyshev product formula or hard lacunary construction)

**Key proofs**:
- `cos_odd_half_pi`: `rw [h, cos_add, cos_pi_div_two, mul_zero, sin_nat_mul_pi, ...]`
- `chebyshevNode_is_root`: simp [chebyshev_T_at_cos], arithmetic cast manipulation, cos_odd_half_pi
- `chebyshevNode_injective`: strictAntiOn_cos.injOn on angles in (0,π)

## Session 2026-04-23 — Results (Session 8)

**Outcome**: progress
**Sorries closed**: 0 (same count — 2 sorries, but proof structure significantly improved)
**New proofs added**:
- `chebyshev_lebesgue_lb`: now PROVED (modulo `chebyshev_trig_sum_lb` sorry)
  - Extracts δ from `cos_rational_pi_pos_min` and C₂ from `chebyshev_trig_sum_lb`
  - Takes C = δ·C₂ and shows Λₙ ≥ C·log(n+1) via `mul_le_mul` chain
  - Key calc: δ·C₂·log(n+1) = (δ/n)·(C₂·n·log(n+1)) ≤ (|cos(nθ)|/n)·S_n = Λₙ
- `chebyshev_trig_sum_lb` (new isolated sorry): S_n ≥ C₂·n·log(n+1)
  - Replaces the undifferentiated sorry in `chebyshev_lebesgue_lb`
  - Docstring explains strategy: Lipschitz |cos θ - cos φₖ| ≤ |θ - φₖ| + node spacing π/n

**Recovery work (session start)**:
- Restored 818-line (2-sorry) file from commit `eddbbdca9b` after squash-merge regression
- Root cause: ballot-problem enrichment PR #11991 was squash-merged from a branch predating PRs #11829/#11873/#11947

**Sorry analysis**:
1. `chebyshev_trig_sum_lb` — harmonic sum lower bound S_n ≥ C₂·n·log(n+1)
   - Strategy: nodes k₀+j at distance ≈ jπ/n from θ = πp/q
   - |cos θ - cos φₖ| ≤ |θ - φₖ| ≤ 2jπ/n (Lipschitz + node spacing)
   - sin(φₖ) ≥ C·sin(θ) near k₀ → each term ≥ C·sin(θ)·n/(2jπ)
   - Summing j = 1..n/2: S_n ≥ C·n·sin(θ)/2π · H_{n/2} ≥ C·n·log(n+1)/2
   - Mathlib: `log_add_one_le_harmonic` (H_n ≥ log(n+1)) available
   - Challenge: θ = πp/q might have sin(θ) close to 0 for large p/q; needs careful bounds
2. `divergence_from_lebesgue_growth` — full-sequence divergence from Λₙ → ∞
   - Fundamental gap: Banach-Steinhaus only gives lim sup |Lₙf(x)| = ∞, not lim = +∞
   - May need to weaken the axiom statement or find an explicit specialized construction

## Next Steps

1. **chebyshev_trig_sum_lb**: Prove S_n ≥ C₂·n·log(n+1) using Lipschitz bound + harmonic series.
   - Need: lower bound on sin(φₖ) near θ, upper bound on |cos θ - cos φₖ|
   - Mathlib tools: `Real.sin_pos_of_pos_of_lt_pi`, `Real.abs_cos_sub_cos_le`, `log_add_one_le_harmonic`
   
2. **divergence_from_lebesgue_growth**: Consider weakening the theorem.
   - Banach-Steinhaus gives lim sup = ∞ (NOT lim = +∞ as currently stated)
   - For lim = +∞: needs specialized construction for Chebyshev nodes at rational cosines
   - Option: weaken axiom statement to ∃ f, lim sup |Lₙf(x)| = ∞
