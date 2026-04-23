# Knowledge Base: fourier-series-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The question is whether Fourier coefficient square-summability for α-Hölder functions
can be proved by an elementary comparison argument (without Parseval's theorem or L² theory).

**Answer: YES.** The Hölder decay bound ‖ĉ_n‖ ≤ (C/2)·(T/(2|n|))^α, when squared, gives
‖ĉ_n‖² ≤ K/|n|^{2α} with K = (C/2)²·(T/2)^{2α}. Since α > 1/2 means 2α > 1, the
p-series ∑ 1/|n|^{2α} converges, and comparison gives the result.

**Critical threshold**: α = 1/2 is exactly the boundary — at α = 1/2 the bound becomes
O(|n|^{-1}) which leads to the harmonic series (divergent).

---

## Insights

### Lean 4 Technical Findings (2026-04-23)

1. **`Real.summable_nat_rpow_inv` needs explicit import**: NOT transitively available from
   `Mathlib.Analysis.Fourier.AddCircle`. Must add `import Mathlib.Analysis.PSeries`.

2. **`.2` vs `.mpr` on Iff**: In certain contexts, `.2` (numeric projection) works where
   `.mpr` fails as dot notation on `Iff` theorems.

3. **`Summable.mul_left` over `Summable.const_smul`**: `const_smul` requires
   `DistribMulAction` typeclasses that don't always resolve; `mul_left` is simpler for ℝ.

4. **`Nat.cast_nonneg'` vs `Nat.cast_nonneg`**: The prime version uses a more general
   typeclass compatible with `abs_of_nonneg`. Import from `Mathlib.Data.Nat.Cast.Order.Basic`.

5. **`pow_le_pow_left₀`**: Renamed from `pow_le_pow_left` in Lean 4.26.

6. **`Real.rpow_mul_natCast hb α 2`**: Gives `b^(α*2) = (b^α)^2` — bridges real and
   natural number powers without norm_cast complications.

7. **`positivity` and `Fact (0 < T)`**: `positivity` doesn't auto-extract `0 < T` from
   `[hT : Fact (0 < T)]`. Must add `have hT_pos := hT.out` explicitly.

8. **`summable_int_iff_summable_nat_and_neg`**: Reduces ℤ summability to two ℕ p-series.

9. **`Summable.of_norm_bounded_eventually`**: Comparison test with cofinite filter —
   allows finite exceptions (e.g., the n=0 term where |n|=0).

### Proof Architecture

The proof splits into 3 clean parts:
- Part I: p-series over ℤ (`summable_const_div_int_rpow`)
- Part II: squaring the decay bound (`fourierCoeff_sq_le_pseries_term`)
- Part III: comparison test (`fourierCoeff_sq_summable_of_holder_pseries`)

The algebraic core of Part II: (T/(2|n|))^{2α} = (T/2)^{2α}/|n|^{2α} via
`Real.div_rpow` — this lets us factor out the |n| dependence cleanly.

---

## Session 2026-04-23 — COMPLETED

**Mode**: FRESH  
**Outcome**: completed (main theorems 0 sorries, 1 intentional sorry for sharpness)

### What I Did
- Created `proofs/Proofs/FourierSeriesOQ02OQ02.lean` (197 lines)
- Fixed all pre-existing build errors in `FourierSeriesOQ02Incomplete01.lean`
- Built successfully via Docker (1 warning: 1 sorry in sharpness corollary)
- Created `src/data/proofs/fourier-series-oq-02-oq-02/meta.json`
- PR: rjwalters/lean-genius#11834

### Key Findings
- Elementary p-series proof is fully formalized (main results 0 sorries)
- Sharpness theorem (harmonic series divergence) left as sorry — requires
  `∑_{n:ℤ, n≠0} 1/|n| = ∞` which is not in Mathlib in this exact form
- OQ-01 (Parseval route, ~15 lines) is shorter; OQ-02 (p-series, ~150 lines) is more quantitative

### Files Modified
- `proofs/Proofs/FourierSeriesOQ02OQ02.lean` (new)
- `proofs/Proofs/FourierSeriesOQ02Incomplete01.lean` (fixed build errors)
- `src/data/proofs/fourier-series-oq-02-oq-02/meta.json` (new)

### Next Steps
- Harmonic series divergence over ℤ (`∑_{n≠0} 1/|n| = ∞`) would complete the sharpness sorry
- See open questions in meta.json: quantitative Fourier approximation rates for Hölder functions

---

## Dead Ends

### `const_smul` for p-series
`(Real.summable_nat_rpow_inv.2 hβ).const_smul K` fails with typeclass inference errors.
Use `mul_left K` instead — same mathematical content, simpler typeclass requirements.

### `simp` approach for abs rewriting in ℤ split
`simp [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]` fails due to typeclass
zero mismatch. Use explicit `rw` + `exact abs_of_nonneg (Nat.cast_nonneg' n)` instead.
