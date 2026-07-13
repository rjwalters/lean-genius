# Knowledge Base: fourier-series-oq-02-oq-03-oq-02

Sharp constants for analytic (exponential) Fourier coefficient
decay — extending OQ-02-OQ-03's polynomial / Hölder framework.

---

## Problem Understanding

For periodic f : ℝ/Tℤ → ℂ extending holomorphically to the strip
{z : |Im z| < δ} and bounded there, Fourier coefficients decay
exponentially: |ĉ_n| ≤ K · e^{-2πδ|n|/T}.

Three questions:
1. **Sharp constant K(f)** for a given function — defined via the
   limsup `sup_n |ĉ_n| · e^{2πδ|n|/T}`.
2. **Sharpness of rate** — the exponent 2πδ/T cannot be improved
   (extremal: cosh-based functions with poles on the boundary).
3. **Converse (Paley-Wiener)** — exponential decay characterizes
   strip-analyticity.

---

## Insights

- Contour shifting is the key analytic technique: shift integration
  to `Im z = δ - ε`, periodicity cancels vertical edges, and the
  exponential factor `e^{-2πn(δ-ε)/T}` falls out.
- The exponential rate `2πδ/T` is sharp, achieved by cosh-extremal
  functions with poles exactly on the strip boundary.
- Paley-Wiener converse: exponential Fourier decay completely
  characterizes strip analyticity.
- The sharp constant `K(f) = sup_n |ĉ_n| · e^{2πδ|n|/T}` equals the
  strip-boundary norm for natural boundaries; can be strictly less
  when f extends further than δ.
- Strip width δ plays the role that Hölder exponent α plays in the
  polynomial regime, but yields exponentially faster decay.
- The Poisson kernel `P_r(x)` with `r ∈ (0,1)` has exact
  exponential decay with strip width `-T·ln(r)/(2π)`.
- `exp_decay_summable`: requires ℤ-indexed geometric series
  decomposition (split into `n ≥ 0` and `n < 0` halves).
- `sharpConstant` proofs: rely on `ciSup_le` / `le_ciSup` from
  `ConditionallyCompleteLattice` API.
- `ciSup_const.symm` converts a constant value to an iSup over a
  nonempty Prop index; `le_ciSup` lifts to outer iSup. Pattern:
  `calc x = iSup (const) ≤ iSup (outer)`.
- Data fix from prior session: `leanFiles` in problem JSON had
  pointed to `FourierSeries.lean` (parent), not
  `FourierSeriesOQ02OQ03OQ02.lean`.

---

## Roadmap to Close 2 Remaining Sorries

### Sorry 1: `exp_dominates_polynomial`
```lean
theorem exp_dominates_polynomial (c M : ℝ) (hc : 0 < c) (hM : 0 < M)
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ n in Filter.cofinite,
      M * Real.exp (-c * |↑n|) ≤ C * |↑n|⁻¹ ^ α
```
Strategy:
1. `Filter.cofinite` on `ℤ` translates to "for all but finitely
   many `n`". Equivalent: `|n| → ∞`.
2. Mathlib lemma: `Real.tendsto_pow_mul_exp_neg_atTop_nhds`
   states `(fun x => x^k * exp(-x)) → 0 at atTop`.
3. Real-α version: use `Real.tendsto_rpow_mul_exp_neg_atTop` if
   available, else cap with `Nat.ceil α`.
4. Translate via `Filter.tendsto.eventuallyLE` to get
   `eventually_atTop` and convert to `cofinite` on ℤ.

Estimate: ~30 lines if the right Mathlib lemma exists; ~80 if a
ceil bound is needed.

### Sorry 2: `analytic_hierarchy`
```lean
theorem analytic_hierarchy (f : AddCircle T → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hf : IsStripAnalytic δ f) :
    ∀ α : ℝ, 0 < α → Summable (fun n : ℤ => ‖fourierCoeff f n‖ * |↑n| ^ α)
```
Strategy:
1. Extract `(M, hM, hbound)` from `IsStripAnalytic`.
2. Use `Summable.of_nonneg_of_le`: bound by
   `M · exp(-c|n|) · |n|^α` which is summable by combining
   `exp_dominates_polynomial` (gives bound by `C · |n|^{-α'}` for
   some α' > 1) with `Summable.of_isBigO`/comparison tests.
3. Alternatively: use `summable_of_isBigO` plus the fact that
   `exp(-c|n|) · |n|^α` is `O(exp(-c|n|/2))` for large `|n|`,
   reducing to `exp_decay_summable`.

Estimate: ~40 lines.

---

## Roadmap to Eliminate 3 Axioms (Per File's Own Documentation)

### Axiom 1: `contour_shift_decay`
- **Need**: complex contour integration on periodic domains
- **Ingredients**: Cauchy's theorem for rectangles, vertical-edge
  cancellation by periodicity, dominated convergence for `ε → 0`
- **Mathlib gap**: periodic contour setup not formalized
- **Difficulty**: MODERATE (~300–500 lines)

### Axiom 2: `rate_is_sharp`
- **Need**: explicit extremal function
  `1 / (cosh(2πz/T) - cosh(2πδ/T))`
- **Ingredients**: pole structure on strip boundary, residue
  calculation for Fourier coefficients
- **Difficulty**: MODERATE (~200 lines, mostly explicit)

### Axiom 3: `paley_wiener_converse`
- **Need**: `∑ ĉ_n · e^{2πinz/T}` converges in the strip given
  exponential decay
- **Ingredients**: Weierstrass uniform-convergence theorem,
  holomorphic limits
- **Mathlib gap**: Weierstrass theorem exists; periodic setup
  needs work
- **Difficulty**: LOW–MODERATE (~200 lines)

**Total estimate**: ~700–1100 lines of new infrastructure.

---

## Dead Ends

- Trying to define `sharpConstant` purely as a `liminf` rather
  than a `iSup`: harder to bound, less canonical.
- Treating exponential decay as trivially polynomial: misses the
  interaction with strip width, gives weaker results.
- Using `Nat.find` on `IsStripAnalytic`: not decidable, only
  `Classical.choose` works.

---

## Sessions

### Session 2026-04-27 (researcher-4) — audit + roadmap
- Created `research/problems/fourier-series-oq-02-oq-03-oq-02/`
  documentation (problem.md, state.md, knowledge.md) — was missing.
- Documented 2-sorry + 3-axiom roadmap.
- No Lean source changes (disk at 921 MB free, below safe Docker
  threshold).

### Prior session — `sharpConstant_is_bound` proof
**Outcome**: 3 sorries → 2 sorries
- Used `ciSup_const + le_ciSup` with `BddAbove` from
  `IsStripAnalytic` to prove `sharpConstant_is_bound`.
- Remaining sorries: `exp_dominates_polynomial`,
  `analytic_hierarchy` (standard analysis, need
  `Filter.cofinite` / `Summable` machinery).

### Earlier session — file creation
- Created `FourierSeriesOQ02OQ03OQ02.lean`:
  3 axioms, 10 theorems, 4 definitions, 5 sorries initially.
- Defined `IsStripAnalytic`, `stripNorm`, `sharpConstant`,
  `poissonKernelStripWidth`.
- Proved structural lemmas: `exp_decay_pos`, `exp_decay_le_one`,
  `wider_strip_faster_decay`, `poissonKernel_strip_positive`.
- Created gallery entry; created Aristotle companion file with 6
  theorem sorries for automated proof search.

---

## Mathlib Gaps Summary

- `Real.rpow_mul_exp_neg_atTop` — real-power version of
  `tendsto_pow_mul_exp_neg_atTop_nhds` (may already exist as
  `Real.tendsto_rpow_mul_exp_neg_atTop_nhds_zero`?).
- Periodic complex contour integration with `AddCircle`.
- Weierstrass uniform-convergence theorem in periodic setup.
- Cosh-based extremal function Fourier coefficient computation.

---

## Next Action

Future session with Docker:
1. Close `exp_dominates_polynomial` (~30–80 lines).
2. Close `analytic_hierarchy` (~40 lines).
3. Update meta.json to reflect `sorries: 0`, badge stays `axiom`
   while 3 axioms remain.
