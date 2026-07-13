# Knowledge Base: fair-games-theorem-oq-02-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Wald's Identity (1944): For i.i.d. integrable r.v.s X₁, X₂, ... and a stopping time τ with E[τ] < ∞:
  E[X₁ + X₂ + ... + X_τ] = E[X₁] · E[τ]

In Lean: `∫ ω, ∑ k in Finset.range (τ ω), X (k + 1) ω ∂μ = (∫ ω, X 0 ω ∂μ) * ∫ ω, (τ ω : ℝ) ∂μ`

This answers the open question from FairGamesTheoremOQ02OQ01: yes, Wald's Identity is fully formalizable
alongside Doob's OST using the same Mathlib infrastructure.

---

## Session 2026-04-24 (Session 2) - Eliminated Both Axioms → Verified

**Mode**: REVISIT
**Outcome**: completed (verified, 0 sorries, 0 axioms)

### What I Did
- Replaced `axiom integral_tau_eq_tsum_prob` with a complete Lean 4 proof:
  - Key path: `integral_eq_lintegral_of_nonneg_ae` → `ENNReal.ofReal_natCast` → `lintegral_nat_eq_tsum_prob` → `ENNReal.tsum_toReal_eq`
  - Private helper `lintegral_nat_eq_tsum_prob`: uses `lintegral_tsum` (Tonelli) after rewriting
    τ(ω) as ∑' k, {ω' | k < τ ω'}.indicator 1 ω (Ω-indexed indicator, avoids type confusion)
  - Key insight: use Ω-indexed indicator form `{ω' | k < τ ω'}.indicator 1 ω` (not ℕ-indexed)
    to match `lintegral_indicator_one`'s expected form exactly

- Replaced `axiom integral_sum_range_eq_tsum` with a complete Lean 4 proof:
  - Key tools: `integral_tsum_of_summable_integral_norm` for Fubini, `ENNReal.summable_toReal` for summability
  - Private helper `integral_indicator_norm_eq`: proves E[‖1_{τ>k}·X(k+1)‖] = E[‖X₀‖]·P(τ>k)
    using the same tower/pull-out/independence argument as `integral_indicator_prod_eq`
  - Summability: ∑ E[‖F_k‖] = E[‖X₀‖] · ∑ P(τ>k) = E[‖X₀‖] · E[τ] < ∞

### Key Findings
- **ENNReal tail sum**: The correct path is via `lintegral_tsum` (Tonelli in ℝ≥0∞, requires only
  AEMeasurable) followed by `lintegral_indicator_one`. The Ω-indexed indicator form is essential.
- **Fubini tool**: `integral_tsum_of_summable_integral_norm` (not `integral_tsum`) requires
  summability of ∫‖f_k‖ rather than absolute convergence of each f_k separately.
- **Summability chain**: ∑ ∫‖F_k‖ = E[‖X₀‖] · ∑ P(τ>k) = finite because E[τ] = ∑ P(τ>k) < ∞.
  `ENNReal.summable_toReal` converts ∑ μ{k < τ} ≠ ∞ to Summable (fun k => μ.real {k < τ}).
- **Type subtlety**: `lintegral_indicator_one` expects `s.indicator 1 ω` where s ⊂ Ω.
  Using `{k' : ℕ | k' < τ ω}.indicator 1 k` (ℕ-indexed) introduces a type mismatch.
  Solution: reformulate using `{ω' : Ω | k < τ ω'}.indicator 1 ω` directly.

### Files Modified
- `proofs/Proofs/FairGamesTheoremOQ02OQ01OQ01.lean` (expanded, 361 lines: +102 lines of proofs)
- `src/data/proofs/fair-games-theorem-oq-02-oq-01-oq-01/meta.json` (updated: verified, axiomCount=0)

---

## Session 2026-04-24 (Session 1) - Complete Axiomatization

**Mode**: FRESH
**Outcome**: completed (axiomatized, 0 sorries, 2 axioms)

### What I Did
- Identified the indicator decomposition proof approach: ∑_{k=1}^τ X_k = ∑_{k≥0} X_{k+1} · 1_{τ>k}
- Chose Lean formulation using `X (k+1)` summand (not `X k`) to ensure X(k+1) ⊥ ℱ_k
- Built 7 theorems/lemmas in `proofs/Proofs/FairGamesTheoremOQ02OQ01OQ01.lean`:
  1. `stopping_gt_measurable`: {τ > k} ∈ ℱ_k for stopping times
  2. `indicator_gt_sm`: 1_{τ > k} is ℱ_k-StronglyMeasurable
  3. `integral_indicator_prod_eq`: E[1_{τ>k} · X(k+1)] = E[X₀] · P(τ > k)
  4. `nat_cast_eq_tsum_indicator`: (n : ℝ) = ∑' k, 1_{k < n} (arithmetic identity)
  5. `wald_identity`: main theorem (requires 2 axioms)
  6. `wald_identity_bounded`: special case for bounded stopping times
  7. `wald_zero_mean_gives_zero_drift`: zero-mean corollary
- Created gallery integration: meta.json, annotations.json, index.ts
- Lean build: my file compiled cleanly (0 errors); pre-existing OQ03 errors did not affect my build

### Key Findings
- **Filtration indexing**: The natural filtration ℱ_n = σ(X₀,...,Xₙ) means X_{k+1} ⊥ ℱ_k (since k < k+1).
  Using X(k+1) in the sum resolves the off-by-one that would arise with X(k).
- **Independence pull-out**: `iIndepFun` + `condExp_natural_ae_eq_of_lt` gives E[X(k+1)|ℱ_k] = E[X₀]
  then `condExp_mul_of_stronglyMeasurable_left` factors the integral.
- **Two axioms needed** for full proof:
  1. `integral_tau_eq_tsum_prob`: E[τ] = ∑_{k≥0} P(τ > k) (tail sum formula)
  2. `integral_sum_range_eq_tsum`: Fubini-Tonelli for stopped sums (exchange sum/integral)
- Both axioms are classical analytic results; the tail sum formula exists in Mathlib for bounded
  integrals but the general dominated convergence version for stopping times isn't directly available.

### Files Modified
- `proofs/Proofs/FairGamesTheoremOQ02OQ01OQ01.lean` (new, 195 lines)
- `src/data/proofs/fair-games-theorem-oq-02-oq-01-oq-01/meta.json` (new)
- `src/data/proofs/fair-games-theorem-oq-02-oq-01-oq-01/annotations.json` (new)
- `src/data/proofs/fair-games-theorem-oq-02-oq-01-oq-01/index.ts` (new)

### Next Steps
- Eliminate Axiom 1 (tail sum): Mathlib's `MeasureTheory.integral_nat_cast` and layer-cake formula
  could prove this; try `tsum_measure_lt_eq_integral_lt` or build from `ENNReal.tsum_eq_integral`
- Eliminate Axiom 2 (Fubini): Use `MeasureTheory.integral_tsum` with summability hypothesis
  (`Summable` from integrability + finite expectation). May need dominated convergence.
- If both axioms eliminated, status upgrades from `axiomatized` to `verified`.

---

## Insights

- **Do NOT use martingale approach for Wald**: The stopped process S_{τ∧n} - (τ∧n)·E[X] is a
  martingale, but proving this requires the natural filtration to include X_n, creating an off-by-one
  in the independence argument. The indicator decomposition is cleaner and more direct.
- **Indicator decomposition is canonical**: ∑_{k=1}^τ X_k = ∑_{k≥0} X_{k+1} · 1_{τ>k} is the
  standard elementary proof and translates well to Lean. Each term factors by independence.
- **iIndepFun vs Indep**: Use `iIndepFun` (mutual independence of the sequence) rather than pairwise
  `Indep`. Mathlib's `iIndepFun.condExp_natural_ae_eq_of_lt` directly gives E[X(k+1)|ℱ_k] = E[X₀].
- **Tail sum in Lean**: The ENNReal route `lintegral_tsum` + `lintegral_indicator_one` is clean.
  The critical step is rewriting τ(ω) as ∑' k, {ω' | k < τ ω'}.indicator 1 ω (Ω-indexed!) first.
  Using a ℕ-indexed indicator ({k' | k' < τ ω}) causes type mismatch with lintegral_indicator_one.
- **Fubini in Lean**: `integral_tsum_of_summable_integral_norm` handles ∫∑' = ∑'∫ cleanly
  once summability of norms is established. `ENNReal.summable_toReal` is the bridge from
  ∑ μ{k < τ} ≠ ∞ (from finite E[τ]) to Summable (real-valued norms).

---

## Dead Ends

- **Martingale approach**: The process M_n = ∑_{k=1}^n X_k - n·E[X₁] is a martingale, but Doob's OST
  for this requires E[τ] < ∞ and uniform integrability. The indicator approach avoids this machinery.
- **Direct `integral_sum`**: Trying to swap sum and integral without explicit Fubini axiom failed at
  the summability hypothesis — need the summable auxiliary result first.
- **ℕ-indexed indicator for tail sum**: `{k' : ℕ | k' < τ ω}.indicator 1 k` is definitionally equal
  to `{ω' | k < τ ω'}.indicator 1 ω` but causes type confusion with lintegral_indicator_one.
  Always use the Ω-indexed form in lintegral arguments.
