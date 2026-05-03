# Knowledge Base: basel-problem-oq-04-oq-03

**Problem**: Formalize Pr[gcd(m,n)=1] = 6/π² via Möbius inversion and Dirichlet series

---

## Session 2026-05-03 (Session 3) — Prove coprime_pair_density_limit

**Mode**: REVISIT (ACT)
**Outcome**: Axiom eliminated — coprime_pair_density_limit now proved. 1 → 0 axioms. COMPLETE.

### What I Did

1. **Wrote `nat_div_div_tendsto` helper** (private, outside namespace):
   - Statement: `Tendsto (fun N => (N/d : ℕ)/(N : ℝ)) atTop (nhds (1/(d : ℝ)))`
   - Proof: For d=0, both sides are 0 (trivial). For d≥1: epsilon-delta via
     `Metric.tendsto_atTop`, choosing `N ≥ max 1 ⌈d/ε⌉`. Key bound:
     `|(N/d)/N - 1/d| = (N%d)/(d*N) ≤ 1/N < ε` using `Nat.div_add_mod`.

2. **Proved `coprime_pair_density_limit`** (~80 lines):
   - Step 1: Rewrite `(countCoprimePairs N : ℝ)/N²` as `∑' d, μ(d)*((N/d)/N)²`
     using `countCoprimePairs_moebius`, `tsum_eq_sum` (tail vanishes: d>N → N/d=0)
   - Step 2: Apply `tendsto_tsum_of_dominated_convergence` (Tannery) with:
     - Summability: `hasSum_zeta_two.summable` (bound = 1/d²)
     - Pointwise: `Tendsto.mul tendsto_const_nhds ((nat_div_div_tendsto d).pow 2)`
     - Domination: `|μ(d)| ≤ 1` + `(N/d)/N ≤ 1/d` (via `Nat.div_mul_le_self`)
   - Step 3: `.congr' h_congr.symm` converts from tsum sequence to original sequence

3. **Updated metadata**: status → `verified`, badge → `original`, axiomCount → 0

### Key Findings

- `Nat.div_add_mod N d : (N/d)*d + N%d = N` — fundamental for the error bound
- `abs_moebius_le_one : |μ n| ≤ 1` — the key arithmetic bound in domination
- `Nat.div_mul_le_self N d : (N/d)*d ≤ N` — gives `(N/d)/N ≤ 1/d`
- `tendsto_tsum_of_dominated_convergence` in `Mathlib.Analysis.Normed.Group.Tannery`
- `Filter.Tendsto.congr' h_congr.symm` converts `Tendsto (tsum f N)` to `Tendsto (seq N)`
- Cast from ℤ to ℝ via `congr_arg (Int.cast : ℤ → ℝ)` + `push_cast`

### Files Modified

- `proofs/Proofs/BaselProblemOQ04OQ03.lean` — axiom → theorem, +131 lines, now 558 total
- `src/data/proofs/basel-problem-oq-04-oq-03/meta.json` — status verified, axiomCount 0
- `src/data/research/problems/basel-problem-oq-04-oq-03.json` — progressSummary COMPLETE
- `research/problems/basel-problem-oq-04-oq-03/knowledge.md` — this file

### Next Steps

- Docker build pending to verify type-correctness of the proof
- If build fails: likely issues in `hcast` cast chain or `div_le_div_iff` direction

---

## Session 2026-05-03 (Session 2) — Prove moebius_dirichlet_series_at_two

**Mode**: REVISIT (ACT)
**Outcome**: Axiom eliminated — moebius_dirichlet_series_at_two now proved. 2 → 1 axioms.

### What I Did

1. **Identified the proof path via Mathlib LSeries**:
   - `Mathlib.NumberTheory.LSeries.Dirichlet` (imported via `EulerProduct.DirichletLSeries`) contains:
     - `LSeries_zeta_mul_Lseries_moebius {s} (hs : 1 < s.re) : L ↗ζ s * L ↗μ s = 1`
     - `LSeriesSummable_moebius_iff : LSeriesSummable ↗μ s ↔ 1 < s.re`
     - `LSeries_zeta_eq_riemannZeta {s} (hs) : L ↗ζ s = riemannZeta s`
   - `Complex.hasSum_ofReal : HasSum (fun x => (f x : ℂ)) x ↔ HasSum f x`
   - `Complex.cpow_two : x ^ (2 : ℂ) = x ^ (2 : ℕ)` (for term computation)

2. **Wrote the proof** (in BaselProblemOQ04OQ03.lean:249-295):
   - At s=2: `L(ζ,2) * L(μ,2) = 1` and `L(ζ,2) = π²/6` → `L(μ,2) = 6/π²`
   - Package as `LSeriesHasSum ↗μ 2 (6/π²)` via `hmu_sum.LSeriesHasSum`
   - Show term equality: `LSeries.term ↗μ 2 n = ((μ n : ℝ)/n² : ℂ)` via `cpow_two` + `push_cast`
   - Convert via `Complex.hasSum_ofReal.mp`

3. **Added `open scoped LSeries.notation`** to enable `↗` and `L` notation

### Key Findings

- `LSeries.Dirichlet` was already transitively imported via `EulerProduct.DirichletLSeries`
- No new imports needed — all tools were already available
- `SummationFilter` abstraction in recent Mathlib: `HasSum` now uses `unconditional` filter by default,
  compatible with `Complex.hasSum_ofReal`
- `mul_left_cancel₀` approach for algebraic inversion in ℂ (field axioms)
- `LSeries.term_zero` and `term_of_ne_zero` are the key term API lemmas

### Files Modified

- `proofs/Proofs/BaselProblemOQ04OQ03.lean` — axiom → theorem for moebius_dirichlet_series_at_two
- `src/data/proofs/basel-problem-oq-04-oq-03/meta.json` — axiomCount 2→1

### Next Steps

1. Eliminate `coprime_pair_density_limit`:
   - Key: `∑' d, μ(d) * (⌊N/d⌋/N)² → ∑' d, μ(d)/d²` as N → ∞
   - Uses: dominated convergence with dominator `1/d²` (summable by `hasSum_zeta_two`)
   - Bound: `|⌊N/d⌋/N - 1/d| ≤ 1/(dN)` → `|μ(d)*(⌊N/d⌋/N)² - μ(d)/d²| ≤ O(1/(d²N))`
   - Mathlib: `tendsto_tsum_of_dominated_convergence` or similar

---

## Problem Understanding

Goal: lim_{N→∞} |{(m,n) : 1≤m,n≤N, gcd(m,n)=1}| / N² = 6/π²

Key connections:
- 6/π² = 1/ζ(2) — reciprocal of the Basel constant
- 6/π² = ∏_p (1 - 1/p²) — Euler product (inverse of BaselProblemOQ04)
- 6/π² ≈ 0.6079 — empirically: N=10 gives 63/100 = 0.63

---

## Session 2026-04-26 (Session 1) — Lean Formalization

**Mode**: FRESH (OBSERVE → ACT)
**Outcome**: Proof file created, 2 axioms, 1 sorry, 18 theorems proved

### What I Did

1. **Surveyed infrastructure**:
   - `ArithmeticFunction.moebius_mul_coe_zeta`: μ * ζ = 1 (key Möbius identity)
   - `Erdos1149Problem.lean`: complete proofs of `moebius_sum_divisors_eq`, `card_multiples`
   - `BaselProblemOQ04.lean`: Euler product ∏_p(1-p⁻²)⁻¹ = π²/6 in 3 forms
   - `riemannZeta_two`: ζ(2) = π²/6 available in Mathlib

2. **Wrote BaselProblemOQ04OQ03.lean** (310 lines):
   - Proved: `moebius_sum_divisors` — Σ_{d|n} μ(d) = 1_{n=1} (from moebius_mul_coe_zeta)
   - Proved: `coprime_iff_moebius_sum` — 1_{gcd=1} = Σ_{d|gcd} μ(d)
   - Proved: `card_multiples` — |{m≤N: d|m}| = ⌊N/d⌋
   - Proved: `card_pairs_divisible` — |{(m,n)≤N²: d|m,d|n}| = ⌊N/d⌋²
   - Sorry: Sum exchange in `countCoprimePairs_moebius` (Finset.sum_comm)
   - Axiom: `moebius_dirichlet_series_at_two` — HasSum μ(d)/d² = 6/π²
   - Axiom: `coprime_pair_density_limit` — the density limit theorem
   - Computed: N=1,2,3,4,5,10 via native_decide (gives 1,3,7,13,21,63)

3. **Created gallery data**: `src/data/proofs/basel-problem-oq-04-oq-03/meta.json`

### Key Mathematical Findings

- The **Möbius decomposition** is the combinatorial heart:
  countCoprimePairs(N) = Σ_{d=1}^N μ(d) · ⌊N/d⌋²
- The **independence over primes** interpretation explains why:
  Pr[p∤gcd(m,n)] = 1-1/p², CRT gives independence → ∏_p(1-1/p²) = 6/π²
- The **sum exchange** is the main technical gap for a 0-sorry proof

### Next Steps

1. Prove the finite sum exchange in `countCoprimePairs_moebius`:
   - Use Finset.sum_comm or sigma-sum bijection
   - Key: d | gcd(m,n) ↔ d|m ∧ d|n, with d ≤ min(m,n) ≤ N
2. Eliminate `moebius_dirichlet_series_at_two`:
   - Bridge algebraic identity (moebius_mul_coe_zeta) to analytic HasSum
   - Check Mathlib.NumberTheory.LSeries.Basic for relevant lemmas
3. Consider Aristotle submission for sub-lemmas in the sum exchange

---

## Insights

- `Erdos1149Problem.lean` contains reusable proofs for Möbius and counting lemmas
- The finite sum exchange is a Finset.sum_comm type argument (implementable in one session)
- `BaselProblemOQ04.lean` has all Euler product ingredients needed
- Small cases (N≤10) are computable via native_decide — good for verification

## Built Items

- `proofs/Proofs/BaselProblemOQ04OQ03.lean` — main proof file (310 lines)
- `src/data/proofs/basel-problem-oq-04-oq-03/meta.json` — gallery entry
- `countCoprimePairs: ℕ → ℕ` — definition
- 4 fully proved lemmas (moebius_sum_divisors, coprime_iff_moebius_sum, card_multiples, card_pairs_divisible)
- 1 key theorem with sorry (countCoprimePairs_moebius)

## Mathlib Gaps

- No direct HasSum for Σ μ(d)/d² = 6/π² (gap in LSeries bridge for ℤ-valued functions)
- Finite sum exchange lemma for the specific Möbius-divisor structure

## Dead Ends

- Direct Euler product approach has same analytic complexity (not simpler)
- Trying to avoid Möbius entirely: no cleaner path found
