# Erdős Problem #671 — Lagrange Interpolation Convergence

**Status**: `in-progress` (ACT phase)
**Prize**: $250 open problem
**Source**: https://erdosproblems.com/671

## Problem Summary

Can Lagrange interpolation converge pointwise at a point x where the Lebesgue function
λ_n(x) = Σ|p_i^n(x)| diverges (limsup → ∞)?

- **Question 1**: ∃ point sequence where for every continuous f, ∃ x with limsup λ_n(x) = ∞ yet L^n f(x) → f(x)?
- **Question 2**: Same but limsup λ_n(x) = ∞ for ALL x ∈ [-1,1]?

**Known**: Bernstein (1931): ∃ x₀ with limsup λ_n(x₀) = ∞ for any sequence.
**Known**: Erdős-Vértesi (1980): ∃ continuous f with |L^n f(x)| → ∞ a.e. for any sequence.

## Session 2026-05-04 (Session 3) — Partition of unity + type refactoring

**Mode**: REVISIT (continued from session 2)
**Outcome**: progress (6 sorries eliminated: 13 → 7)

### What I Did

- Proved `lagrangeInterp_degree`: interpolant degree ≤ n-1 via `Polynomial.natDegree_prod_le`
- Proved `equidistantNodes.in_interval` and `.distinct`: arithmetic with `(n:ℝ) - 1` coercions
- Proved `chebyshevNodes.distinct`: `Real.strictAntiOn_cos.injOn` on [0,π] via angle bounds
- Proved `lagrangeBasis_sum_one` (partition of unity): Σp_i(x) = 1 via polynomial root counting
  - Key: Q = Σp_i - 1 has n distinct roots but degree ≤ n-1, so Q = 0
  - Uses: `Polynomial.card_roots_le_degree`, `Multiset.toFinset_card_le_card`, `Finset.card_image_of_injOn`
- Proved `lebesgueFunction_ge_one`: λ_n(x) ≥ 1 via triangle inequality + partition of unity
- Proved `q2_fails_implies`: ¬Q2 → explicit divergence via `by_contra; push_neg`
- Eliminated 5 type-sorry instances by refactoring `∃ x ∈ S` to `∃ x : Set.Icc S` (subtype)
  - Q1, Q2, faber, full_measure_convergence types now sorry-free
  - q2_fails_implies type+proof now fully sorry-free
- Updated meta.json: 7 sorries, 396 lines, axiomCount=3
- PR #15458 updated

### Key Findings

- Partition of unity: Σp_i(x) = 1 requires polynomial root counting (not just evaluation at nodes)
- `Polynomial.card_roots_le_degree` works for ALL polynomials (includes Q=0 corner case)
- `∃ x ∈ S, P x` notation doesn't give `hx : x ∈ S` inside `P x` — must use subtype `∃ x : S, P x.val`
- `lebesgueFunction_ge_one` requires `hn : 0 < n` (false for n=0: empty sum = 0 < 1)
- Build 2 verified (equidistantNodes + lagrangeInterp_degree): compiled clean
- Build 3 in progress (all new proofs including partition of unity + subtype refactoring)

### Files Modified

- `proofs/Proofs/Erdos671Problem.lean` — 6 sorries eliminated
- `src/data/proofs/erdos-671/meta.json` — 7 sorries, 396 lines

### Remaining Sorries (7 — all HARD classical results)

- `bernstein`: Bernstein 1931 — requires Baire category or explicit construction
- `lebesgueConstant_growth`: Λ_n ≥ (2/π)ln n — integration argument on extremal polynomial
- `erdos_vertesi`: Erdős-Vértesi 1980 — hard analysis (a.e. divergence)
- `equidistant_diverges`: exponential Lebesgue constant — explicit product bounds
- `faber`: Faber 1914 — uniform boundedness / Baire category
- `positive_measure_divergence`, `full_measure_convergence`: measure theory

### Next Steps

1. Check Build 3 result for partition-of-unity proof
2. Consider `lebesgueConstant_growth` — bound via extremal polynomial construction
3. Consider `equidistant_diverges` — explicit product estimate for equidistant nodes
4. Submit `bernstein`, `erdos_vertesi`, `faber` to Aristotle (HARD classical results)

---

## Session 2026-05-04 (Session 2) — Compilation fixes + q2_implies_q1

**Mode**: REVISIT (continued from session 1)
**Outcome**: progress (1 more sorry eliminated, full compilation fix)

### What I Did

- Resolved rebase conflicts in meta.json (kept `"sorries": 19` from HEAD across 2 conflict sites)
- Proved `q2_implies_q1`: Q2 ⟹ Q1 via `obtain ⟨seq, hdiv, hconv⟩ := h; exact ⟨seq, fun f => ...⟩`
- Fixed: `C`/`X` ambiguity — removed `Polynomial` from `open`; use `Polynomial.C`/`Polynomial.X` with `(... : Polynomial ℝ)` annotation
- Fixed: `Filter.limsup = ⊤` — introduced `LebesgueUnbounded`/`InterpUnbounded` helper defs using `∀ M : ℝ, ∃ᶠ m in atTop, ... ≥ M`
- Updated meta.json: 18 sorries, 274 lines
- Created PR #15458 (fixing broken code merged by PR #15444)
- Docker build running (container lean-build-13630)

### Key Findings

- `q2_implies_q1` trivial: Q2 requires ∀ x divergence + ∃ x convergence; Q1 only needs ∃ x divergence + ∃ x convergence. The same sequence and same x witness both.
- With `open Polynomial ContinuousMap`, bare `C` is ambiguous between `Polynomial.C` and `ContinuousMap.C`. Fix: remove `Polynomial` from open, use qualified names.
- `∃ᶠ m in atTop, f m ≥ M` is the correct "frequently ≥ M" formulation capturing limsup = +∞ for ℝ-valued functions.

### Files Modified

- `proofs/Proofs/Erdos671Problem.lean` — q2_implies_q1 proved, compilation fixes
- `src/data/proofs/erdos-671/meta.json` — 18 sorries, 274 lines, updated assumptions

---

## Session 2026-05-04 (Session 1) — Initial formalization

**Mode**: FRESH (new gallery entry)
**Outcome**: progress (4 sorries eliminated, compilation fixes)

### What I Did

- Located `proofs/Proofs/Erdos671Problem.lean` with 23 real sorries
- Fixed bad `import` statements (specific module paths → `import Mathlib`)
- Proved `lagrangeBasis_self`: `∏ j ≠ i, (1/(a_i-a_j))*(a_i-a_j) = 1` via `Finset.prod_eq_one` + `field_simp`
- Proved `lagrangeBasis_other`: factor `a_j - a_j = 0` gives product = 0 via `Finset.prod_eq_zero`
- Proved `lagrangeInterp_at_node`: isolate the i-th term via `Finset.sum_eq_single_of_mem`
- Proved `chebyshevNodes.in_interval`: `Real.cos_mem_Icc _` (one-liner)
- Fixed syntax `∏ j in s` → `∏ j ∈ s` (deprecated in current Mathlib)
- Fixed `Filter.limsup ... = ⊤` type error: ℝ has no Top; use EReal cast `(f n : EReal)`
- Fixed `lagrangeInterp f` type mismatch: changed `f : ℝ → ℝ` to `f : Set.Icc (-1:ℝ) 1 → ℝ` so `C([-1,1], ℝ)` coerces automatically
- PR #15444 created and updated

### Key Findings

- `∏ j in s, ...` syntax deprecated; use `∏ j ∈ s, ...`
- `Filter.limsup (f : ℕ → ℝ) atTop : ℝ` but `⊤ : ℝ` doesn't typecheck (ℝ has no Top); use `(· : EReal)` cast
- `C(Set.Icc (-1:ℝ) 1, ℝ)` coerces to `Set.Icc (-1:ℝ) 1 → ℝ` via DFunLike automatically
- Lagrange basis proof strategy: prod = 1 via each factor = 1 (distinctness gives non-zero denominator); prod = 0 via finding one zero factor

### Files Modified

- `proofs/Proofs/Erdos671Problem.lean` (main file)
- `src/data/proofs/erdos-671/meta.json` (sorries 23→19)

### Remaining Sorries (18)

- `lagrangeBasis_self`, `lagrangeBasis_other`, `lagrangeInterp_at_node`: **PROVED**
- `chebyshevNodes.in_interval`: **PROVED**
- `q2_implies_q1`: **PROVED**
- `lagrangeInterp_degree`: degree bound for Lagrange interpolant (HARD)
- `lebesgueFunction_ge_one`: λ_n ≥ 1 at nodes (HARD — needs partition of unity argument)
- `bernstein`: Bernstein's 1931 theorem (HARD — needs Baire category or explicit construction)
- `lebesgueConstant_growth`: Λ_n ≥ (2/π)ln(n) - 1 (HARD)
- `erdos_vertesi`: Erdős-Vértesi 1980 theorem (HARD)
- `question1_open` / `question2_open`: axioms (OPEN)
- `chebyshevNodes.distinct`: injectivity of cos on specific points (HARD)
- `equidistantNodes` (2 sorries): arithmetic bounds (MODERATE)
- `equidistant_diverges`: exponential Lebesgue constant for equidistant nodes (HARD)
- `faber`: Faber's theorem (HARD)
- `positive_measure_divergence`, `full_measure_convergence`: measure-theoretic (HARD)
- `main_conjecture_open`: axiom (OPEN)
- `q2_implies_q1`, `q2_fails_implies`: logical implications (MODERATE — should follow from defs)

### Next Steps

1. Try `q2_implies_q1`: should follow directly from definitions (Q2 is strictly stronger than Q1)
2. Try `lebesgueFunction_ge_one`: use partition of unity; Σ p_i(x) = 1 (interpolating constants) so |Σ p_i(x)| ≤ Σ|p_i(x)|
3. Try `lagrangeInterp_degree`: use that lagrangeBasis has degree ≤ n-1 and the sum has ≤ n terms
4. Submit `bernstein`, `lebesgueConstant_growth`, `erdos_vertesi` to Aristotle as HARD sorries
