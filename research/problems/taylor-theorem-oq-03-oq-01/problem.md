# Problem: Bridge taylorWithinEval to expPartialSum for Remainder Axiom Elimination

**Slug**: taylor-theorem-oq-03-oq-01
**Created**: 2026-04-05T04:46:25-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The open question: can the two remainder axioms in the Taylor series convergence proof
be fully proved by connecting Mathlib's `taylorWithinEval` (local polynomial) to
`expPartialSum` (global partial sums), using the fact that `iteratedDerivWithin` on
`Icc a b` equals `iteratedDeriv` for globally smooth functions?

Concretely, prove (without axioms) the equivalence:

$$
\text{taylorWithinEval}(\exp, n, [0,x], 0, x) = \sum_{k=0}^{n} \frac{x^k}{k!}
$$

via the bridge `iteratedDerivWithin k \exp (Icc 0 x) = iteratedDeriv k \exp` for
all k, using that `exp` is globally C^∞.

### Plain Language

`TaylorTheoremOQ03.lean` uses Mathlib's `taylorWithinEval` (the Taylor polynomial
restricted to a closed interval) to state the Lagrange remainder theorem. Separately,
`expPartialSum` is the standard partial sum `∑ x^k/k!`. The question is whether these
two representations can be bridged purely from Mathlib lemmas, i.e., whether
`taylorWithinEval exp n (Icc 0 x) 0 x = ∑ k in range (n+1), x^k / k!`.

The key step: `exp` is globally C^∞, so `iteratedDerivWithin k exp (Icc 0 x) y =
iteratedDeriv k exp y = exp y` for every y ∈ Icc 0 x. This collapses the
`taylorWithinEval` sum to the standard `expPartialSum`.

### Why This Matters

This would eliminate any remaining axiom dependency in the Taylor-exp remainder
proof hierarchy, making the Lagrange remainder conclusion fully axiom-free for the
exponential function. It also demonstrates the technique for other analytic functions.

## Known Results

### What's Already Proven

- `iteratedDeriv_exp k : iteratedDeriv k Real.exp = Real.exp` — proved in `TaylorTheoremOQ03.lean`
- `taylorWithinEval` definition in `Mathlib.Analysis.Calculus.Taylor`
- `ContDiffOn.iteratedDerivWithin_eq_iteratedDeriv` — key bridge lemma (needs verification)
- `Real.contDiff_exp : ContDiff ℝ ⊤ Real.exp` — exp is globally smooth
- `exp_lagrange_remainder` — Lagrange remainder stated using `taylorWithinEval`

### What's Still Open

- Whether `taylorWithinEval exp n (Icc 0 x) 0 x = ∑ k in range (n+1), x^k / k!` can
  be proved directly from Mathlib without additional axioms
- Whether `iteratedDerivWithin k exp (Icc 0 x) = fun y => exp y` follows cleanly
  from `ContDiff.contDiffOn` + `ContDiffOn.iteratedDerivWithin_eq_iteratedDeriv`

### Our Goal

Prove the bridge lemma:
```lean
theorem taylorWithinEval_exp_eq_partialSum (x : ℝ) (hx : 0 < x) (n : ℕ) :
    taylorWithinEval Real.exp n (Icc 0 x) 0 x =
      ∑ k in Finset.range (n + 1), x ^ k / (k ! : ℝ) := by
  ...
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| taylor-theorem | Parent proof; uses same Mathlib Taylor infrastructure | `taylorWithinEval`, `ContDiff` |
| taylor-theorem-oq-03 | Direct parent; Cauchy remainder for exp convergence | `taylorWithinEval`, `iteratedDerivWithin` |
| e-transcendental | Uses exp series properties | power series, Liouville |
| fourier-series | Similar partial sum convergence pattern | `tsum`, `HasSum` |

## Initial Thoughts

### Potential Approaches

1. **Direct unfolding via `taylorWithinEval` definition**
   - Unfold `taylorWithinEval` to `taylorWithin`, then use `iteratedDerivWithin_eq_iteratedDeriv`
   - Why it might work: Mathlib has `ContDiffOn.iteratedDerivWithin_eq_iteratedDeriv` or similar
   - Risk: The exact lemma name may differ; requires checking current Mathlib API

2. **Via `Finset.sum` rewriting**
   - Show each summand `iteratedDerivWithin k exp (Icc 0 x) 0 / k! * x^k = x^k / k!`
   - Use `iteratedDeriv_exp k` then convert `iteratedDeriv` → `iteratedDerivWithin`
   - Risk: Direction of conversion (global → local is easier than local → global)

3. **Via `exp_series_summable` + HasSum**
   - Connect `taylorWithinEval` through the HasSum characterization of exp
   - May be cleaner for the convergence proof overall

### Key Difficulties

- `iteratedDerivWithin` vs `iteratedDeriv`: converting from restricted to global derivative requires `UniqueDiffOn` on `Icc 0 x`
- The exact Mathlib API for `ContDiffOn → iteratedDerivWithin = iteratedDeriv` needs verification
- `taylorWithin` unfolds to a `Finset.sum` over `range (n+1)` — need to match indexing

### What Would a Proof Need?

- Key lemma: `ContDiff.iteratedDerivWithin_eq_iteratedDeriv` or equivalent
- `uniqueDiffOn_Icc hx : UniqueDiffOn ℝ (Icc 0 x)` (for hx : 0 < x)
- `Real.contDiff_exp.contDiffOn` to get `ContDiffOn` on `Icc 0 x`
- Unfolding `taylorWithinEval` → `Finset.sum` representation

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is clear and the key ingredients exist in Mathlib
- Main challenge is API discovery: finding the right `iteratedDerivWithin = iteratedDeriv` lemma
- `#check` exploration in Lean should resolve this quickly
- Similar bridges have been done in other OQ files

**Estimated Effort**:
- Exploration: 1-2 hours (Mathlib API search)
- If tractable: 1 day (write and verify the bridge lemma)
- If hard: likely needs Aristotle for automation of intermediate steps

## References

### Mathlib
- `Mathlib.Analysis.Calculus.Taylor` — `taylorWithinEval`, `taylorWithin`, `taylor_mean_remainder_lagrange`
- `Mathlib.Analysis.Calculus.Deriv.Inverse` — iterated derivative infrastructure
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` — `Real.contDiff_exp`, `iteratedDeriv_exp`

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - taylor-series
  - mathlib-api
  - axiom-elimination
related_proofs:
  - taylor-theorem
  - taylor-theorem-oq-03
  - e-transcendental
difficulty: medium
source: gallery-gap
created: 2026-04-05T04:46:25-07:00
```

**Significance**: 7/10
**Tractability**: 7/10
