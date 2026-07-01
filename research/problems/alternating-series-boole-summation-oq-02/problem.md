# Problem: Boole Summation in Normed Spaces: Finite Identity and Remainder Bound over Banach-Valued Sequences

**Slug**: alternating-series-boole-summation-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: alternating-series-boole-summation

## Problem Statement

### Formal Statement

$$
\Big\| \mathrm{altSum}\,a\,n\,m - \tfrac12\big((-1)^n a_n - (-1)^m a_m\big)\Big\| \le \tfrac12 \sum_{j=n}^{m-1} \|\Delta a_j\|,\qquad a:\mathbb{N}\to E
$$

### Plain Language

The parent proves the finite Boole summation identity and total-variation bound only for real sequences. Generalize both to sequences a : ℕ → E valued in a normed ℝ-vector space E (e.g. E = ℂ, or a Banach space). Show the first-order identity altSum a n m = ½·((-1)^n·a_n − (-1)^m·a_m) − ½·altSum(Δa) n m over any ℝ-module, and the corresponding norm bound.

### Why This Matters

One engine then covers ℂ-valued, operator-valued, and Fourier/Dirichlet partial sums. The algebraic Boole identity is domain-agnostic; the honest scope is that the finite identity and remainder bound port, while the antitone/telescoping monotonicity bounds do NOT (E is unordered).

## Known Results

### What's Already Proven

- Parent entry `alternating-series-boole-summation` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `alternating-series-boole-summation`. Category: **generalization**.

## Target Lean Sketch

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def altSum (a : ℕ → E) (n m : ℕ) : E := ∑ j ∈ Finset.Ico n m, (-1:ℝ)^j • a j
def fdiff (a : ℕ → E) (j : ℕ) : E := a (j+1) - a j

theorem boole_first_normed (a : ℕ → E) {n m : ℕ} (h : n ≤ m) :
    altSum a n m
      = (1/2:ℝ) • ((-1:ℝ)^n • a n - (-1:ℝ)^m • a m) - (1/2:ℝ) • altSum (fdiff a) n m := by
  sorry

theorem altSum_sub_model_norm_le (a : ℕ → E) {n m : ℕ} (h : n ≤ m) :
    ‖altSum a n m - (1/2:ℝ) • ((-1:ℝ)^n • a n - (-1:ℝ)^m • a m)‖
      ≤ (1/2:ℝ) * ∑ j ∈ Finset.Ico n m, ‖fdiff a j‖ := by
  sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `alternating-series-boole-summation` | Parent: real Boole summation identity + bound | finite differences, summation by parts |
| `alternating-series-boole-summation-oq-01` | Sibling: m→∞ limit passage (real case) | tsum, Filter.Tendsto |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. Port `altSum`/`fdiff`/`altSum_succ` to E, proving `altSum_succ` from `Finset.sum_Ico_succ_top`.
2. Prove `boole_first_normed` by `Nat.le_induction`; in the successor step rewrite both altSums via altSum_succ, substitute the IH, close with `module` (handle (-1)^(m+1)•x via pow_succ/neg_smul).
3. Derive the norm bound: rearrange to altSum − model = −½•altSum(Δa) n m, then chain `norm_smul`, `norm_sum_le`, and ‖(-1:ℝ)^j • Δaⱼ‖ = ‖Δaⱼ‖. Finish with a worked E = ℂ instantiation.

## References

### Mathlib

- `Finset.sum_Ico_succ_top` — Algebra/BigOperators/Intervals.lean (drives the one-step recurrence; used by verified parent)
- `Nat.le_induction` — induction on m ≥ n
- `norm_sum_le` — Analysis/Normed/Group/Basic.lean (‖∑ f‖ ≤ ∑ ‖f‖)
- `norm_smul` — Analysis/Normed/MulAction.lean (‖r • x‖ = ‖r‖ * ‖x‖)
- `module` tactic — Tactic/Module.lean (closes the smul identity where the parent used `ring`)

## Metadata

```yaml
tags:
  - analysis
  - series
  - alternating-series
  - boole-summation
  - normed-space
  - banach-space
  - finite-difference
  - remainder-bound
related_proofs:
  - alternating-series-boole-summation
  - alternating-series-boole-summation-oq-01
difficulty: low
source: proof-suggestion
created: 2026-06-30
```
