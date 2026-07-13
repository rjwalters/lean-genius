# Problem: The Generalized Euler Constant of an Antitone Function — Convergence of the Sum–Integral Defect

**Slug**: antitone-integral-sum-comparison-oq-01-oq-02-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap (open-question child of antitone-integral-sum-comparison-oq-01-oq-02)

## Problem Statement

The parent entry pinned the defect `Hₙ − log n → γ` for the special function
`f(x) = 1/x`, bridging to Mathlib's `Real.eulerMascheroniConstant`. This child
abstracts that result: for an **arbitrary** non-increasing, non-negative `f` on
`[1, ∞)` whose integral diverges, the "sum minus integral" defect still converges
to a finite limit — the *generalized Euler constant of `f`*. The special case
`f(x) = 1/x` recovers `γ`.

### Formal Statement

Let `f : ℝ → ℝ` be antitone on `[1, ∞)` with `f x ≥ 0` there (divergence of
`∫₁^∞ f` is what makes the problem nontrivial, but it is not needed for the
convergence claim itself — the defect converges regardless). Define the
**defect sequence**

```
D n = (∑ k ∈ Finset.Icc 1 n, f k) − ∫ x in (1:ℝ)..n, f x.
```

The claim is that `D` converges:

```lean
theorem antitone_defect_converges
    {f : ℝ → ℝ} (hmono : AntitoneOn f (Set.Ici 1))
    (hnonneg : ∀ x ≥ (1:ℝ), 0 ≤ f x)
    (hint : ∀ n : ℕ, IntervalIntegrable f MeasureTheory.volume 1 n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, f k) - ∫ x in (1:ℝ)..n, f x)
      Filter.atTop (nhds L) := by
  sorry
```

The proof is a bounded–monotone convergence argument: `D` is **monotone
decreasing** and **bounded below by 0**, so it converges by
`tendsto_atTop_ciInf` (an antitone sequence bounded below tends to its infimum).
The limit is `L = ⨅ n, D n`.

### Plain Language

Picture the graph of a non-increasing curve `y = f(x)` and the staircase of
rectangles of width 1 and heights `f(1), f(2), f(3), …`. The left-endpoint
staircase overestimates the area under the curve, so on each unit interval
`[k, k+1]` the sliver between the step `f(k)` and the curve has positive area,
namely `f(k) − ∫ₖ^{k+1} f`. Because `f` is non-increasing, this sliver is at
most `f(k) − f(k+1)`, and summing telescopes to at most `f(1)`. The total
overhang — the sum of all the slivers — is therefore finite and non-negative:
that total is exactly the limiting defect. When `f(x) = 1/x` the curve is the
hyperbola, the staircase is the harmonic series, the overhang is `γ ≈ 0.5772`,
and the picture is the classical derivation of the Euler–Mascheroni constant.

### Why This Matters

The parent proof does the whole story for one function, `f(x) = 1/x`, and lands
on `Real.eulerMascheroniConstant`. But the *mechanism* — a monotone, bounded
defect converging by the integral test — is completely general and reusable.
Formalizing it once yields a clean piece of Mathlib-style infrastructure: a
"generalized Euler constant exists" lemma applicable to `f(x) = 1/xᵖ` for
`0 < p ≤ 1`, `f(x) = 1/(x log x)`, and any other antitone divergent series,
each of which currently would require a bespoke argument.

Mathlib already knows the harmonic special case tightly: the divergence itself is
`Real.tendsto_sum_range_one_div_nat_succ_atTop` (partial sums of `∑ 1/(n+1)` tend
to `atTop`), and the constant lives at `Real.eulerMascheroniConstant` with the two
defect limits `Real.tendsto_harmonic_sub_log` and
`Real.tendsto_harmonic_sub_log_add_one` and the monotone bracketing sequences
`Real.eulerMascheroniSeq` / `eulerMascheroniSeq'`. What Mathlib does **not**
have is the abstract antitone version; this problem supplies it, and the parent
entry's `f = 1/x` proof becomes a corollary obtained by unfolding definitions.

### Known Results

The two ingredients are both elementary and both already available in Mathlib in
the exact form the parent uses.

1. **Per-interval sandwich (antitonicity).** For `f` antitone on `[k, k+1]`,
   ```
   f (k+1) ≤ ∫ x in (k:ℝ)..(k+1), f x ≤ f k,
   ```
   the two halves being `AntitoneOn.sum_le_integral` and
   `AntitoneOn.integral_le_sum` (the same lemmas the root proof
   `AntitoneIntegralSumComparison.integral_sandwich` packages). Consequently
   ```
   0 ≤ f k − ∫ₖ^{k+1} f ≤ f k − f (k+1).
   ```

2. **Bounded-monotone convergence.** A sequence that is antitone and bounded
   below converges to its infimum. In Lean:
   `tendsto_atTop_ciInf (h_anti : Antitone D) (hbdd : BddBelow (Set.range D))`
   gives `Tendsto D atTop (𝓝 (⨅ n, D n))`.

Combining: `D` is decreasing (item 1 makes each increment `≤ 0`) and bounded
below by `0` (item 1 telescopes), so it converges (item 2). Divergence of
`∫₁^∞ f` is not required for convergence of the *defect*; it is the hypothesis
that makes the result interesting (otherwise both `∑ f` and `∫ f` converge
separately and the defect is a trivial difference of limits).

### Suggested Approach

A concrete Lean plan, naming only lemmas that appear in the parent/root files or
standard Mathlib:

1. **Split the integral additively.** Write
   `∫₁^{n+1} f = ∫₁^n f + ∫ₙ^{n+1} f` via
   `intervalIntegral.integral_add_adjacent_intervals` (needs the
   `IntervalIntegrable` hypotheses `hint`). Then
   ```
   D (n+1) − D n = f (n+1) − ∫ₙ^{n+1} f.
   ```

2. **Monotone decreasing.** On `[n, n+1]`, antitonicity gives
   `f (n+1) ≤ ∫ₙ^{n+1} f` (from `AntitoneOn.integral_le_sum`, or directly
   `intervalIntegral.integral_mono_on` against the constant `f (n+1)`), hence
   `D (n+1) − D n ≤ 0`. Package as `Antitone D` via
   `antitone_nat_of_succ_le`.

3. **Bounded below by 0.** Telescoping the per-interval upper bound
   `∫ₖ^{k+1} f ≤ f k` over `k = 1 … n−1` gives `∫₁^n f ≤ ∑_{k=1}^{n−1} f k`,
   so `D n ≥ f n ≥ 0` (using `hnonneg`). Establish
   `BddBelow (Set.range D)` with `0` as a lower bound (`bddBelow_def` /
   `mem_lowerBounds`).

4. **Conclude.** Apply `tendsto_atTop_ciInf` (antitone + `BddBelow`) to obtain
   `Tendsto D atTop (𝓝 (⨅ n, D n))`, and provide the witness
   `L := ⨅ n, D n` via `Filter.Tendsto` and `⟨_, _⟩`.

5. **Sanity check the special case.** Instantiate `f := fun x => 1/x`. With the
   root file's `oneDiv_antitone` and `log_integral`, `D n` becomes
   `Hₙ − log n`, whose limit is `Real.eulerMascheroniConstant` by
   `Real.tendsto_harmonic_sub_log`; this confirms the abstract `L` specializes
   to `γ` and mirrors the parent's `tendsto_harmonic_sub_log`.

The whole argument stays inside real analysis with no measure-theoretic
subtleties beyond `IntervalIntegrable`; the antitone per-interval bounds and the
`ciInf` convergence lemma are the only non-trivial imports.

### Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - analysis
  - integral-test
  - euler-mascheroni
  - convergence
  - monotone-convergence
  - asymptotics
  - harmonic-numbers
rationale: >
  Genuinely tractable: the result is a textbook bounded-monotone convergence
  argument, and every ingredient (AntitoneOn.integral_le_sum /
  AntitoneOn.sum_le_integral from the root proof, tendsto_atTop_ciInf,
  intervalIntegral.integral_add_adjacent_intervals) is already in Mathlib. The
  significance is the reusable abstraction: it lifts the parent's single-function
  γ result to a general "generalized Euler constant exists" lemma that Mathlib
  currently lacks. Main care points are the IntervalIntegrable side-conditions
  and getting the telescoping lower bound clean.
```

### Related Gallery Proofs

| Slug | Relationship |
|------|--------------|
| `antitone-integral-sum-comparison-oq-01-oq-02` | Parent. Proves the special case `f(x) = 1/x`: `Hₙ − log n → γ = Real.eulerMascheroniConstant`, with the monotone bracketing `Hₙ − log(n+1) < γ < Hₙ − log n`. This child abstracts that convergence to arbitrary antitone non-negative `f`. |
| `antitone-integral-sum-comparison` | Root. Establishes the general integral-test sandwich `∑ f(x₀+i+1) ≤ ∫ f ≤ ∑ f(x₀+i)` via `AntitoneOn.sum_le_integral` / `AntitoneOn.integral_le_sum` — the per-interval engine reused here. |
| `antitone-integral-sum-comparison-oq-01` | Sibling intermediate node in the integral-test family (harmonic-defect boundedness). |
| `antitone-integral-sum-comparison-oq-01-oq-03` | Sibling open-question child on the same integral-test lineage. |
