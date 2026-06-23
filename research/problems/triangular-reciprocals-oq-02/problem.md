# Problem: Generalized Triangular Reciprocals via Digamma — ∑1/(n(n+k)) = H_k/k

**Slug**: triangular-reciprocals-oq-02
**Created**: 2026-04-05T19:30:46-07:00
**Status**: Active (OBSERVE → ORIENT, S2)
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

For every integer $k \ge 1$,

$$
\sum_{n=1}^{\infty} \frac{1}{n(n+k)} \;=\; \frac{H_k}{k},
$$

where $H_k = \sum_{i=1}^{k} \frac{1}{i}$ is the $k$-th harmonic number.

Equivalently, via the digamma function $\psi$ and Euler–Mascheroni constant $\gamma$:

$$
\sum_{n=1}^{\infty} \frac{1}{n(n+k)} \;=\; \frac{\psi(k+1) + \gamma}{k}.
$$

### Plain Language

For each fixed offset $k$, the infinite sum of $\tfrac{1}{n(n+k)}$ over $n \ge 1$ has a closed
form: a finite rational, namely the $k$-th partial harmonic sum divided by $k$. The result
generalizes the classical Leibniz identity $\sum 1/(n(n+1)) = 1$ (which is the $k=1$ case,
since $H_1 = 1$) to arbitrary shifts.

### Why This Matters

- It is the natural one-parameter generalization of the Wiedijk-100 result
  `triangular-reciprocals` (the $k=1$ scaled version, sum $=2$).
- Provides the connection between partial-fraction telescoping and the harmonic numbers,
  exposing the digamma function as the analytic interpolation of $H_k$.
- The same finite-difference identity $H_{N+k} - H_N \to 0$ underlies many series
  evaluations in number theory and combinatorial analysis.

## Known Results

### What's Already Proven (in this gallery)

- `triangular-reciprocals` — $\sum_{n=1}^\infty 2/(n(n+1)) = 2$ (Wiedijk 42, fully verified).
- `triangular-reciprocals-oq-03` — alternating analogue (verified;
  `Proofs/TriangularReciprocalGeneralized.lean` despite the filename treats the
  *alternating* generalization, with `partial_fraction`, `generalized_alternating_sum`,
  `generalized_alternating_tsum`).
- `triangular-reciprocals-oq-01` — figurate-number reciprocal sums (in-progress sibling,
  `Proofs/TriangularReciprocalsFigurate.lean`).
- `harmonic-divergence` / `oq-01/oq-02/oq-04` — establish $H_n$ unbounded; not directly used
  here but supply the harmonic-sum infrastructure.

### What Mathlib Provides

- `Mathlib.NumberTheory.Harmonic.Defs.harmonic : ℕ → ℚ`
  `harmonic n = ∑ i ∈ Finset.range n, (↑(i+1))⁻¹` with `harmonic_succ`, `harmonic_eq_sum_Icc`.
- `Mathlib.NumberTheory.Harmonic.Bounds` — log bounds on $H_n$.
- `Mathlib.NumberTheory.Harmonic.GammaDeriv.deriv_Gamma_nat`:
  `deriv Real.Gamma (n+1) = n! * (-γ + harmonic n)` (David Loeffler, 2024).
  This gives `Real.Gamma.logDeriv (n+1) = -γ + harmonic n`, i.e. the digamma identity
  $\psi(n+1) = -\gamma + H_n$ in Mathlib form.
- `Mathlib.Analysis.SpecialFunctions.Gamma.Beta` — $\Gamma$ beta integral, useful if pivoting
  to integral representation.
- `Mathlib.Topology.Algebra.InfiniteSum.Basic.tsum`,
  `Mathlib.Analysis.PSeries.Real.summable_nat_rpow_inv` — convergence machinery already used
  by the base proof.

### What's Still Open in This Gallery

- A direct Lean proof of $\sum 1/(n(n+k)) = H_k/k$ for general $k$.
- The digamma reformulation $(\psi(k+1) + \gamma)/k$ as a corollary.

### Our Goal

Produce a Lean 4 file (provisional name `Proofs/TriangularReciprocalsHarmonic.lean` or
`TriangularReciprocalsOQ02.lean`) that:

1. Establishes the partial-fraction identity
   $\tfrac{1}{n(n+k)} = \tfrac{1}{k}\bigl(\tfrac{1}{n} - \tfrac{1}{n+k}\bigr)$ for
   $n, k \ge 1$.
2. Computes the partial sum $S_N(k) = \sum_{n=1}^{N} 1/(n(n+k))$ in closed form as
   $\tfrac{1}{k}(H_{N+k} - H_N - (-H_k))$, i.e.
   $S_N(k) = \tfrac{1}{k}\bigl(H_k - (H_{N+k} - H_N)\bigr)$.
3. Shows $H_{N+k} - H_N \to 0$ as $N \to \infty$.
4. Concludes $\sum_{n=1}^\infty 1/(n(n+k)) = H_k/k$ and packages summability + value.
5. Optionally derives the digamma reformulation via `Real.deriv_Gamma_nat`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `triangular-reciprocals` | $k=1$ scaled (sum $=2$) base case | partial fractions, telescoping, p-series comparison |
| `triangular-reciprocals-oq-03` | alternating analogue | `shifted_alternating_hasSum`, `partial_fraction` |
| `triangular-reciprocals-oq-01` | figurate reciprocal sums | sibling, in-progress |
| `harmonic-divergence` family | $H_n$ properties | log bounds, divergence |

## Initial Thoughts

### Potential Approaches

1. **Direct partial fractions + harmonic telescoping (recommended).**
   - Why it might work: the alternating sibling already has a `partial_fraction` lemma
     for $\tfrac{1}{n(n+k)}$; only the non-alternating telescoping and the tail
     estimate $H_{N+k} - H_N \to 0$ are needed. Both are routine.
   - Risk: managing the index shift between `Finset.range` and `Finset.Icc` sums and the
     ℚ↔ℝ cast (Mathlib's `harmonic` lives in ℚ; the `tsum` will need ℝ).

2. **Digamma route.**
   - Why it might work: $\sum 1/(n(n+k))$ is exactly $\psi(k+1) + \gamma$ over $k$ by a
     standard series for $\psi$.
   - Risk: Mathlib does not expose a `digamma` definition or a series formula. The Gamma
     derivative at integers is available (`deriv_Gamma_nat`), but the series identity
     $\psi(x+1) = -\gamma + \sum_{n=1}^\infty \tfrac{x}{n(n+x)}$ is not in Mathlib at this
     version. Heavy lift.

3. **Reduce to oq-03 (alternating) + auxiliary.**
   - Combine alternating and non-alternating sums to isolate either; algebraically clean
     but no obvious lift over the direct route.

### Key Difficulties

- ℚ/ℝ casting: `Mathlib.NumberTheory.Harmonic.harmonic` is rational; the `tsum` is real.
  Need `(harmonic n : ℝ) = ∑ i ∈ Finset.Icc 1 n, (↑i : ℝ)⁻¹` (likely a one-line `push_cast`).
- Index shift: partial sum runs $n \in [1, N]$ but telescoping gives sums over
  $[N+1, N+k]$; getting that into the right `Finset` form needs care.
- Tail decay: $0 \le H_{N+k} - H_N \le k/(N+1)$ — elementary, but needs the right Mathlib
  lemma name (likely a one-line `sum_le_card_nsmul`).

### What Would a Proof Need?

- **Lemma 1 (partial fraction)**: for $n,k \ge 1$,
  `(1 : ℝ)/(n*(n+k)) = (1/k) * (1/n - 1/(n+k))`. Field arithmetic.
- **Lemma 2 (partial sum closed form)**:
  `∑ n ∈ Finset.Icc 1 N, 1/(n*(n+k)) = (1/k) * ((harmonic k : ℝ) - ((harmonic (N+k) : ℝ) - (harmonic N : ℝ)))`.
  Reindex + cancel.
- **Lemma 3 (tail decay)**: `(harmonic (N+k) - harmonic N : ℝ) → 0` as $N \to \infty$
  (for fixed $k$). Bound by `k * (1/(N+1))`.
- **Lemma 4 (summability)**: comparison with $\sum 1/n^2$ via $1/(n(n+k)) \le 1/n^2$.
- **Main theorem**: `HasSum (fun n => 1/((n+1:ℝ)*((n+1)+k))) ((harmonic k : ℝ)/k)`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The base case ($k=1$) is solved in this gallery with the same technique.
- The alternating sibling oq-03 has the same partial-fraction lemma already (different sign).
- All Mathlib pieces exist; no missing infrastructure.

**Estimated Effort**:
- ORIENT (literature + sketch confirmation): 1–2 iterations.
- DECIDE (approach lock + file scaffold): 1 iteration.
- ACT (proof execution): 3–5 iterations, primarily Lemma 2 (reindex) and Lemma 3 (tail decay).
- Build/verify under Docker: 1 iteration.

## References

### Papers / Sources
- Gradshteyn & Ryzhik §0.234.2 — $\sum_{n=1}^\infty \frac{1}{n(n+k)} = \frac{H_k}{k}$.
- Abramowitz & Stegun §6.3.5 — digamma series $\psi(x+1) = -\gamma + \sum_{n=1}^\infty \frac{x}{n(n+x)}$.
- David Loeffler, *Derivative of Gamma at positive integers*, Mathlib `NumberTheory.Harmonic.GammaDeriv` (2024).

### Mathlib Modules
- `Mathlib.NumberTheory.Harmonic.Defs` — `harmonic`, `harmonic_succ`, `harmonic_eq_sum_Icc`.
- `Mathlib.NumberTheory.Harmonic.Bounds` — log bounds on $H_n$ (not needed but adjacent).
- `Mathlib.NumberTheory.Harmonic.GammaDeriv` — `Real.deriv_Gamma_nat`.
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `tsum`, `HasSum`.
- `Mathlib.Analysis.PSeries` — `summable_one_div_nat_pow`.

## Metadata

```yaml
tags:
  - analysis
  - series
  - special-functions
  - harmonic-numbers
  - telescoping
related_proofs:
  - triangular-reciprocals
  - triangular-reciprocals-oq-01
  - triangular-reciprocals-oq-03
  - harmonic-divergence
difficulty: medium
source: proof-suggestion
created: 2026-04-05T19:30:46-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
