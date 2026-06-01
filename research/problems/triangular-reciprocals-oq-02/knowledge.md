# Knowledge Base: triangular-reciprocals-oq-02

Insights accumulated during research on $\sum_{n=1}^\infty \frac{1}{n(n+k)} = \frac{H_k}{k}$.

---

## Problem Understanding

The identity is the natural $k$-shift generalization of the Wiedijk-100 Leibniz sum
$\sum 1/(n(n+1)) = 1$. The closed form is rational (a finite harmonic sum divided by $k$),
which makes the result mechanizable without leaving ℚ until the final ℝ-cast for `tsum`.

The same identity has an analytic reading via the digamma function:
$\psi(x+1) = -\gamma + \sum_{n=1}^\infty \frac{x}{n(n+x)}$. Specializing $x=k$ gives
$\psi(k+1) + \gamma = \sum_{n=1}^\infty \frac{k}{n(n+k)} = k \cdot \frac{H_k}{k} = H_k$,
which matches Mathlib's $\Gamma'(n+1) = n!(-\gamma + H_n)$ (`deriv_Gamma_nat`,
`NumberTheory/Harmonic/GammaDeriv.lean`, David Loeffler 2024).

---

## Insights (S2, 2026-06-01)

### Mathlib API map

- `harmonic : ℕ → ℚ := fun n => ∑ i ∈ Finset.range n, (↑(i+1))⁻¹` — `NumberTheory.Harmonic.Defs`.
  - `harmonic_zero : harmonic 0 = 0`.
  - `harmonic_succ n : harmonic (n+1) = harmonic n + (↑(n+1))⁻¹`.
  - `harmonic_eq_sum_Icc : harmonic n = ∑ i ∈ Finset.Icc 1 n, (↑i)⁻¹`.
- `Real.deriv_Gamma_nat n : deriv Real.Gamma (n+1) = n! * (-γ + harmonic n)` — gives the
  digamma corollary once the main identity is in place.
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `tsum`, `HasSum`, `Summable`.
- `Mathlib.Analysis.PSeries.summable_one_div_nat_pow` — p-series for the dominating
  comparison $1/(n(n+k)) \le 1/n^2$.

### Sibling proof reuse

`Proofs/TriangularReciprocalGeneralized.lean` (gallery slug `triangular-reciprocals-oq-03`,
*alternating* generalization) has a `partial_fraction` lemma at line 133:

```
theorem partial_fraction {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
  (1 : ℝ)/((n : ℝ) * ((n : ℝ) + k)) = (1/k) * ((1/n) - (1/((n : ℝ)+k)))
```

This is **identical** to the partial fraction we need (the alternating sign appears at the
sum level, not the lemma). We can lift this verbatim or restate.

### Telescoping closed form (sketch)

Reindex: $\sum_{n=1}^{N} \tfrac{1}{n} - \tfrac{1}{n+k} =
\sum_{n=1}^{N} \tfrac{1}{n} - \sum_{m=k+1}^{N+k} \tfrac{1}{m}
= H_N - (H_{N+k} - H_k) = H_k - (H_{N+k} - H_N)$.

So $\sum_{n=1}^{N} \tfrac{1}{n(n+k)} = \tfrac{1}{k}\bigl(H_k - (H_{N+k} - H_N)\bigr)$.

### Tail bound

For $k \ge 1$: $0 \le H_{N+k} - H_N = \sum_{j=N+1}^{N+k} \tfrac{1}{j} \le \tfrac{k}{N+1}$.
Hence $H_{N+k} - H_N \to 0$ as $N \to \infty$. Taking the limit in the partial sum gives
$\sum_{n=1}^\infty \tfrac{1}{n(n+k)} = H_k/k$.

### Summability

$\tfrac{1}{n(n+k)} \le \tfrac{1}{n^2}$ for $n \ge 1$, $k \ge 0$ (since $n+k \ge n$). The
RHS is summable by the p-series with $p=2 > 1$, so the original series converges absolutely
by direct comparison. This justifies passing from `HasSum` of partial sums to `tsum =`.

### ℚ ↔ ℝ casting

Because Mathlib's `harmonic` is ℚ-valued, the `tsum` in ℝ requires casting at the
boundary. Standard `push_cast` / `Rat.cast_sum`+`Rat.cast_inv`+`Rat.cast_natCast` chain
(as used in `NumberTheory.Harmonic.Bounds` lines 24, 31). This is a one-liner per
harmonic reference, not a structural obstacle.

---

## Dead Ends

### Pure digamma route

Trying to prove the identity by first proving the digamma series expansion
$\psi(x+1) = -\gamma + \sum \tfrac{x}{n(n+x)}$ requires significant analytic machinery
(uniform convergence of the series, comparison with $\Gamma'$). Mathlib has the integer-
case derivative `deriv_Gamma_nat` but not the series identity. Pursuing this would
require a long detour into special functions. **Parked**: derive as a corollary of
the partial-fraction main result instead, once the latter is proved.

---

## Open Questions for Next Iteration

1. Exact form for the main theorem signature — `HasSum` vs `tsum =` vs both?
   (Mathlib idiom: prove `HasSum` first, derive `tsum` via `HasSum.tsum_eq`.)
2. Should the result be stated for `k : ℕ, hk : 0 < k` or `k : ℕ+`?
   (Lean idiom and sibling files prefer `k : ℕ, hk : k ≠ 0` or `hk : 0 < k` —
   `triangular-reciprocals-oq-03` uses `hk : 0 < k`.)
3. Index convention for the sum — `Finset.range` (0-indexed, shift) vs `Finset.Icc 1 N`
   (1-indexed, natural)?
   (Mathlib's `harmonic` is `range`-defined but `harmonic_eq_sum_Icc` gives both views.)
