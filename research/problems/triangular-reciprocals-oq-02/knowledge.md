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

## Decisions Locked in S3 (researcher-1, 2026-06-01)

### File and namespace
- **File**: `proofs/Proofs/TriangularReciprocalsOQ02.lean`.
- **Namespace**: `TriangularReciprocalsHarmonic`.
- **Companion**: `proofs/Proofs/TriangularReciprocalsOQ02Aristotle.lean` exposing
  Lemmas 1, 3, 4 (Lemma 2 stays in the main file because its proof is the substantive
  index manipulation, which Aristotle will not crack).

### Hypothesis convention
- `(k : ℕ) (hk : 0 < k)` — matches sibling
  `TriangularReciprocalGeneralized.lean` (`generalized_alternating_sum k hk`).

### Index convention
- Prove Lemma 2 over `Finset.Icc 1 N` (matches `harmonic_eq_sum_Icc`).
- Convert to `Finset.range` at the `HasSum` boundary using `hasSum_nat_add_iff 1` to
  drop the $n=0$ term — exactly the trick used at
  `TriangularReciprocalGeneralized.lean:124`.

### Casting recipe (ℚ → ℝ)
At each statement using `harmonic`, cast at the **statement** level: write
`(harmonic k : ℝ)`. Inside proofs, unfold via
```
simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
```
This is the canonical recipe at `NumberTheory/Harmonic/Bounds.lean:24` and `:31`.

### Lean Signatures (for S4 scaffold)

```lean
import Mathlib

namespace TriangularReciprocalsHarmonic

open Finset BigOperators Filter Topology Real

/-- Partial fraction decomposition. -/
theorem partial_fraction {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + k)) =
      (1 / k) * (1 / (n : ℝ) - 1 / ((n : ℝ) + k)) := by sorry

/-- Closed form for the N-th partial sum. -/
theorem partial_sum_closed_form (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + k)) =
      (1 / (k : ℝ)) *
        ((harmonic k : ℝ) - ((harmonic (N + k) : ℝ) - (harmonic N : ℝ))) := by sorry

/-- The shifted-harmonic tail $H_{N+k} - H_N$ tends to 0. -/
theorem tail_to_zero (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => ((harmonic (N + k) : ℝ) - (harmonic N : ℝ)))
      Filter.atTop (𝓝 0) := by sorry

/-- Summability of $1/(n(n+k))$ by comparison with $1/n^2$. -/
theorem summable_one_div_n_mul_n_add_k (k : ℕ) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ)
      else 1 / ((n : ℝ) * ((n : ℝ) + k))) := by sorry

/-- **Main theorem**: $\sum_{n=1}^\infty 1/(n(n+k)) = H_k/k$. -/
theorem triangular_reciprocals_harmonic (k : ℕ) (hk : 0 < k) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else 1 / ((n : ℝ) * ((n : ℝ) + k)))
      ((harmonic k : ℝ) / (k : ℝ)) := by sorry

end TriangularReciprocalsHarmonic
```

### Reindex sketch for Lemma 2 (the substantive lemma)

Working over ℝ, let $S_N(k) = \sum_{n \in \text{Icc } 1 N} \tfrac{1}{n(n+k)}$. Then:
1. Apply `partial_fraction` pointwise inside the sum, factor out $1/k$:
   $S_N(k) = (1/k) \cdot \bigl(\sum_{n \in \text{Icc } 1 N} 1/n -
                                \sum_{n \in \text{Icc } 1 N} 1/(n+k)\bigr)$.
2. First sum is $(H_N : \mathbb{R})$ by `harmonic_eq_sum_Icc` after the cast recipe.
3. Second sum: reindex $m = n+k$. As $n$ ranges over $\text{Icc } 1 N$, $m$ ranges over
   $\text{Icc } (k+1) (N+k)$. Tactically:
   ```
   rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) from Nat.Icc_succ_right_eq_Ico_succ ▸ rfl,
       Finset.sum_Ico_add' (fun (m : ℕ) ↦ (m : ℝ)⁻¹) 1 (N+1) (c := k)]
   -- now sum is over Ico (k+1) (N+k+1) of m⁻¹, i.e. Icc (k+1) (N+k) of m⁻¹.
   ```
4. Split $\text{Icc } (k+1) (N+k) = \text{Icc } 1 (N+k) \setminus \text{Icc } 1 k$ via
   `Finset.sum_Icc_consecutive` or `Finset.sum_Ioc_consecutive`. Result:
   $\sum_{\text{Icc } (k+1)(N+k)} 1/m = H_{N+k} - H_k$.
5. Combine: $S_N(k) = (1/k) \cdot (H_N - (H_{N+k} - H_k)) = (1/k) \cdot (H_k - (H_{N+k} - H_N))$.

The trickiest step is (3)/(4); both are mechanizable with `omega` for index bounds and
`Finset.sum_Ico_consecutive`. If `sum_Ico_add'` requires `range`-style indexing, fall
back to converting Icc ↔ Ico via `Finset.Icc_eq_Ico_add_one` (or whatever the v4.26.0
name is).

### Risk register for S4

- (low) Mathlib lemma name churn for the Icc ↔ Ico conversion. Mitigation: probe with
  `#check` in scaffold or `exact?` if a name fails.
- (low) `Finset.sum_Ico_add'` signature has subtle argument order; copy the call site
  from `harmonic_eq_sum_Icc` source verbatim.
- (medium) The ℝ-cast over harmonic differences may need `push_cast` rather than the
  explicit `Rat.cast_*` chain; both work but the explicit chain is more diagnostic.

## Open Questions for Next Iteration

1. Should `summable_one_div_n_mul_n_add_k` be stated as plain `Summable` (no $n=0$ guard)
   or with the `if n = 0` indicator (matching `HasSum` style in the sibling)?
   — Decision deferred to S4: write both and keep whichever simplifies the main theorem.
2. Does Aristotle close `partial_fraction` automatically given the `field_simp; ring`
   recipe is so short? — Test in S4: include in Aristotle companion.
