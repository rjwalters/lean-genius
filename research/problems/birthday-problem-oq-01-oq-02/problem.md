# Problem: Coupling between expected pairs and collision probability

**Slug**: `birthday-problem-oq-01-oq-02`
**Parent**: `birthday-problem-oq-01` (Expected Number of Shared Birthday Pairs, verified, 0 sorries / 0 axioms)
**Sibling proofs**: `birthday-problem-oq-01-oq-01` (collision-count distribution), `birthday-problem-oq-02` (tight collision asymptotics)

## Plain Statement

Two quantitative measures of "how likely is a birthday collision among `n` people choosing from `d` equally-likely birthdays" appear in the gallery:

1. **Expected shared-pair count** (parent `birthday-problem-oq-01`):
   ```
   expectedPairs n d = (Nat.choose n 2 : ℚ) / (d : ℚ) = n(n-1) / (2d)
   ```
   A purely *first-moment* quantity computed by linearity of expectation
   over the C(n,2) pair-indicators `I_{f(i)=f(j)}`, each Bernoulli(1/d).

2. **Collision probability** (sibling `birthday-problem-oq-02`):
   ```
   probCollision k d = 1 - probAllDistinct k d
                     = 1 - ∏_{i=0}^{k-1} (1 - i/d)
   ```
   The actual probability that at least one pair shares a birthday under
   the uniform model. Already bounded above by the exponential approximation
   `1 - exp(-k(k-1)/(2d))` (`probCollision_ge`, `BirthdayProblemOQ02.lean:175–181`).

**The open question** is to formalise the **direct Markov coupling**
between these two quantities, plus its second-moment lower-bound companion:

```
(MARKOV)            probCollision n d ≤ ↑(expectedPairs n d)
(PALEY-ZYGMUND)     probCollision n d ≥ (expectedPairs n d)² / E[X²]
```

where `E[X²]` is the second moment of the shared-pair count
`X(f) = collisionCount f` (defined in
`BirthdayProblemOQ01OQ01.lean:50–58`).

## Why this Matters

1. **Closes a methodology gap.** The gallery contains both moment-based
   (`OQ01`: `expectedPairs`, `variancePairs`) and probability-based
   (`OQ02`: `probCollision`) treatments of the birthday problem, but no
   formal proof that the two viewpoints **bracket the same quantity**.
   The Markov bound is the natural one-line bridge.
2. **First-moment ↔ second-moment coupling.** Formalising both Markov
   (uses `E[X]`) and Paley-Zygmund (uses `E[X²]`) exercises the variance
   bound `variancePairs_le_expected` (`OQ01:164`) — the latter sits unused
   in the gallery without a coupling theorem to give it a downstream
   client.
3. **Companion to the exponential bound.** The OQ02 exponential bound
   `probCollision ≥ 1 - exp(-k(k-1)/(2d))` and this coupling's Markov
   bound `probCollision ≤ k(k-1)/(2d)` together sandwich `probCollision`
   between two closed forms — neither implies the other in general
   (different regimes: Markov is sharpest at small `k(k-1)/d`, exponential
   bound is sharpest near the threshold).
4. **Mathlib gap.** The first-moment / second-moment Markov / Paley-Zygmund
   bounds are well-known but, at the pinned Mathlib revision, are not
   stated for *deterministic* (finite-sample-space) random variables in a
   form that mirrors the explicit `probAllDistinct` product. A
   gallery-side formalisation has standalone teaching value and may
   propagate upstream.

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4) | Module |
|------|----------------------|--------|
| Finset product `∏ i ∈ range n, f i` | `Finset.prod_range_succ` | `Mathlib.Algebra.BigOperators.Group.Finset` |
| Finset sum `∑ i ∈ range n, f i` | `Finset.sum_range_succ` | `Mathlib.Algebra.BigOperators.Group.Finset` |
| `(1 - a)(1 - b) ≥ 1 - a - b` | `mul_self_nonneg` + `nlinarith` | (algebra) |
| `Finset.one_sub_prod_le_sum` (union bound) | **not in Mathlib at pin** | (gap; provable by induction) |
| `Finset.card_filter_le` | `Finset.card_filter` family | `Mathlib.Data.Finset.Card` |
| `Real.exp` and `add_one_le_exp` | `Real.add_one_le_exp` | `Mathlib.Analysis.SpecialFunctions.Exp` |
| Markov inequality (measure-theoretic) | `MeasureTheory.measure_inv_le_inv_mul_lintegral_of_*` family | `Mathlib.MeasureTheory.Function.LpSpace.*` |
| Rat → Real cast | `Rat.cast`, `Nat.cast_div_le`, `pushcast` tactic | `Mathlib.Data.Rat.Cast.Defs` |
| Variance ≤ E[X] | `variancePairs_le_expected` | `BirthdayProblemOQ01:164–172` |
| Gauss sum `∑ i/d = k(k-1)/(2d)` | `gauss_sum_div` | `BirthdayProblemOQ02:145–150` |
| collisionCount `X(f)` random variable | `collisionCount`, `collisionCount_eq_zero_iff_injective` | `BirthdayProblemOQ01OQ01:50–58` |
| `descFactorial(d,n)` for # injective | (`Fintype.card_embedding_eq`) | `Mathlib.Data.Fintype.Pi` |

### Existing in-gallery infrastructure (no Mathlib search needed)

- `expectedPairs n d : ℚ` and `expectedPairs_eq_rational : 2*d*expectedPairs n d = n*(n-1)` (`OQ01:138`).
- `variancePairs n d : ℚ` and `variancePairs_le_expected` (`OQ01:164`).
- `probAllDistinct k d : ℝ` and `probCollision k d : ℝ = 1 - probAllDistinct k d` (`OQ02:67–73`).
- `gauss_sum_div k d : ∑ i ∈ range k, (i:ℝ)/d = k*(k-1)/(2*d)` (`OQ02:145`).
- `probAllDistinct_le_exp` and `probCollision_ge` (`OQ02:158–181`).
- `collisionCount : (Fin n → Fin d) → ℕ` and `collisionCount_eq_zero_iff_injective` (`OQ01OQ01:50–60`).

## Suggested Next-Action Decomposition

S1 (this iteration) is **OBSERVE** — no Lean changes, only the
problem statement, infrastructure map, and S2+ decomposition below.

### S2 — Generic union bound for products

State and prove the standalone lemma

```lean
theorem one_sub_prod_le_sum {n : ℕ} (f : ℕ → ℝ)
    (hnn : ∀ i, i < n → 0 ≤ f i) (hle : ∀ i, i < n → f i ≤ 1) :
    1 - ∏ i ∈ Finset.range n, (1 - f i) ≤ ∑ i ∈ Finset.range n, f i
```

in a new file `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`. Proof by
induction on `n` (~25 lines):

- **Base `n = 0`**: `1 - ∏ ∅ (...) = 1 - 1 = 0 ≤ 0 = ∑ ∅ (...)`. `simp`.
- **Step**: with `a := f n` and `P := ∏ i ∈ range n, (1 - f i)`,
  `1 - (1 - a) · P = a + (1 - a) · (1 - P)`.
  Both `(1 - a) ∈ [0, 1]` and `(1 - P) ∈ [0, 1]` (chain of inductive
  positivity), so `(1 - a) · (1 - P) ≤ 1 - P`, giving
  `1 - (1 - a) · P ≤ a + (1 - P) ≤ a + ∑ rest = ∑ all`.

### S3 — Specialisation to birthday product (the Markov bound)

```lean
theorem probCollision_le_expectedPairs (n d : ℕ) (hd : 0 < d) :
    probCollision n d ≤ ((expectedPairs n d : ℚ) : ℝ) := by
  unfold probCollision probAllDistinct expectedPairs
  -- 1 - ∏(1 - i/d) ≤ ∑ i/d  by `one_sub_prod_le_sum`
  -- ∑ i/d = n(n-1)/(2d)      by `gauss_sum_div`
  -- n(n-1)/(2d) = C(n,2)/d  by `two_mul_choose_two` (rearranged)
  sorry
```

Chains S2's union bound with `gauss_sum_div` (OQ02) and
`two_mul_choose_two : 2 * n.choose 2 = n * (n - 1)` (OQ01:109).
~40 lines once the casts are stabilised (`Rat.cast`, `pushcast`).

### S4 — Variance / second-moment computation

Compute `E[X²] = Var(X) + E[X]²` formally in OQ01-OQ02 style:

```lean
theorem expectedPairs_sq_le_expected_add_expected_sq (n d : ℕ) (hd : 1 ≤ d) :
    ((expectedPairs n d : ℚ) : ℝ) ^ 2
      ≤ ((variancePairs n d + expectedPairs n d ^ 2 : ℚ) : ℝ)
```

(equality is provable but inequality is what feeds Paley-Zygmund).
Direct algebraic rearrangement using `variancePairs n d ≥ 0`
(provable from `OQ01.variancePairs_nonneg`).

### S5 — Paley-Zygmund lower bound

```lean
theorem probCollision_ge_paley_zygmund (n d : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    probCollision n d ≥
      (((expectedPairs n d : ℚ) : ℝ) ^ 2) /
      (((variancePairs n d + expectedPairs n d ^ 2 : ℚ) : ℝ))
```

Uses the discrete Paley-Zygmund identity
`E[X]² ≤ E[X · 1_{X ≥ 1}] · P(X ≥ 1)` (Cauchy-Schwarz),
then `E[X · 1_{X ≥ 1}] ≤ E[X²]^{1/2} · P(X ≥ 1)^{1/2}` etc.
Substantially heavier (~80 lines) because it requires bridging
`probAllDistinct` (OQ02 product formulation) and `collisionCount` /
`Fintype.card` (OQ01OQ01 finite-sample-space formulation).

### S6 — Bridge between OQ02 product and OQ01OQ01 counting

Standalone helper:

```lean
theorem probAllDistinct_eq_descFactorial_div (n d : ℕ) (hd : 0 < d) :
    probAllDistinct n d
      = (Nat.descFactorial d n : ℝ) / ((d : ℝ) ^ n)
```

i.e. `∏_{i=0}^{n-1}(1 - i/d) = d!/((d-n)! · d^n)`. Both formulations
should be PROVED equal so that the Markov bound (S3) and the
Paley-Zygmund bound (S5) can speak to a common P(collision).
~30 lines: telescoping the product `∏(1 - i/d) = ∏(d - i)/d` and
identifying with `descFactorial`.

S6 can be done **before** S5 to give the latter a clean foundation.

## Risk Notes

- The `proofs/.lake` symlink in researcher worktrees is broken
  (`feedback_researcher_lake_symlink_broken.md`); each Docker build
  costs ~25–45 minutes of fresh Mathlib clone. S2 is short enough
  that an end-of-S2 Docker build is feasible; S5 may need to be
  split into multiple sessions.
- No axioms required. `status` will be `verified` once all sorries
  close.
- The `Rat.cast` / `Real.cast` chain can produce surprising elaboration
  delays. Pre-emptively use `push_cast` / `norm_cast` between coupling
  steps.
- Paley-Zygmund in S5 requires bridging the product (OQ02) and counting
  (OQ01OQ01) formulations of `probCollision`. The bridge S6 is the
  key prerequisite.

## References

- Markov's inequality: standard probability text (e.g.
  Grimmett & Stirzaker §3.6).
- Paley–Zygmund inequality: Kahane (1985) *Some Random Series of
  Functions*, Theorem 6.1.
- Birthday problem second moment: covered in Mitzenmacher & Upfal
  *Probability and Computing* §3.3.
- Union bound: any introductory probability text;
  Bonferroni's inequality of order 1.
