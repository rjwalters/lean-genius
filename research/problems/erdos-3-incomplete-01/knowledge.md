# Knowledge: erdos-3-incomplete-01

Erdős Problem #3 ($5000, OPEN): if `∑_{a∈A} 1/a = ∞` then `A` contains
arbitrarily long arithmetic progressions.

The claimed sorry is in `Proofs/Erdos3Problem.lean`:

```lean
theorem required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → RequiredBound k) → Erdos3Conjecture := sorry
```

where `RequiredBound k := ∀ c>0, ∀ᶠ N, rothNumber k N ≤ c·N/log N` (i.e.
`r_k(N) = o(N/log N)`) and `Erdos3Conjecture := ∀ A, HasDivergentSum A →
∀ k, ContainsAP A k`.

---

## FINDING: the sorry's threshold `o(N/log N)` is INSUFFICIENT for the reduction

The file frames this sorry as a mechanical "logical implication" and claims
(header, line 12) the conjecture is *equivalent* to `r_k(N) = o(N/log N)`. The
reverse direction actually written as the sorry is **not** provable by the
standard reciprocal-sum argument, because `o(N/log N)` is the wrong threshold.

**The intended proof.** Fix `k ≥ 3`, take `A` with `HasDivergentSum A`, and
suppose for contradiction `A` is AP-free of length `k` (`¬ContainsAP A k`). Then
every subset of `A ∩ [1,N]` is AP-free, so the counting function satisfies

```
f_A(N) := |A ∩ [1,N]|  ≤  rothNumber k N.
```

Under `RequiredBound k`, `rothNumber k N = o(N/log N)`, hence `f_A(N) = o(N/log N)`.
The proof wants to conclude `∑_{a∈A} 1/a < ∞`, contradicting `HasDivergentSum A`.

**Why it fails.** `f_A(N) = o(N/log N)` does **not** imply `∑ 1/a` converges.
By partial summation `∑_{a∈A} 1/a ≍ ∑_n f_A(n)/n²`. Take the borderline profile

```
f(N) ≍ N / (log N · log log N)      ( = o(N/log N),  since  ·/(N/log N) = 1/loglog N → 0 ),
```

for which

```
∑ f(n)/n²  ≍  ∫ dt / (t · log t · log log t)  =  log log log t → ∞.
```

So a set can have counting function `o(N/log N)` **and** divergent reciprocal
sum. Whether such a set can also be AP-free is *exactly* the negation of Erdős #3
(Behrend's AP-free sets have size `N/exp(c√log N)`, far below this, with
convergent reciprocal sum). Hence the sorry at the `o(N/log N)` threshold is **as
hard as Erdős #3 itself** — not a tractable logical step. Tractability rated 4/10
by the seeker is over-optimistic for the statement as written.

## CONSTRUCTIVE FIX: a genuinely provable reduction at the `(log N)^{1+ε}` threshold

Strengthen the hypothesis to the bound that actually powers the reciprocal-sum
argument. Add a new definition and theorem (leaving the original sorry as the
open, correctly-labelled hard reduction):

```lean
/-- The bound that suffices for the reciprocal-sum reduction:
    r_k(N) = O(N / (log N)^{1+ε}) for some ε > 0. -/
def StrongBound (k : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε)

theorem strong_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → StrongBound k) → Erdos3Conjecture
```

**Proof (dyadic blocking — avoids Abel summation and Bertrand series).** With `A`
AP-free of length `k`, `f_A(N) ≤ rothNumber k N ≤ C·N/(log N)^{1+ε}` for large `N`.
Decompose `A` into dyadic blocks `A ∩ (2^j, 2^{j+1}]`:

```
∑_{a∈A} 1/a  =  Σ_j  Σ_{a ∈ A∩(2^j,2^{j+1}]} 1/a
             ≤  Σ_j  |A ∩ (2^j,2^{j+1}]| / 2^j
             ≤  Σ_j  f_A(2^{j+1}) / 2^j
             ≤  Σ_j  C·2^{j+1} / ( ((j+1)·log 2)^{1+ε} · 2^j )
             =  (2C / (log 2)^{1+ε}) · Σ_j 1/(j+1)^{1+ε}   <  ∞,
```

the last sum being a convergent p-series (`p = 1+ε > 1`). So `∑ 1/a` converges,
contradicting `HasDivergentSum A`. ∎

This is a real 0-axiom conditional theorem: it isolates the *exact* analytic
strength the reduction needs, and makes explicit that the gap between it and
`o(N/log N)` is where Erdős #3's difficulty lives.

**Mathlib API (4.26.0):**
- p-series: `Real.summable_one_div_nat_rpow : Summable (fun n => 1/n^p) ↔ 1 < p`
  (or `Real.summable_nat_rpow_inv`); comparison `Summable.of_nonneg_of_le`.
- reindex reciprocal sum over `A` by dyadic blocks: `tsum` over the subtype `A`
  regrouped via `Set.Ioc (2^j) (2^(j+1))`; `ENNReal.tsum_biUnion` / `tsum_iUnion`
  or a `Finset`-exhaustion `HasSum` argument — the fiddly step.
- `Real.log_pow` / `Real.log_rpow`, `Real.rpow_natCast`, `Real.rpow_le_rpow`.
- small `k` (`k ≤ 2`): `ContainsAP A k` is trivial for a divergent-sum (hence
  infinite) `A`; only `k ≥ 3` needs `StrongBound`, matching the hypothesis's `k≥3`.

Estimated ~200–280 lines; the dyadic reindexing of the `tsum` is the main cost.

## What is BLOCKED

- The **original** sorry (`o(N/log N)` threshold): as hard as Erdős #3; do not
  attempt a direct proof. Best action is to (a) add the `StrongBound` reduction
  above, and (b) re-document the original as "open, threshold-critical," fixing
  the header's over-strong "equivalent to `o(N/log N)`" claim.
- Erdős #3 itself: open. Best known Roth-type bounds
  (Kelley–Meka 2023 `r_3(N) ≪ N/exp((log N)^{1/11})`, Leng–Sah–Sawhney 2024) are
  far from even `o(N/log N)`, let alone `O(N/(log N)^{1+ε})` — the file header's
  results list is accurate on this point.

## Existing file inventory (`Proofs/Erdos3Problem.lean`, 163 lines)

- Defs: `ArithProg`, `ContainsAP`, `IsAPFree`, `reciprocalSum`, `HasDivergentSum`,
  `rothNumber`, `countingFunction`, `SublogarithmicGrowth`, `Erdos3Conjecture`,
  `RequiredBound`.
- `euler_prime_sum_diverges` (axiom), `erdos3_implies_green_tao` (proved),
  `erdos_3_open` (trivial `em`).
- Sorry count: 1 (`required_bound_implies_conjecture`).

## Status

PARTIAL / IN-PROGRESS. Delivered: (1) a correctness FINDING — the current sorry's
`o(N/log N)` threshold is insufficient (Abel-summation counterexample) and the
statement as written is as hard as Erdős #3; (2) a fully designed, 0-axiom
provable replacement `strong_bound_implies_conjecture` at the `(log N)^{1+ε}`
threshold via dyadic blocking + p-series, with exact Mathlib API. Verification
deferred this iteration: no Mathlib olean cache in the environment and disk at
99%, so no `import Mathlib` build could be run (see state.md).
