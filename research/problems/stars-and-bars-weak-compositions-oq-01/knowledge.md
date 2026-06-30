# Knowledge Base: stars-and-bars-weak-compositions-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

- The GF view `W k = ∑ₙ #{f : Fin k → ℕ // ∑ f = n}·Xⁿ = 1/(1−X)ᵏ` (OQ-01) is the
  natural home for *structural* follow-ups, because Mathlib's `invOneSubPow` carries
  the full units-group API (`invOneSubPow_zero`, `invOneSubPow_add`). Any
  multiplicative identity on the counts is a one-liner once `W` is identified with
  `(invOneSubPow S k).val`.
- **OQ-04 (2026-06-30, PR #31639, VERIFIED 0-axiom):** added the convolution layer.
  - `weakCompositionGenFun_zero`: `W(0) = 1` (closes OQ-01's `0 < k` boundary; the
    unique `Fin 0 → ℕ` sums to 0, so only the constant coefficient survives — via
    parent `card_weakComposition` + `Nat.choose_eq_zero_of_lt`).
  - `weakCompositionGenFun_eq_invOneSubPow_val`: bridge for **all** k (zero/pos split).
  - `weakCompositionGenFun_mul`: `W(k₁)·W(k₂) = W(k₁+k₂)` — image under `(·).val` of
    `invOneSubPow_add`; no tuple bijection needed.
  - `vandermonde_negBinomial`: `∑_{i+j=n} C(i+k₁−1,i)·C(j+k₂−1,j) = C(n+k₁+k₂−1,n)`,
    extracted as the n-th `PowerSeries.coeff_mul` coefficient over ℤ and dropped to ℕ
    by `exact_mod_cast`. Stated without positivity (holds at k=0 where C(·−1,·) is the
    indicator of 0).
  - Technique worth reusing: to get a ℕ binomial-convolution identity, prove the GF
    identity, take `congrArg (coeff n)`, `simp [coeff_mul, <coeff-of-W>]`, then
    `exact_mod_cast` — avoids all truncated-ℕ-subtraction bookkeeping inside binomials.

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
