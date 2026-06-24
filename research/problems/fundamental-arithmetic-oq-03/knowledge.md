# Knowledge Base: fundamental-arithmetic-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

This problem is the parent FTA entry's **third open question**: formalize the
Euler product ζ(s) = ∏ₚ(1-p⁻ˢ)⁻¹ as a consequence of the Fundamental Theorem of
Arithmetic. Mathlib already supplies the general Euler product
(`riemannZeta_eulerProduct_tprod`), whose proof IS unique factorization (the engine
`EulerProduct.eulerProduct_completely_multiplicative` matches partial products over
p-smooth numbers with partial sums). A bare re-export of that lemma would be
low-value, so the entry instead records the historically decisive **consequence**
that Mathlib does not state: combining the Euler product with the closed-form
special values ζ(2)=π²/6 and ζ(4)=π⁴/90 to recover Euler's 1737 prime-product
evaluations.

---

## Insights

- The Euler product is the analytic incarnation of the FTA. Expanding each factor
  (1-p⁻ˢ)⁻¹ = 1 + p⁻ˢ + p⁻²ˢ + ⋯ and multiplying over primes reproduces ∑ₙ n⁻ˢ
  because every n factors uniquely.
- Once the convergence hypothesis 1 < Re s is supplied (trivial: `by norm_num`),
  the famous special-value products reduce to a single `rw` chaining
  `riemannZeta_eulerProduct_tprod` with `riemannZeta_two` / `riemannZeta_four`.
- Three forms shipped: `tprod` (unordered product), `HasProd` (order-independent
  convergence), and a `Tendsto` over `Nat.primesBelow n` (Euler's finite sieve).
- Non-vanishing of π²/6 and π⁴/90 is free via `riemannZeta_ne_zero_of_one_lt_re`
  (a convergent product of nonzero factors is nonzero).

---

## Dead Ends

- **GOTCHA (not a dead end, a fix):** with only `open Complex`, the `π` notation is
  not in scope, so Lean auto-bound `π` as a *free complex variable* and every
  rewrite against Mathlib's `↑Real.pi` failed (`↑Real.pi ^ 2 / 6 = π ^ 2 / 6`
  unsolved). Adding `open Real` makes `π = Real.pi`, so `(π : ℂ)` elaborates to the
  same `↑Real.pi` Mathlib uses and the rewrites close by `rfl`.
