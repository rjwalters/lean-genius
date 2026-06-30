# Knowledge Base: lovasz-local-lemma-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

- The research-pool *title* "Finite Symmetric Thresholds" is a misnomer: that
  rational/combinatorial surrogate is already fully complete in
  `Proofs/LovaszLocalLemma.lean` (0 sorries, 0 axioms). The authoritative goal
  (problem.md) is the **measure-theoretic** probabilistic LLL, which is still
  open and research-grade.
- `lllThreshold d = dᵈ/(d+1)^{d+1}` is the exact maximum of `x(1-x)ᵈ` over
  `x ∈ [0,1)`, attained at `x = 1/(d+1)`. It equals `(1/(d+1))·(d/(d+1))ᵈ`
  (`lllThreshold_eq_product`).

---

## Insights

- **Threshold monotonicity** `T(d+1) ≤ T(d)` (and the chain `T(d) ≤ T(c)` for
  `1 ≤ c ≤ d`) holds and is now formalized. It subsumes the universal bound
  `T(d) ≤ 1/4` because `T(1) = 1/4`.
- Monotonicity reduces (after cross-multiplication) to the elementary
  polynomial inequality `(a+1)^{2d+2} ≤ aᵈ(a+2)^{d+2}`, which yields to a single
  application of Bernoulli `(1-1/(a+1)²)ᵈ ≥ 1 - d/(a+1)²` plus the residual
  `(a²+a+1)(a+2)² ≥ (a+1)⁴` (difference `a³+3a²+4a+3`). No real analysis / `exp`
  needed — stays entirely in ℚ.
- Reusable Lean pattern: to clear an `xᵈ`-power inequality of the form
  `c ≤ (p/q)ᵈ`, rewrite with `div_pow` then `le_div_iff₀ (0 < qᵈ)`, multiply
  through by the residual denominator with `mul_le_mul_of_nonneg_right`, and
  hand the opaque `pᵈ`, `qᵈ` factors to `nlinarith` as atoms.
- `div_le_div_iff` is gone in this Mathlib; use **`div_le_div_iff₀`**
  `(hb : 0<b) (hd : 0<d) : a/b ≤ c/d ↔ a*d ≤ c*b`. Likewise `le_div_iff` →
  `le_div_iff₀`.

---

## Dead Ends

- Trying to prove `(a+1)^{2d+2} ≤ aᵈ(a+2)^{d+2}` term-by-term fails: the
  base-power factor `((a+1)²)ᵈ ≥ (a(a+2))ᵈ` points the *wrong* way; the
  `(a+2)²` vs `(a+1)²` factor is what compensates, so the Bernoulli/ratio
  argument is required rather than monotonicity of `xⁿ`.
- The measure-theoretic LLL is NOT a quick increment: Mathlib supplies
  `iIndepSet`, `ProbabilityMeasure`, `cond`, but no LLL, and a real proof spans
  multiple sessions.
