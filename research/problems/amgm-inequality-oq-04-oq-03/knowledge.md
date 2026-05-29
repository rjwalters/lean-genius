# Knowledge Base: amgm-inequality-oq-04-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Target: Gauss's AGM theorem M(a,b) = a·π/(2·K(k')), k = b/a, k' = √(1−k²), via the
hypergeometric representation of the complete elliptic integral of the first kind:

  K(k) = (π/2)·₂F₁(1/2, 1/2; 1; k²) = (π/2)·∑_{n≥0} cₙ k^{2n}.

`K` is already defined rigorously (interval integral) in the companion file
`AmgmInequalityOQ04OQ01.lean`, where the AGM↔K connection is itself an axiom.

---

## Insights

- The series coefficient is cₙ = ((1/2)_n / n!)² = (centralBinom n / 4ⁿ)², using the
  identity (1/2)_n / n! = (2n choose n)/4ⁿ.
- Classical expansion: K(k) = (π/2)[1 + (1/2)²k² + (1·3/(2·4))²k⁴ + ⋯]; so c₀ = 1 and
  c₁ = (1/2)² = 1/4. Both verified in Lean (`hypCoeff_zero`, `hypCoeff_one`).
- Proof route for the full identity: binomial series (1−u)^(−1/2) = ∑ (centralBinom n/4ⁿ) uⁿ,
  substitute u = k² sin²θ, integrate term by term over [0, π/2], and use the Wallis integral
  ∫₀^{π/2} sin^{2n}θ dθ = (π/2)(2n choose n)/4ⁿ.
- The k = 0 case is provable WITHOUT the deep identity: K(0) = π/2 (`ellipticK_zero`) and
  ₂F₁(…;0) = 1 (`hyp2F1_zero`), so both sides equal π/2
  (`ellipticK_hyp2F1_consistent_zero`). This anchors the axiom's correctness at k = 0.

## Built (this session, Proofs/AmgmInequalityOQ04OQ03.lean — builds clean, 0 sorries, 1 axiom)

- `hypCoeff`, `hyp2F1` definitions (central-binomial series).
- `hypCoeff_zero` (=1), `hypCoeff_one` (=1/4), `hypCoeff_nonneg`, `hypCoeff_pos`.
- `hyp2F1_zero` : ₂F₁(…;0) = 1 (via `tsum_eq_single`).
- `ellipticK_hyp2F1_consistent_zero` : K(0) = (π/2)·₂F₁(…;0), independent of the axiom.
- `ellipticK_eq_hyp2F1` (axiom) : K(k) = (π/2)·₂F₁(1/2,1/2;1;k²) for |k|<1.

---

## Dead Ends / Blockers

- No general Gauss hypergeometric ₂F₁ in Mathlib.
- No off-the-shelf term-by-term integration lemma matching K; the sum/integral interchange
  (dominated convergence, delicate as k → 1) is the genuine obstacle to discharging the axiom.
- Wallis closed form ∫₀^{π/2} sin^{2n} = (π/2)(2n choose n)/4ⁿ must be assembled from
  Mathlib's `integral_sin_pow` recurrences (not packaged directly).
