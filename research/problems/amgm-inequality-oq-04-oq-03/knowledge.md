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
- **Wallis half-period structural fact (S3)**: Mathlib's `integral_sin_pow_even`
  and `Real.Wallis.W` cover [0, π], not [0, π/2]. The half-period closed form
  is NOT packaged directly. Fix: apply the reduction `integral_sin_pow` (a, b
  parameterised) at a=0, b=π/2 — both boundary terms `sin a^(n+1)·cos a` and
  `sin b^(n+1)·cos b` vanish (`sin 0 = 0`, `cos(π/2) = 0`), yielding the
  clean recurrence W(n+2) = ((n+1)/(n+2)) · W(n).
- **Central binomial recurrence threading**: closed form
  W(2n) = (π/2)·centralBinom n / 4^n proved by induction using
  `Nat.succ_mul_centralBinom_succ`:
  `(n+1) · centralBinom (n+1) = 2 · (2n+1) · centralBinom n`. After casting to
  ℝ and substituting centralBinom(k+1) = 2(2k+1)·centralBinom(k) / (k+1),
  `field_simp; ring` closes the algebraic step cleanly.

## Built (across sessions, Proofs/AmgmInequalityOQ04OQ03*.lean — builds clean, 0 sorries)

In `Proofs/AmgmInequalityOQ04OQ03.lean` (S1, merged):
- `hypCoeff`, `hyp2F1` definitions (central-binomial series).
- `hypCoeff_zero` (=1), `hypCoeff_one` (=1/4), `hypCoeff_nonneg`, `hypCoeff_pos`.
- `hyp2F1_zero` : ₂F₁(…;0) = 1 (via `tsum_eq_single`).
- `ellipticK_hyp2F1_consistent_zero` : K(0) = (π/2)·₂F₁(…;0), independent of the axiom.
- `ellipticK_eq_hyp2F1` (axiom) : K(k) = (π/2)·₂F₁(1/2,1/2;1;k²) for |k|<1.

In `Proofs/AmgmInequalityOQ04OQ03.lean` summability section (S2, PR #22021 open mergeable):
- `centralBinom_le_four_pow` : Nat.centralBinom n ≤ 4^n (upper-bound gap in v4.26.0).
- `hypCoeff_le_one` : hypCoeff n ≤ 1 (direct corollary).
- `summable_hyp2F1` : Summable (fun n => hypCoeff n · x^n) for |x| < 1 (comparison
  with geometric).

In `Proofs/AmgmInequalityOQ04OQ03Wallis.lean` (S3 ACT, this session, additive companion):
- `wallisHalf n := ∫ θ in 0..π/2, sin θ ^ n` (definition).
- `wallisHalf_zero` : W(0) = π/2.
- `wallisHalf_recurrence` : W(n+2) = ((n+1)/(n+2)) · W(n) (half-period reduction).
- `wallisHalf_even` : W(2n) = (π/2) · centralBinom n / 4^n (main Wallis closed form).

---

## Dead Ends / Blockers

- No general Gauss hypergeometric ₂F₁ in Mathlib.
- No off-the-shelf term-by-term integration lemma matching K; the sum/integral interchange
  (dominated convergence, delicate as k → 1) is the genuine obstacle to discharging the axiom.
- Mathlib's `integral_sin_pow_even` and `Real.Wallis.W` are over the full period [0, π]; the
  half-period closed form needed for the elliptic substitution u = k² sin²θ over [0, π/2]
  must be derived from the reduction formula directly. The S3 companion now ships this leg.

---

## Leg-by-leg axiom discharge plan

To prove `ellipticK_eq_hyp2F1 : K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)`:

1. ✅ **Summability** (S2, `summable_hyp2F1` in PR #22021): the series ∑ cₙ x^n
   converges for |x|<1.
2. ✅ **Wallis closed form** (S3, `wallisHalf_even`, this session): the half-period
   integral ∫₀^{π/2} sin^{2n}θ dθ has the explicit central-binomial value.
3. ⏳ **Binomial series**: (1−u)^(−1/2) = ∑ (centralBinom n / 4ⁿ) uⁿ for |u|<1.
4. ⏳ **Uniform summability**: on compact k-subsets of (−1, 1), the series
   ∑ cₙ k^{2n} sin^{2n}θ is dominated and uniformly summable in θ.
5. ⏳ **Sum/integral interchange**: DCT-style argument combining 3, 4 to compute
   K(k) term by term, then close using 2 and 1.

The companion files in `Proofs/AmgmInequalityOQ04OQ03*.lean` are built so that legs
can ship independently without rebasing on each other; the final composition step
(leg 5) integrates them once leg 3 lands.
