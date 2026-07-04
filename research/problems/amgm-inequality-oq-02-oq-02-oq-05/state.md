# Research State: amgm-inequality-oq-02-oq-02-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 3 (PART II)

## Current Focus
Extended the real-rooted/discriminant route to the first nontrivial arity `n = 3`
(both log-concavity steps), building on the PART-I `n = 2` base case. Five new
theorems in `Proofs/AmgmInequalityOQ02OQ02OQ05.lean`, 0 sorries, 0 axioms
(docker-build clean, 7743 jobs; Tier-A axiom-free):
- `newton_three_first : 3(xy+yz+zx) ≤ (x+y+z)²`  (`e₁² ≥ 3e₂`, the first Newton
  step at n=3), for SIGNED reals, SOS `½Σ(x−y)²`.
- `newton_three_second : 3(x+y+z)·xyz ≤ (xy+yz+zx)²`  (`e₂² ≥ 3e₁e₃`, the second
  Newton step), SOS `½Σ(xy−yz)²`.
- `discrim_deriv_cubic_first` / `discrim_recip_deriv_cubic_second`: the same two
  facts as the nonnegative discriminants of the derivative quadratic
  `P' = 3X²−2e₁X+e₂` and the reciprocal-derivative quadratic `−3e₃X²+2e₂X−e₁` —
  the `n = 3` instance of "a derivative of a real-rooted polynomial is
  real-rooted (discriminant ≥ 0)".
- `newton_three_normalized`: both steps in normalized `p`-mean form.

The `n = 3` discriminants are proved *directly* by SOS — which IS the
real-rootedness of those quadratics — so this arity needs neither the general
Rolle-iteration crux nor any sign hypothesis. Rolle is the motivation; SOS is the
proof.

## Active Approach
Classical calculus route: real-rootedness ⇒ (Rolle) derivative real-rooted ⇒
reduce to a quadratic ⇒ discriminant ≥ 0 is Newton. n=2 and n=3 arities now
complete via explicit SOS discriminant certificates; the GENERAL `n` reduction
(arbitrary arity) still needs the packaged iterated-Rolle lemma.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: real-rooted/discriminant atom + n=2 base case (I);
  n=3 both steps via SOS discriminant certificates (II)

## Blockers
- **MATH**: general (arbitrary-`n`) Newton needs the packaged lemma
  "differentiation preserves full real-rootedness counting multiplicity"
  (iterated Rolle on `∏(X - xᵢ)`) — not in Mathlib; `problem.md` estimates
  multi-week. Retained open (not stubbed). The per-arity SOS route sidesteps it
  for fixed small `n` but does not scale symbolically.

## Next Action
1. n=4 by the same SOS discriminant route (three Newton steps; degree grows but
   each reduced quadratic still admits an SOS certificate) — a further concrete
   instance if desired, though it approaches enumeration.
2. The genuine general increment: prove derivative-of-fully-real-rooted is
   fully-real-rooted (Rolle between consecutive roots + multiplicity), then
   reduce three consecutive coefficients to a quadratic and apply
   `discrim_nonneg_of_root` for the arbitrary-`n`, signed-input Newton.
