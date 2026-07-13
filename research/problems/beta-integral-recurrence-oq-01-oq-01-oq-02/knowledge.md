# Knowledge: Off-diagonal Beta value and the OGF of the central Beta sequence

## Problem Summary

The diagonal Euler Beta sequence b(n) = B(n+1,n+1) = (n!)²/(2n+1)! = 1/((2n+1)·C(2n,n)).
The off-diagonal value B(m+1,n+1) = m!·n!/(m+n+1)! and the diagonal special case
already exist in the gallery (BetaIntegralRecurrence.betaIntegral_nat_nat,
BetaCentralBinomial.betaIntegral_diag_central_binom). The remaining deliverable of
this OQ is the **ordinary generating function** Σₙ b(n)xⁿ in closed form.

## Key Facts (established)

- **Closed form (target, numerically verified 12 digits):**
  Σₙ b(n)xⁿ = 4·arcsin(√x/2)/√(x(4−x)) for 0 < x < 4; value π/2 at x = 2.
- **Contiguous recurrence (VERIFIED in Lean):** (4n+6)·b(n+1) = (n+1)·b(n),
  i.e. b(n+1)/b(n) = (n+1)/(2(2n+3)) — a degree-(1,1) rational ratio
  (hypergeometric-type). This is the coefficient form of the ODE
  x(4−x)y'(x) + (2−x)y(x) = 2, y(0) = 1, solved by the arcsine closed form.
- **Integral bridge (route to the closed form):** b(n) = ∫₀¹ (t(1−t))ⁿ dt (real
  diagonal Beta). Then Σₙ b(n)xⁿ = ∫₀¹ dt/(1 − x·t(1−t)); completing the square
  1 − x·t(1−t) = x((t−1/2)² + (4−x)/(4x)) gives an arctan equal to the arcsine form.

## Session 2026-07-03 (Session 1) — FRESH — VERIFIED arithmetic backbone

**Mode**: FRESH. **Outcome**: progress (verified core shipped; closed form open).

### What I Did
- Confirmed off-diagonal value + diagonal special case already exist in gallery.
- Identified the genuine new deliverable = the OGF closed form.
- Numerically verified recurrence and closed form (mpmath, 12 digits).
- Built Proofs/BetaCentralBinomialOGF.lean (142 L, 8 thm + 1 def, 0 sorry/axiom,
  Docker build OK): centralBeta def over ℝ; base values; positivity;
  reciprocal/central-binomial form; cast bridge to gallery complex Beta value;
  the Nat factorial identity; and the contiguous recurrence.
- Created gallery entry src/data/proofs/beta-integral-recurrence-oq-01-oq-01-oq-02/
  (verified/original, honestly scoped: recurrence-characterization proven, arcsine
  closed form stated as the open analytic sequel).

### Key Findings
- The recurrence + b(0)=1 fully characterizes the OGF as a formal power series and
  pins its ODE; the closed form is the ODE's solution.
- Full analytic proof needs tsum↔integral interchange + FTC — a substantial
  analysis task, appropriate for Aristotle (known classical result).

### Files Modified
- proofs/Proofs/BetaCentralBinomialOGF.lean (new)
- src/data/proofs/beta-integral-recurrence-oq-01-oq-01-oq-02/{meta,annotations}.json, index.ts (new)

### Next Steps
- Prove b(n) = ∫₀¹ (t(1−t))ⁿ dt; interchange; evaluate the integral to arcsine form.
- Re-submit the closed form to Aristotle (overnight) when MCP available.
