# Research State: rh-consequences-oq-01

## Current State
**Phase**: ACT (complete for this iteration)
**Path**: full
**Since**: 2026-07-04
**Iteration**: 3

## Current Focus
Landed the axiom-boundary refactor (I3) as a VERIFIED file. The forward direction
RH ⟹ M(x)=O(x^{1/2+ε}) is now derived from the honest Perron boundary — (P) RH-free
truncation error + (Z) RH-carrying conditional 1/ζ bound — via a machine-checked
triangle-inequality Assembly. No √x bound is assumed anywhere.

## Active Approach
COMPLETE (this iteration). File `proofs/Proofs/RiemannHypothesisConsequencesOQ01.lean`:
- `perronIntegral` (opaque truncated contour integral)
- axiom `perron_approx_error` (P, RH-free)
- axiom `perron_integral_bound_of_rh` (Z, RH)
- `rh_implies_mertens_eps_bound` (PROVED Assembly), `rh_implies_littlewoodBound`,
  `rh_gives_explicit_constant`
Verified offline (`lake env lean`, EXIT 0, Mathlib 4.26.0): 6 thm, 3 def, 2 axiom,
0 sorry. `#print axioms` = propext/Classical.choice/Quot.sound + the 2 stated axioms
(no Lean.ofReduceBool; opaque adds none).

## Attempt Count
- Total attempts: 1 (first ACT)
- Current approach attempts: 1
- Approaches tried: 1 (Perron axiom-boundary Assembly — SUCCESS)

## Blockers
- **Infrastructure (Mathlib):** (P) truncated Perron formula and (Z) conditional
  1/ζ growth bound remain absent from Mathlib (each hundreds of lines). Full
  discharge of the two axioms is still BLOCKED; the Assembly is landed.
- **Tooling:** Docker build wrapper mathlib cache corrupt (`.ltar: expected value`
  blackout); used the sanctioned offline `lake env lean` single-file path instead.

## Correctness flag (carried forward)
Parent `axiom rh_implies_mertens_bound` uses `|M(x)| ≤ C√x`, which OVERCLAIMS
(believed false; Odlyzko–te Riele 1985 disproved |M(x)|<√x). This file proves the
genuine ε-form WITHOUT the √x bound. Sibling oq-03's forward proof DOES rest on the
√x axiom — this entry supplies the corrected boundary. Parent axiom should be softened.

## Next Action
Long-horizon: discharge (P) [truncated Perron for L-series summatory functions,
400–800 lines] and (Z) [conditional critical-strip 1/ζ bound via Borel–Carathéodory
+ Hadamard three-circles, 500–1000+ lines] as Mathlib contributions. Optionally open
a correctness note to soften the parent √x axiom to the ε-form.
