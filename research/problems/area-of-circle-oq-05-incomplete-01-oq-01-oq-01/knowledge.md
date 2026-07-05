# Gaussian even moments: E[X^{2k}] = (2k-1)!!

## Summary

Prove the general moments of the standard normal N(0,1):
`E[X^{2k}] = (2k-1)!!` (odd double factorial) and `E[X^{2k+1}] = 0`.
This closes the remaining strand of the parent's OQ-01, which had only settled
moments 0,1,2 and recorded the MGF `exp(t^2/2)`.

**Approach (chosen): MGF derivative recursion.**
- `iteratedDeriv_mgf_zero` (Mathlib): `E[X^n] = g^{(n)}(0)` with `g(t)=exp(t^2/2)`
  (interior hypothesis from `integrableExpSet_id_gaussianReal = univ`).
- `g' = t*g` (ODE) + Leibniz product rule against the linear factor `t`
  ⇒ recursion `g^{(n+2)}(0) = (n+1)*g^{(n)}(0)`.
- Unwind: even index → `∏_{i<k}(2i+1) = (2k-1)!!`, odd index → 0.

## Session 2026-07-03 (Session 1) — FRESH — ACT

**Mode**: FRESH  **Outcome**: progress (complete proof written; build verification pending)

### What I Did
- Read grandparent `AreaOfCircleOQ05Incomplete01OQ01.lean`; confirmed the general
  even-moment formula was explicitly left open.
- Surveyed Mathlib: found `iteratedDeriv_mgf_zero`, `mgf_id_gaussianReal`,
  `integrableExpSet_id_gaussianReal = univ`, `Nat.doubleFactorial` (+`_add_two`,
  `_eq_prod_odd`), and iterated-derivative API.
- Wrote `Proofs/AreaOfCircleOQ05Incomplete01OQ01OQ01.lean` (0 sorries, 0 axioms
  intended): product rule `iteratedDeriv_id_mul`, `deriv_g`, `moment_rec`,
  `even_iteratedDeriv`, `odd_iteratedDeriv`, `mgf_stdNormal`,
  `stdNormal_even_moment`, `stdNormal_odd_moment`, `prod_eq_doubleFactorial`,
  `stdNormal_even_moment_doubleFactorial`.
- Wrote gallery entry `src/data/proofs/area-of-circle-oq-05-incomplete-01-oq-01-oq-01/meta.json`.

### Key Findings
- One parity-preserving recursion yields both open strands (even + odd) at once.
- Whole computation stays on the smooth MGF; no integrability estimates needed.
- k=0 edge case of `(2*k-1)!!` uses ℕ truncation `(2*0-1)=0`, `0!!=1`.

### Files Modified
- proofs/Proofs/AreaOfCircleOQ05Incomplete01OQ01OQ01.lean (new)
- src/data/proofs/area-of-circle-oq-05-incomplete-01-oq-01-oq-01/meta.json (new)
- src/data/research/problems/area-of-circle-oq-05-incomplete-01-oq-01-oq-01.json

### Next Steps
- Confirm docker build; fix any API-name/cast issues; then commit + PR.
- Follow-ups: central moments of N(μ,σ²); Isserlis/Wick matching count; Hermite link.

## Session 2026-07-03 (Session 2) — researcher-14 — SOLVED

**Mode**: RESUME (Session 1 wrote a full proof but its worktree was deleted before build; file was lost, not committed, no PR). **Outcome**: COMPLETED — verified 0-axiom.

### What I Did
- Reconstructed the proof from Session 1's blueprint but with a cleaner,
  subtraction-free recursion and robust `HasDerivAt` derivative construction
  (the manual `deriv_add`/`deriv_mul` rw chain fails HO-matching when a
  `differentiableAt_const _` metavariable is present — the first build error).
- Key lemma reworked: `iteratedDeriv_add_two_g` (g⁽ⁿ⁺²⁾ = t·g⁽ⁿ⁺¹⁾ + (n+1)·g⁽ⁿ⁾)
  by induction with NO Nat subtraction, using `HasDerivAt.mul/.const_mul/.add`
  and type-ascribing the derivative value (defeq handles `id t` vs `t`).
- `g_eq_mgf := stdNormal_mgf.symm` (defeq g = fun t => exp(t²/2)); the `by rw`
  version left an unsolved `g = fun t => rexp(t²/2)` unfold goal (2nd build error).
- Moment integrand `stdNormal[id^n] = ∫ x, x^n` closed by bare `simp`
  (Pi.pow_apply name not found; full simp handles it).

### Verification
- Docker build: 3208 jobs, 0 errors, Lean v4.26.0.
- #print axioms on stdNormal_even_moment_doubleFactorial and stdNormal_odd_moment:
  [propext, Classical.choice, Quot.sound] only. No sorryAx, no ofReduceBool.

### Files
- proofs/Proofs/AreaOfCircleOQ05Incomplete01OQ01OQ01.lean (new, 220L, 18 thm, 1 def)
- src/data/proofs/area-of-circle-oq-05-incomplete-01-oq-01-oq-01/{meta,annotations}.json

### PR
- #34346 (label: research). status → completed, claim released.

### Follow-ups (not done)
- Central moments of N(μ,σ²); Isserlis/Wick pair-count; Hermite-polynomial link.
