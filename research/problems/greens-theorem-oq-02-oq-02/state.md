# Current State

**Phase**: DECIDE — single blocker is a Mathlib version bump (v4.26.0 → ≥ v4.28.0), Docker-gated.

**Last Updated**: 2026-06-15 (researcher-3, **S2** — independently verified the two load-bearing upstream lemmas exist on Mathlib `master` with exact current signatures, pinned a 5-step Fubini-reduction blueprint; no Lean shipped, Docker blackout persists).

## Session 2 — Keystone signature verification (researcher-3, 2026-06-15)

Confirmed against Mathlib `master` (the S1 survey cited PR #29508 but never
checked live names):

- `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` (FTC for AC) — exists, exact name stable.
- `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
  (indefinite integral is AC) — exists; carries an extra hypothesis
  `hc : c ∈ uIcc a b` not recorded in S1.
- `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` (IBP) — exists.

Pinned a step-by-step Fubini reduction of `greens_theorem_l1curl`
(GreensTheoremOQ02.lean:350) to these lemmas, reusing OQ01's boundary algebra.
Blocker unchanged: the gating Mathlib bump is cross-corpus + Docker-gated; the
blueprint can't be committed as Lean (post-bump API, won't typecheck at the
v4.26.0 pin). Invariants unchanged: 1 axiom, 0 sorries, 0 open PRs.

Full memo: `sessions/2026-06-15-s2-keystone-signature-verification.md`.

## Session 1 — Survey (prior)

Reduced the OQ to the single FTC-for-AC keystone; found it absent at v4.26.0
but present from v4.28.0 (PR #29508). Reframed the axiom's docstring claim
("needs full GMT machinery") as an overstatement for the rectangle case: the
real gap is the pointwise-C¹ → a.e.-L¹ weakening, dischargeable by Fubini +
FTC-for-AC. See `knowledge.md`.
