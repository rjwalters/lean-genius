# Knowledge Base: dirichlet-approximation-theorem-oq-01

Infinitude of good rational approximations: for every irrational α there are
infinitely many p/q (lowest terms) with |α − p/q| < 1/q².

---

## Status: COMPLETE (verified)

`proofs/Proofs/DirichletApproximationOQ01.lean` — 101 lines, **0 sorry / 0
axiom / 0 native_decide**, no assumption-carrying structures. Headline results:

- `infinite_good_rat_approx (hξ : Irrational ξ)` — the set of rationals q with
  |ξ − q| < 1/q.den² is infinite.
- `infinite_coprime_approx` — the original contribution: bridges the Mathlib
  infinitude to the classical coprime integer-pair form {(p,q) : Coprime, ...}.
- `infinite_approx_iff_irrational` — the characterization (infinitude ⇔ irrational).
- `exists_good_approx` — the one-shot existence corollary.

The headline infinitude delegates to Mathlib's
`AddCircle`/`Irrational`-based density machinery; the coprime-pair bridge is the
genuine new content (Tier-B delegation, disclosed in the gallery meta).

## Closure (researcher-1, 2026-06-18)

Verified merged + integrated: PR #25627 merged to main; the file is registered
in `Proofs.lean` (import line) so it is CI-compiled; a gallery entry
`src/data/proofs/dirichlet-approximation-theorem-oq-01/` (meta.json +
annotations.json) exists. The previous session left this `in-progress/ACT`
only because local Docker was saturated and it couldn't self-verify the build;
that gate is now closed by CI on main. Marking COMPLETED.

## Next Steps

None for this slug. Possible adjacent work elsewhere: the quantitative
Hurwitz refinement (|α − p/q| < 1/(√5 q²) with the √5 optimal) is a distinct,
stronger statement and would be its own problem.
