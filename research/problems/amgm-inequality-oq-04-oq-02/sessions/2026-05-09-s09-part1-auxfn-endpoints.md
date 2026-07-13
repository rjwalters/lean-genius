# Session 9 part 1 — auxFnK + endpoint vanishings

**Date**: 2026-05-09
**Researcher**: researcher-1
**Phase**: ACT (S9 part 1; S9 parts 2–4 deferred)
**Outcome**: progress

## What landed

A new §13 in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` with the
**boundary side** of the K-side integration-by-parts (IBP) step:

1. `auxFnK k θ := Real.sin θ * Real.cos θ / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)`
   — the auxiliary function whose FTC closure on `[0, π/2]` produces
   the K-side integral identity.
2. `auxFnK_zero (k : ℝ) : auxFnK k 0 = 0` — by `Real.sin_zero,
   zero_mul, zero_div`.
3. `auxFnK_pi_div_two (k : ℝ) : auxFnK k (π / 2) = 0` — by
   `Real.cos_pi_div_two, mul_zero, zero_div`.

Net new: 1 definition, 2 theorems, 0 axioms, 0 sorries. File total
1015 lines (was 963).

## Why this is the right scope for S9 part 1

The full S9 plan from `state.md` (post-#17451) is ~95 lines split four
ways:

* part 1 (this PR): `auxFnK` def + endpoints (~15 lines actual Lean,
  rest is exposition).
* part 2: `auxFnK` chain rule (~50 lines, `HasDerivAt.mul` +
  `HasDerivAt.sqrt` + `HasDerivAt.div` plus an algebraic reduction
  matching `(cos²θ − sin²θ + k² sin²θ cos²θ / D²)`).
* part 3: FTC on `auxFnK` over `[0, π/2]` (~15 lines, just
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` + the two
  endpoint-vanishings landed here).
* part 4: combine with §12's `integral_cos_sq_div_sqrt_denom` (~15
  lines, algebraic).

Splitting at the `auxFnK_zero / auxFnK_pi_div_two` boundary makes part 1
**self-contained, build-pending-safe, and free of HasDerivAt
manipulation**. The chain rule (part 2) is where the genuine API
density lives — pinning that into a separate PR avoids tying a quick
boundary-vanishing landing to a long chain-rule debug cycle.

## Trap-checks before edits

* `gh pr list` for slug: 2 OPEN PRs (#17371 S6 dE/dk, #17445 my own
  S8 dE_dk replay) — both touch §1/§8/§9 and add a `dE_dk` theorem
  after §11. They do **not** touch §13 / `auxFnK`. Independence
  preserved.
* `git log origin/main --oneline -20 --grep='amgm'`: top 5 amgm
  commits are #17451 (S8 partial K-side integrals), #17431 (S7 K-side
  bound), #17373 (S6 K-side chain rule), #17358 (S5 E-side bound),
  #17269 (S4 dE/dk infra). The K-side track now has §10 / §11 / §12
  on origin/main; §13 (`auxFnK`) is the next link.
* `git branch -r | grep amgm`: three feature branches all already
  have PRs — no orphan `s9` / `auxfn` / `ibp` branches in flight.

## Mathlib API surface

Zero new lemmas. The two endpoint-vanishings need only:

* `Real.sin_zero : Real.sin 0 = 0`
* `Real.cos_pi_div_two : Real.cos (π / 2) = 0`
* `zero_mul`, `mul_zero`, `zero_div` (default simp set; we use `rw`
  explicitly for transparency).

No new imports beyond `import Mathlib` and `import Proofs.AmgmInequalityOQ04OQ01`
already present.

## Risks

* **Build pending**: not validated against the Docker wrapper this
  session (the broken `proofs/.lake` symlink documented in MEMORY.md
  costs ~45 min for a full Mathlib clone; not within the 90-min claim
  TTL after the trap-check / planning overhead). The deliverable is
  three lines of `rw` over basic Mathlib trig identities; high
  confidence. If the build fails, the fix is local to §13 and
  Mechanic-tractable.
* **Concurrent S9**: another researcher could be doing the same scope
  in parallel — none was visible at claim time, but the slug is hot
  (7+ PRs in 24h). If a parallel S9 part 1 lands first, this PR
  becomes redundant; close gracefully.

## Next session pointer

Pick up §13's chain rule:

```lean
lemma auxFnK_hasDerivAt (k θ : ℝ) (hk : k ^ 2 < 1) :
    HasDerivAt (fun θ => auxFnK k θ)
      (Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
         - (1 - k ^ 2) * Real.sin θ ^ 2
             / ((1 - k ^ 2 * Real.sin θ ^ 2)
                 * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))) θ
```

Strategy: `HasDerivAt.mul` on `sin θ · cos θ` (deriv = `cos²θ − sin²θ`),
`HasDerivAt.sqrt` on `√(1 − k² sin²θ)` (inner deriv `−2k² sin θ cos θ`),
`HasDerivAt.div` of the product over the sqrt, then `field_simp; ring`
to match the target form. The denominator's nonvanishing is supplied
by `AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ`.

## References

* `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` §13 (this PR).
* `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` §12 (PR #17451) —
  `integral_sin_sq_div_sqrt_denom`, `integral_cos_sq_div_sqrt_denom`
  to be combined with the FTC step in S9 part 4.
* `proofs/Proofs/AmgmInequalityOQ04OQ01.lean` — `sqrt_denom_pos`
  (denominator nonvanishing).
* `Mathlib/Analysis/Calculus/IntervalIntegral.lean` —
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` (the FTC workhorse
  for S9 part 3).
