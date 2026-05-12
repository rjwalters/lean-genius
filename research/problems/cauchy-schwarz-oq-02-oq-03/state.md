# State: cauchy-schwarz-oq-02-oq-03

## Current Phase

OBSERVE (Session 1) — survey + Mathlib audit + S2 plan.

## Problem

Formalize the complex polarization identity:

```
⟨f, g⟩_ℂ = (‖f + g‖² − ‖f − g‖² + i‖f + ig‖² − i‖f − ig‖²) / 4
```

over `InnerProductSpace ℂ E`.

## Next Action

S2 ACT — single-shipping session:

1. Create `proofs/Proofs/CauchySchwarzOQ02OQ03.lean` with the typed wrapper
   theorem `polarization_identity_complex` proved by direct appeal to
   Mathlib's `inner_eq_sum_norm_sq_div_four`.
2. Create gallery entry
   `src/data/proofs/cauchy-schwarz-oq-02-oq-03/{meta.json, annotations.json,
   index.ts}`.
3. Build verify via `./proofs/scripts/docker-build.sh
   Proofs.CauchySchwarzOQ02OQ03`.

Estimated Lean LOC: ~60. Gallery: ~120 lines.

## Decomposition Plan

| Session | Phase | Deliverable | Status |
|---|---|---|---|
| S1 | OBSERVE | Mathlib audit, scaffold (4 docs + JSON) | **this iteration** |
| S2 | ACT | `CauchySchwarzOQ02OQ03.lean` + gallery | next |
| S3 | ACT (optional) | `ℂ`-parallelogram-law + Pythagorean-ℂ wrappers | optional |

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE survey)
- Current approach attempts: 1 (Mathlib upstream lemma `inner_eq_sum_norm_sq_div_four`)
- Approaches tried: 1

## Key Files (when shipped)

- `proofs/Proofs/CauchySchwarzOQ02OQ03.lean` — companion file (S2)
- `proofs/Proofs/CauchySchwarzOQ02.lean` — parent file (contains the real
  `polarization_identity` for reference; unchanged by S2)
- `src/data/proofs/cauchy-schwarz-oq-02-oq-03/meta.json` — gallery entry
  with status `verified` (0 sorries, 0 axioms)

## Notes for Future Sessions

- **Race-safe behaviour:** per memory rules, even tier-B fresh slugs are
  not race-safe. Before pushing S2 ACT, re-run
  `gh pr list --search "cauchy-schwarz-oq-02-oq-03"` and abandon if a
  duplicate appears.
- **Build:** must use the Docker wrapper, not `lake build`. The proof is
  a one-liner so the build is purely a sanity check; cache should be warm
  for `Mathlib.Analysis.InnerProductSpace.Basic`.
- **Don't add `loom:review-requested`.** Math-research PRs go through
  the deployer's auto-merge path, not Judge review.
- **Polarization-identity-in-the-other-direction** — the corollary
  "if two inner products on `E` induce the same norm then they are equal"
  is a natural S3 candidate, but it requires showing the inner products
  are *symmetric/conjugate-symmetric* before polarization kicks in.
  Mathlib's `Inner` typeclass already bundles this, so the statement is
  trivial; the *value* of the corollary is pedagogical, not technical.
  Defer to S3 only if Mathlib does not already expose it.
