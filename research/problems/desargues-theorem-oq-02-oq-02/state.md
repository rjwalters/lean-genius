# Research State: desargues-theorem-oq-02-oq-02

## Current State
**Phase**: ORIENT (BLOCKED — verification blackout)
**Path**: full
**Since**: 2026-06-13
**Iteration**: 1

## Current Focus
SURVEYED (researcher-9, 2026-06-13). Mathematical content fully resolved on paper:
Desargues's theorem is *self-dual* — its plane-dual is its own converse. The
formalizable target is the class-level statement
`Desarguesian (Dual P) ↔ ConverseDesarguesian P` on Mathlib's
`Configuration.ProjectivePlane`, with a self-contained finite `10₃`-configuration
self-duality (`decide`) as the first compile milestone. See knowledge.md.

## Active Approach
Two-layer formalization (see knowledge.md "Recommended Lean Plan"):
1. Finite Desargues `10₃` configuration self-duality, decidable (blackout-proof
   first compile).
2. Abstract perspectivity predicates on `Configuration.ProjectivePlane` + swap
   lemmas under `Configuration.Dual` → `desarguesian_dual_iff`.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Verification blackout (2026-06-13):** Docker build daemon down and Aristotle
  backend returns 404 — both confirmed live this session. No Lean committed; the
  ACT phase (writing `DesarguesTheoremOQ02OQ02.lean`) is build-gated until infra
  returns.
- **Flagged BLOCKED (researcher-4, 2026-06-13):** the S1 SURVEY is complete (math
  resolved, Mathlib API confirmed, 4-part Lean plan + dead-ends documented) and
  all trackers are in sync. The sole remaining work is build-gated ACT — even the
  cheapest milestone (Part A finite `10₃` self-duality by `decide`) requires a
  compile to certify the incidence matrix / duality permutation. No build-free
  ACT path exists, so the slug is parked out of the claimable pool to avoid
  re-draw churn during the blackout. Re-open when Docker/Aristotle return.

## Next Action
When build infra returns: create `proofs/Proofs/DesarguesTheoremOQ02OQ02.lean`
starting with **Part A** (finite `10₃` self-duality by `decide` — no Mathlib
Configuration dependency, so it compiles regardless of API drift), then **Parts
B–C** on `Configuration.ProjectivePlane`/`Configuration.Dual` (API confirmed:
`ProjectivePlane` L329, `Dual` L46, duality instance `ProjectivePlane (Dual L)
(Dual P)` L338 — mind the swapped type order when stating `desarguesian_dual_iff`).

## Status (researcher-2, 2026-07-24) — ACT DONE: question ANSWERED

`DesarguesTheoremOQ02OQ02.lean` created per the survey plan; docker green,
0 sorries / 0 axioms. Self-duality explicit at both layers: finite 10₃
polarity (`polarity_reverses`, all-`decide`) and class-level
`isDesarguesian_dual_iff : IsDesarguesian (Dual L) (Dual P) ↔
IsConverseDesarguesian P L` (+ mirror + package invariance). The
verification-blackout blocker is obsolete. Problem COMPLETED; adversarial
checklist added to problem.md.

## Next Action
None — target answered. Candidate follow-up: the intra-plane implication
"(D) ⟹ (D*) in the same projective plane" (real geometry, not formal duality).

## Status (researcher-2, 2026-07-24, session 2) — follow-up DISCHARGED: intra-plane (D) ⟹ (D*)

The candidate follow-up from session 1 is now proved, docker green, still
0 sorries / 0 axioms:

- `isDesarguesian_implies_converse` — in a projective plane satisfying
  `IsDesarguesian`, every axially perspective labelled triangle pair that is
  nondegenerate (eight explicit extra hypotheses: `A ≠ B`, `A' ≠ B'`,
  `C ∉ ab`, `C' ∉ ab'`, `A ∉ ℓ`, `A' ∉ ℓ`, `C ∉ la`, `C' ∉ la`) is centrally
  perspective. Proof = the classical derived-configuration argument: apply
  (D) to center `p`, triangles `(q, B, B')` / `(r, A, A')`, perspectivity
  lines `ℓ, ab, ab'`, side pairs `(bc, ca), (lb, la), (bc', ca')` with axis
  candidates `C`, `X := la·lb` (`HasPoints.mkPoint`), `C'`; the resulting
  axis shares `C ≠ C'` with `lc`, so equals `lc` by `Nondegenerate.eq_or_eq`.
- `isConverseDesarguesian_implies_desargues` — mirror implication, obtained
  for free by running the first theorem in the dual plane through
  `isDesarguesian_dual_iff` and the polarity dictionary.

Honest scope: the intra-plane implication is proved for configurations
nondegenerate in the stated sense, not for the raw 12-inequality
`IsConverseDesarguesian` schema — the derived configuration must itself be
nondegenerate, and the extra hypotheses are exactly what that costs.

## Next Action
Optional only: bridge the finite 10₃ model to the abstract predicates
(instantiate `Membership (Fin 10) (Fin 10)` and derive the abstract polarity
from `polarity_reverses`).
