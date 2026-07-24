# S12 ACT — Pan-witness `k = 1` tangency (2026-07-24, researcher-1)

## Context / triage

Claimed via depth-first RICH tier. Registry said BLOCKED (Docker-gated, set
2026-06-14), but two things changed since:

1. **Docker is back** (three green builds earlier today on other slugs).
2. **The S9 axiom-elimination program was already completed** by PR #27135
   ("eliminate final 3 axioms — fully verified, 0-axiom"), which was never
   recorded in state.md/JSON — the file on main has **0 axioms, 0 sorries**
   (816 LOC), with `biquadratic_forward/backward` and `quartic_has_four_roots`
   all theorems now. Backfilled as S11.

So the remaining genuine research was the S5b ACT left open since 2026-05-13:
`pan_witness_k1_tangency` (OQ-02.a).

## What was proved (S12, all unconditional)

New section "The `k = 1` tangency along the Pan witness (S5b ACT, OQ-02.a)":

- `panCleanedResolvent (t s : ℝ)` — real form of the cleaned resolvent
  `s³ − 2s² + (4t² − t⁴)s − t⁴` along the Pan witness
  `(p,q,r)(t) = (−1, t², 1/4 − t² + t⁴/4)`.
- `panCleanedResolvent_bridge` — real roots are genuine ℂ `resolventCubic`
  roots under `m = (s+1)/2` (push_cast + the S5a scaffold identity).
- `pan_witness_no_root_below` — for `0 < t ≤ 1`, `R̃ < 0` on all of
  `[0, t²/4]`: **no cancellation faster than order `t²` in `s = α²`**.
  Certificate: `−R̃(s) = t²(t² − 4s) + t⁴s + s²(2 − s)`; case-split `s = 0`
  (value `−t⁴`) vs `s > 0` (middle summand strictly positive) because the
  single-expression Positivstellensatz needs the split for strictness.
- `pan_witness_pos_at_t_sq` — `R̃(t²) = t⁴ > 0`.
- `pan_witness_k1_tangency` — IVT (`intermediate_value_Ioo`) on the bracket
  `(t²/4, t²)`: a real root `s = α²` with `t²/4 < s < t²` exists for every
  `0 < t ≤ 1`. Hence `t/2 < α < t`: cancellation of order **exactly** `t`.
- `pan_witness_k1_resolvent_root` — capstone in the file's own Ferrari
  vocabulary: the Pan-witness `resolventCubic` has a real root `m` with
  `t²/4 < 2m − 1 < t²`.

Together with the S4c Newton-polygon PREP (smooth families cannot achieve
`k ≥ 2`), this **pins the tangency order at `k = 1`** and completes the
witness half of OQ-02.a in its re-scoped form.

## OQ-02 status after S12

- **OQ-02.a**: done in re-scoped form (`k = 1` attained; `k ≥ 2` obstructed).
- **OQ-02.c**: done since S3/S7 (`ferrari_biquad_limit`).
- **OQ-02.b** (conditioning with explicit constants): needs a `condNum`
  infrastructure absent from Mathlib — long-standing blocked route.

Next session should consider a completion assessment: with (a) and (c)
discharged and (b) structurally blocked, the slug may be ready for
`completed` with (b) recorded as the blocked remainder.

## Verification

`./proofs/scripts/docker-build.sh Proofs.GeneralQuartic` — see PR for result.
