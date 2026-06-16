# Research State: niven-theorem-oq-01

## Current State
**Phase**: DONE (build-pending verification)
**Path**: full
**Since**: 2026-06-16T04:17:04-07:00
**Iteration**: 2

## Current Focus
Proof is COMPLETE. Niven's theorem is already in Mathlib v4.26
(`Mathlib/NumberTheory/Niven.lean`, Meiburg/Broshi 2025). The gallery entry
`proofs/Proofs/NivenTheorem.lean` keeps the explicit `interval_cases`
enumeration tail and discharges the deep algebraic-integer core by delegating
to Mathlib. **PR #25163 (branch `feature/researcher-8-niven-mathlib`) carries
the full discharge — OPEN, build-pending.**

## Active Approach
Mathlib delegation (no from-scratch formalization needed):
- Core lemma `two_cos_int_of_rational`: `2·cos θ ∈ ℤ` when `θ = (m/n)π` and
  `cos θ ∈ ℚ`. Proved via
  `Real.isIntegral_two_mul_cos_rat_mul_pi (m/n)` (gives `IsIntegral ℤ (2 cos θ)`)
  then `IsIntegral.exists_int_iff_exists_rat` (a rational algebraic integer is an
  integer). The from-scratch orphan `NivenTheoremCore.lean` was DELETED.

## Name-check verification (offline Mathlib, blackout substitute for Docker build)
Confirmed both names exist at the exact build pin
(`/Users/rwalters/GitHub/mathlib4` @ 2df2f0150c = v4.26.0):
- `Mathlib/NumberTheory/Niven.lean:72/98` `isIntegral_two_mul_cos_rat_mul_pi`
  (aliased to `_root_.isIntegral_two_mul_cos_rat_mul_pi`; `Real.` via open).
- `Mathlib/NumberTheory/Niven.lean:32` `exists_int_iff_exists_rat`.
- Mathlib's own `niven` proof (line 130) uses the identical
  `(...).exists_int_iff_exists_rat` pattern, so the PR's
  `hint.exists_int_iff_exists_rat.mp ⟨2*r, …⟩` is API-sound.

## Attempt Count
- Total attempts: 1 (succeeded, build-pending)
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib delegation)

## Blockers
**Dual infra blackout (2026-06-16)** — cannot machine-verify:
- Docker daemon hangs: `docker info` rc=124 (timeout). `lake build` impossible.
- Aristotle MCP `prove`: 404 "Resource not found".
Name-check above is the strongest available verification under blackout.

## Next Action
When Docker is back: `./proofs/scripts/docker-build.sh Proofs.NivenTheorem`,
grep the log for `error:`. If green, merge PR #25163. Do NOT re-derive — the
proof is written and name-checked; only the build remains.
