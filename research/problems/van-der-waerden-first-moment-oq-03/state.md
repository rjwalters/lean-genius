# Research State: van-der-waerden-first-moment-oq-03

## Current State
**Phase**: ACT (proof drafted; verification blocked by infra)
**Path**: full
**Since**: 2026-06-28
**Iteration**: 2

## Current Focus
Bridge `vdw_lower_bound` (verified, axiom-free) into the `Erdos138` namespace as a
machine-checked lower bound on `W k`, and formally record the strength gap to the
axiomatized bounds.

## Active Approach
Approach A (direct bridge) succeeded at the design level by reusing erdos-138's own
`contains_mono_ap_imp` + `not_in_guarantee_lt_sInf`, combined with Approach B's
honest strength-gap statement (`firstMoment_bound_negligible`). New file:
`proofs/Proofs/Erdos138FirstMomentBridge.lean` (namespace `Erdos138`).

## Attempt Count
- Total attempts: 1 (this session)
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- **INFRA (not mathematical):** Docker build unavailable this session — host disk
  filled to 100% and Docker Desktop's containerd content store corrupted (missing
  blob; `docker images`/`prune` error out). Could not machine-verify. `lake build`
  is forbidden directly. Needs a Docker Desktop restart to verify.

## Next Action
1. Restart/repair Docker Desktop.
2. `./proofs/scripts/docker-build.sh Proofs.Erdos138FirstMomentBridge`.
3. Fix any lemma-name drift (esp. in the analytic `firstMoment_bound_negligible`).
4. Once green: register in `Proofs.lean` and, if desired, surface the verified
   `W` lower bound in a short note on the `erdos-138` / `van-der-waerden-first-moment`
   gallery entries (status stays `axiomatized` for erdos-138 — no axiom removed).
