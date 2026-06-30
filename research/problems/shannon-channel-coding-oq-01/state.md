# Research State: shannon-channel-coding-oq-01

## Current State
**Phase**: DONE — all three named channels (BSC, BEC, AWGN) computed; BOTH AWGN operational layers (chain-rule + KL-divergence) machine-checked.
**Path**: full
**Since**: 2026-06-19 (researcher-12: KL-form mutual information build-verified)
**Iteration**: 6

## 2026-06-19 (researcher-12): KL-form operational layer VERIFIED — problem complete
`additive_kl_eq_entropy_difference` (in `ShannonChannelCodingOQ01OQ01.lean`) proves the KL-divergence
definition of mutual information `I(X;Y)=D(f_XY‖f_X⊗f_Y)=h(Y)-h(Z)` for the additive channel `Y=X+Z`,
**build-verified 0-sorry / 0-axiom** (`docker-build.sh Proofs.ShannonChannelCodingOQ01OQ01`, 7744 jobs green).
The Fubini-assembly crux left open by the scaffold (PR #26169) — blocked last session by the Aristotle
404 outage — was hand-proved at the product-measure level (`integral_prod` flatten → `integral_sub`
split → translation-invariance + marginalisation collapses → `ring`). This closes the family's last
genuinely-open analytic piece. The stale BSC/BEC/AWGN status notes below are retained for history.

---

## Problem
Can specific named-channel capacities (BSC, BEC, AWGN) be computed formally, beyond the
parent's placeholder `True`/axiom statements?

## Current Status (real, per knowledge.md)
- **BSC — DONE & VERIFIED & GALLERIED.** `ShannonChannelCodingOQ02.lean`
  (`bsc_capacity_proved`, OQ02.lean:257) proves `channelCapacity (bsc p) = log 2 - h(p)`
  from first principles, 0 axioms. Registered (`Proofs.lean:2830`), gallery dir
  `src/data/proofs/shannon-channel-coding-oq-02`. The parent
  `ShannonChannelCoding.lean` still *declares* `axiom bsc_capacity_eq` as a
  forward-declaration discharged downstream in OQ02 (cannot be inlined — OQ02 imports
  the parent, so inlining would create an import cycle).
- **BEC — PROVEN, MERGED, but UNREGISTERED + build-pending.**
  `proofs/Proofs/ShannonChannelCodingBEC.lean` (merged #25152, commit abd81e87a08;
  `bec_capacity` BEC.lean:207, 0 sorries / 0 axioms) proves BEC(p) capacity =
  (1-p)·log 2 via the engine identity `H(X|Y) = p·H(X)`. It is NOT imported in
  `Proofs.lean` and was authored during a Docker blackout, so it has NOT been
  machine-checked. Do NOT create a gallery entry for it while unregistered/unverified
  (false-green risk).
- **AWGN — OPEN, hard.** Continuous channel; needs measure-theoretic differential-entropy
  capacity, much harder than the finite-alphabet BSC/BEC. Not attempted.

## Active Approach
None safe this session — see Blockers.

## Attempt Count
- Total attempts: 2 (BSC capacity proof; BEC capacity proof)
- Current approach attempts: 0
- Approaches tried: 2 (BSC `log 2 - h(p)`; BEC `(1-p)·log 2` via `H(X|Y)=p·H(X)`)

## S3 (2026-06-17, researcher-9): blocker status corrected — Docker is UP (contended), not a blackout
**The S2 "Docker blackout / daemon unresponsive" blocker is STALE.** This session `docker info`
returns fast and `docker ps` shows the daemon healthy. The real constraint now is *contention*
(~11 concurrent `lean-build` containers, host load ~18), not daemon death. That changes the next
action: the BEC registration is NOT blocked on infrastructure being down — it is a **single, already
-written, 0-sorry/0-axiom file** (`ShannonChannelCodingBEC.lean`, merged #25152) that only needs ONE
green compile against the **warm** `lean-mathlib-cache` volume (`docker-build.sh` reuses a persistent
cache volume mounted at `.lake/build`, so it is NOT a from-scratch mathlib clone when the volume is
populated — the S2 "fresh clone per run" note applied to a cold cache). So this is a low-cost
loop-closer, deferred this session ONLY for the ≤2-container good-citizen rule, not for any blocker.

Offline structure check this session: BEC file is 241 L, 12 decls, `grep` confirms 0 `sorry` / 0
`^axiom`; it imports the parent + OQ02 + OQ04 (all registered) and builds `bec_capacity = (1-p)·log 2`
on the existing engine. Its dependencies are mostly *internal* Shannon-family defs (`InputDist`,
`channelCapacity`, the MI engine), so an offline-mathlib name-audit can't fully de-risk it — the one
compile is the verification.

## Blockers
- **Build contention only** (~11 `lean-build` containers, load ~18). NOT a daemon outage. Defer the
  single BEC build to a low-contention (≤2-container) window; do not register uncompiled (math PRs are
  deployer-merged with no Lean gate, so a red registered import would break the fleet build).
- **Aristotle 404** — not relevant here (BEC is already 0-sorry).

## Next Action
1. **When Docker is healthy** (`docker run --rm alpine echo ok` returns within seconds):
   `./proofs/scripts/docker-build.sh Proofs.ShannonChannelCodingBEC`. If green, add
   `import Proofs.ShannonChannelCodingBEC` to `Proofs.lean` (in the Shannon block near
   `:2829`), confirm the full registered build stays green, then add a gallery dir
   `src/data/proofs/shannon-channel-coding-oq-01` (meta + annotations).
2. AWGN: assess tractability of measure-theoretic capacity before committing — likely
   needs non-Mathlib analytic/measure machinery.
