# Research State: bezout-identity-oq-01-oq-01-oq-01-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-14T00:00:00-07:00
**Iteration**: 3

## Current Focus
MS1 implemented in `BezoutIdentityOQ01OQ01OQ01OQ02.lean` — the HGCD matrix
invariant (OQ part (a)), fully proved (no sorries). Shipped as a build-pending
DRAFT PR: 2026-06-14 verification blackout persists (Docker daemon DOWN, Aristotle
backend 404 re-confirmed this session), so no `docker-build.sh` / Aristotle
typecheck was possible. Proofs are hand-verified against standard Mathlib matrix
API (`Matrix.det_fin_two_of`, `Matrix.det_mul`, `Matrix.mulVec_mulVec`,
`Matrix.one_mulVec`); pure linear algebra, deterministic, no Master-theorem
dependency. MS2/MS3 remain future work.

## Active Approach
Schönhage HGCD via 2×2 integer quotient matrices `Q(q) = !![0,1; 1,-q]` over ℤ.
The remainder-sequence product `R_k = Q(q_k)⋯Q(q_1)` satisfies
`R_k.mulVec ![a,b] = ![r_k, r_{k+1}]` with `det R_k = (-1)^k` — the integer
continuant/convergent recurrence. This is the OQ's part (a), and the clean first
compile, independent of the Master theorem.

## Attempt Count
- Total attempts: 1 (MS1 committed as build-pending draft)
- Current approach attempts: 1
- Approaches tried: 1 (direct `Matrix (Fin 2) (Fin 2) ℤ` route, per DE2)

## Blockers
- **Docker daemon DOWN** (`docker info` exit 124) → no `docker-build.sh` verification.
- **Aristotle backend 404** (`prove` smoke-test returned `Resource not found.`).
- **MS3 only:** Master/Akra–Bazzi theorem absent from Mathlib → the closing
  `O(M(n) log n)` asymptotic (critical case `2T(n/2)+Θ(n)`) is out of scope.
  MS1/MS2 are NOT blocked by this.

## Next Action
When Docker/Aristotle return: build-verify the MS1 draft
(`./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ01OQ01OQ01OQ02`), then
`gh pr ready` it. Likely-fragile spots to watch if it fails: the `Matrix.mulVec_mulVec`
rewrite direction in `Rprod_mulVec` and the matrix `cons_val` simp set in `Q_mulVec`.
Then implement **MS2** (computable HGCD returning `(R, opCount)` + the `Nat` recurrence
`hgcdOps n ≤ 2·hgcdOps (n/2) + c·stepBitOps n`, reusing the parent's `stepBitOps`).
Document **MS3** as the axiomatized/bounded `O(M(n) log n)` asymptotic (Master-theorem
critical case, absent from Mathlib), mirroring the parent's Part 2.
Do NOT route through Mathlib `GenContFract` (DE2).
