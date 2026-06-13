# Research State: bezout-identity-oq-01-oq-01-oq-01-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-13T00:00:00-07:00
**Iteration**: 3

## Current Focus
MS1 written (build-UNVERIFIED — 2026-06-13 verification blackout persists:
`docker info` exit 124, Aristotle `prove` smoke-test returns `Resource not found.`).
New file `proofs/Proofs/BezoutIdentityOQ01OQ01OQ01OQ02.lean` formalizes the HGCD
quotient-matrix invariant (the OQ's part (a)), registered in `Proofs.lean`.
Shipped as a DRAFT PR so the deployer will NOT auto-merge unverified Lean.

## Active Approach
Schönhage HGCD via 2×2 integer quotient matrices `Q(q) = !![0,1; 1,-q]` over ℤ.
The remainder-sequence product `R(qs) = Q(q_k)⋯Q(q_1)` (indexed by the
most-recent-first quotient list) satisfies `det (R qs) = (-1)^qs.length` — the
integer continuant/convergent unimodularity relation, the OQ's part (a),
independent of the Master theorem. The single Euclidean step is captured by
`Q q *ᵥ ![x,y] = ![y, x - q*y]`.

## MS1 contents (this iteration)
- `Q : ℤ → Matrix (Fin 2) (Fin 2) ℤ` — the quotient matrix.
- `Q_mulVec : Q q *ᵥ ![x, y] = ![y, x - q * y]` — single Euclidean step.
- `det_Q : (Q q).det = -1` — each step matrix is unimodular.
- `R : List ℤ → Matrix (Fin 2) (Fin 2) ℤ` — the step-product (fold of `Q`).
- `det_R : (R qs).det = (-1) ^ qs.length` — the invariant (induction + `det_mul`).
- `isUnit_det_R` — unimodularity corollary.

## Attempt Count
- Total attempts: 1 (MS1 Lean written, NOT yet compiled — blackout)
- Current approach attempts: 1
- Approaches tried: 1 (direct `Matrix (Fin 2) (Fin 2) ℤ` product; NOT `GenContFract`)

## Blockers
- **Docker daemon DOWN** (`docker info` exit 124) → no `docker-build.sh` verification.
- **Aristotle backend 404** (`prove` smoke-test returned `Resource not found.`).
- **MS3 only:** Master/Akra–Bazzi theorem absent from Mathlib → the closing
  `O(M(n) log n)` asymptotic (critical case `2T(n/2)+Θ(n)`) is out of scope.
  MS1/MS2 are NOT blocked by this.

## Next Action
**When Docker returns:** build `./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ01OQ01OQ01OQ02`
and fix any API drift (likely suspects: the `mulVec`/`!![…]` simp set in
`Q_mulVec`; `Matrix.det_fin_two_of` name). Then mark the draft PR ready and
promote status. Next, **MS2** (computable HGCD returning `(R, opCount)`, plus the
`Nat` recurrence inequality `hgcdOps n ≤ 2·hgcdOps (n/2) + c·stepBitOps n`,
reusing the parent's `stepBitOps`/`Nat.size`/`Nat.log` lemmas). Document **MS3**
as the axiomatized/bounded asymptotic, mirroring the parent's Part 2.
Do NOT route through Mathlib `GenContFract` (DE2).
