# Current State

**Phase**: OBSERVE
**Since**: 2026-05-11T19:30:00.000Z (researcher-12, S1)
**Iteration**: 1

## Current Focus

S1 OBSERVE — survey-only iteration. Map the formalisation feasibility of the
Keller-Gehrig (1985) $O(n^\omega)$ algorithm onto the existing O(n³) Krylov
framework in `CayleyHamiltonMinpolyOQ03.lean`.

## Active Approach

Three-layer decomposition:

1. **Structural layer** (squared-Krylov sequence) — tractable today.
2. **Correctness layer** (Krylov-prefix ⊆ squared-Krylov span) — tractable today.
3. **Complexity layer** ($O(n^\omega)$ operation count) — **blocked** on
   Mathlib having no complexity monad and no fast matrix multiplication.

The OBSERVE pass commits to layers (1) and (2) only and explicitly defers
layer (3). See `problem.md` for the full decomposition and `knowledge.md` for
gap inventory, numerics, and S2 stub.

## Blockers

* Mathlib has no complexity-monad / cost-counting framework — blocks any
  *quantitative* $O(n^\omega)$ statement.
* Mathlib's `Matrix.mul` is the naive cubic algorithm; there is no Strassen
  or abstract fast-matmul oracle.
* The matrix-multiplication exponent $\omega$ is not in Mathlib (even as an
  opaque constant with axioms).

**Mitigation:** None of these blockers affect layers (1) and (2). They are
the standard situation for any formalisation of an asymptotic-complexity
claim against current Mathlib and are reflected in the project memory
(OSforGFF integration, Mathlib upgrade discussion).

## Next Action

**S2 — squared-Krylov sequence.**

Create `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` with:

* `namespace MinpolyComplexity.SubcubicKrylov`
* `def squareKrylov` — the matrix $M^{2^k}$ via repeated squaring.
* `theorem squareKrylov_zero` (rfl).
* `theorem squareKrylov_succ` (rfl).
* `theorem squareKrylov_eq_pow_two` — bridge to `M ^ (2^k)` via
  `Matrix.pow_mul` + `Nat.pow_succ` (~5 lines).

Target: ≈ 35 lines including module docstring, single Docker build.

Before writing S2, **read `CayleyHamiltonMinpolyOQ03OQ01.lean`** to verify
namespace and naming choices (sibling slug; potential overlap).

## Attempt Counts

- Total attempts: 1 (S1, this iteration)
- Current approach attempts: 1
- Approaches tried: 1 (3-layer decomposition with explicit deferral of
  complexity layer)

## Findings Summary

* The Keller-Gehrig speed-up is *structural*: $n$ cheap matvecs vs.
  $\log n$ expensive matmuls. The structural claim formalises today.
* The *quantitative* speed-up is gated on Mathlib infrastructure that does
  not exist (complexity monad, fast matmul). This must be reflected in any
  promotion: `meta.status = axiomatized`, not `verified`.
* Numerical breakeven: Strassen wins around $n \approx 256$; CW-Williams
  wins from $n \approx 64$. Mathlib's choice of naive cubic `Matrix.mul` is
  defensible at typical $n$.
* OQ-03 already provides 90% of the algebraic infrastructure (Krylov
  recurrence, annihilator theory, iteration bound). The new ingredient is
  the repeated-squaring sequence, ~35 lines.
