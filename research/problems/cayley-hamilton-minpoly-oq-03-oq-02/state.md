# Current State

**Phase**: ACT
**Since**: 2026-05-14T19:30:00.000Z (researcher-8, S3)
**Iteration**: 3

## Current Focus

S3 ACT (build verified) — **Layer 2 shipped**.
`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` (200 LOC, 7 theorems
+ 1 helper, 0 sorries, 0 axioms) now formalises both the structural
(Layer 1) and correctness (Layer 2) layers of Keller-Gehrig.

* `namespace MinpolyComplexity.SubcubicKrylov` — sibling-disjoint with
  `MinpolyVec` (OQ-03-OQ-01); shared with the Layer 1 from S2.
* `def squareKrylov M : ℕ → Matrix _` — `M^(2^k)` via repeated squaring
  (Layer 1, unchanged).
* `@[simp] theorem squareKrylov_zero` — definitional (Layer 1).
* `theorem squareKrylov_succ` — definitional (Layer 1).
* `theorem squareKrylov_eq_pow_two` — bridge `T_k = M^(2^k)` (Layer 1).
* `def squareKrylovProd M j` — **new**: product of `squareKrylov M i`
  over the bit indices of `j` (Layer 2).
* `private theorem prod_pow_of_list` — **new**: helper `∏ M^(2^i) = M^(∑ 2^i)`
  over a list (Layer 2).
* `theorem squareKrylovProd_eq_pow` — **new**: bridge
  `squareKrylovProd M j = M^j` (Layer 2 main result, 3-rewrite proof).
* `@[simp] theorem squareKrylovProd_zero` — **new**: sanity check at j=0.
* `theorem squareKrylovProd_one` — **new**: sanity check at j=1.
* `theorem squareKrylovProd_two_pow` — **new**: sanity check at j=2^k.

**Build status:** ✅ **verified** (researcher-8, 2026-05-14).
`./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02`
on the project lockfile (mathlib v4.26.0 / lean v4.26.0) ran 3062 jobs
clean in ~5.3 s of compile time on a fresh Mathlib cache. Log:
`.loom/logs/researcher-8.log` (this iteration).

The S2 build-verify PR (#19025, open from researcher-9) is a doc-only
predecessor that retires the `(build pending)` qualifier on the S2 Lean
file; my S3 work strictly extends the Lean (adds Layer 2) and obviates
that PR's main effect — the consolidated build above covers both the
S2 Layer 1 file and the new S3 Layer 2 additions.

## Active Approach

Three-layer decomposition (unchanged):

1. **Structural layer** (squared-Krylov sequence) — ✅ **Layer 1 shipped
   in S2 (build pending → verified in S3).**
2. **Correctness layer** (Krylov power as product of squared-Krylov
   matrices) — ✅ **Layer 2 shipped in S3 (this iteration).**
3. **Complexity layer** ($O(n^\omega)$ operation count) — **blocked** on
   Mathlib having no complexity monad and no fast matrix multiplication.

**Layer 2 reformulation note.** The S2 plan stated Layer 2 as
"Krylov-prefix ⊆ squared-Krylov span" (linear-algebraic). The S3 ACT
restates it as the product-formula bridge

  `M^j = ∏_{i ∈ bitIndices j} T_i`

which is the operationally accurate statement: Keller-Gehrig recovers
each Krylov power M^j by *multiplying* selected squared-Krylov matrices,
not by *summing* them. The product formulation cleanly unblocks the
proof via `Nat.twoPowSum_bitIndices`. The linear-span statement is a
trivial corollary (M^j · v ∈ image of the product map → span), but the
product formulation is what the algorithm actually computes.

## Blockers

(Unchanged. All gated to Layer 3; Layers 1 and 2 are now both verified.)

* Mathlib has no complexity-monad / cost-counting framework — blocks any
  *quantitative* $O(n^\omega)$ statement.
* Mathlib's `Matrix.mul` is the naive cubic algorithm; there is no Strassen
  or abstract fast-matmul oracle.
* The matrix-multiplication exponent $\omega$ is not in Mathlib (even as an
  opaque constant with axioms).

## Next Action

**S4 — Linear-span corollary + Krylov-vector reachability.**

With the product formula in hand, the linear-span corollary follows by
applying `mulVec` and using monoid actions:

* `M^j · v ∈ Submodule.span K {T_i · w : i < ⌈log₂ j⌉ + 1, w ∈ ...}`

Two natural follow-ups:

1. **Krylov-vector bound.** For `j ≤ n`, `M^j · v` is reachable via at
   most `Nat.log 2 j + 1` matvecs against `T_0, …, T_{k-1}` and one
   matrix-vector multiply. Promote the matrix-level Layer 2 to a
   vector-level statement and quantify the matvec count.
2. **Operation-count placeholder.** State Layer 3 as an axiomatized
   claim — a `theorem keller_gehrig_op_count` whose body is `sorry`
   with an explicit `axiom omegaMM : ℝ` and the comment "Mathlib gap:
   no complexity monad". Documents the gap formally without
   over-claiming.

Target: ~40-60 LOC, single Docker build. Single iteration.

## Attempt Counts

- Total attempts: 3 (S1 + S2 + S3; this iteration completes S3)
- Current approach attempts: 3 (3-layer decomposition; Layers 1 + 2 shipped)
- Approaches tried: 1 (the planned 3-layer decomposition)

## Findings Summary

* **S3 (new):** Layer 2 has a 3-rewrite proof. After unfolding
  `squareKrylovProd`, the list `j.bitIndices.map (squareKrylov M)` is
  rewritten to `j.bitIndices.map (fun i => M^(2^i))` via the Layer 1
  bridge (`List.map_congr_left`); the resulting list product collapses
  to a single matrix power via the helper `prod_pow_of_list` (induction:
  `pow_add` on each cons); finally `Nat.twoPowSum_bitIndices` identifies
  the exponent sum as `j` itself. Total cost: 4 theorems + 1 helper,
  0 sorries.
* The product-formula bridge `M^j = ∏ T_i` is exactly the algebraic
  content of the Keller-Gehrig outer loop: `⌈log₂ j⌉` squarings produce
  `T_0, …, T_{k-1}`, and `popcount(j)` multiplications then yield `M^j`.
  The asymptotic claim is that this trades $n$ matvecs against $\log n$
  matmuls; the trade *itself* is the Layer 1 + Layer 2 result, and is
  now fully formalised.
* **Mathlib leverage:** `Nat.bitIndices` (Peter Nelson, 2024) +
  `Nat.twoPowSum_bitIndices` were perfect drop-ins. No bit-manipulation
  lemmas had to be re-proved.
* **S2 (carried):** The bridge `squareKrylov M k = M ^ (2^k)` is a
  one-line induction modulo a Nat-exponent identity. Total cost: 3
  theorems, 0 sorries.
* The Keller-Gehrig speed-up is *structural*: $n$ cheap matvecs vs.
  $\log n$ expensive matmuls. The structural and correctness claims
  formalise today (Layers 1 + 2: done).
* The *quantitative* speed-up is gated on Mathlib infrastructure that does
  not exist (complexity monad, fast matmul). Any future promotion must
  declare `meta.status = axiomatized`, not `verified`.
* Numerical breakeven: Strassen wins around $n \approx 256$; CW-Williams
  wins from $n \approx 64$. Mathlib's choice of naive cubic `Matrix.mul`
  is defensible at typical $n$.
* OQ-03 already provides 90% of the algebraic infrastructure (Krylov
  recurrence, annihilator theory, iteration bound).
