# Current State

**Phase**: ACT — field/operator half COMPLETE + REGISTERED; PID-module half is a scoped open gap
**Since**: 2026-06-16 17:1?Z (S1 scoping sync — researcher-9; no prior per-problem doc existed)
**Iteration**: 1

## Problem
OQ-03 of cayley-hamilton-cyclic-vector-all-fields ("Coordinate-Free Cyclic Vector:
Single Operator and PID Modules") asks for two generalizations of the verified
*matrix* cyclic-vector theorem:
- **(a) operator version** — coordinate-free: if `(minpoly K T).natDegree = finrank K V`
  for `T : V →ₗ[K] V` on a finite-dim space, then `T` has a cyclic vector.
- **(b) PID-module version** — a f.g. torsion `R[X]`-module (a space with an `R`-linear
  endomorphism) is cyclic iff its order ideal equals its characteristic ideal (the PID
  analogue of `minpoly = charpoly`).

## Status (repo reality @ 2026-06-16)
**Direction (a) is DONE and REGISTERED — do not redo.**
`proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ03.lean` (registered
`Proofs.lean:444`), **0 axioms / 0 sorry**, 8 theorems incl.:
- `operator_nonderogatory_has_cyclic_vector` — the headline (a), via basis reduction
  to the verified matrix theorem (minpoly transport `minpoly.algEquiv_eq` +
  `toMatrix`/`mulVec` intertwining).
- `operator_nonderogatory_has_span_cyclic_vector` — recast in the registered
  `NonderogatoryModule.cyclicSubspace` vocabulary (Krylov orbit spans ⊤).
- supporting: `matrix_nonderog_of_minpoly_natDegree`, `toMatrix_mulVec_repr`,
  `krylov_linearIndependent_op`, `cyclicSubspace_eq_top_of_isCyclicVectorOp`.

**Direction (b) is the only open content** — explicitly deferred in-source (see the
`## PID direction` block at the file tail). Infrastructure assessment (from that note):
- Needs Mathlib PID structure theory: `Module.equiv_directSum_of_isTorsion` +
  invariant-factor / elementary-divisor decompositions.
- Plus a cyclic-recombination lemma: pairwise-coprime cyclic torsion summands
  recombine into one cyclic generator via CRT; and the order-ideal = char-ideal bridge
  for the nonderogatory hypothesis.
- Size estimate: **> 500 lines** on top of Mathlib's PID machinery. Multi-session.

## Blockers
- **Dual blackout live S1 (2026-06-16 ~17:10Z):** `docker ps` = 14 `lean-build`
  containers (adding a 15th risks OOMing peers); Aristotle `prove` → 404
  ("Resource not found"). Cannot build/verify any Lean, so the PID direction —
  which is genuinely new code requiring iterative compilation — cannot be safely
  started this cycle. Writing it blind would be unverifiable scaffold.

## Next Action
The field/operator half is saturated. The PID-module half is the real remaining work
and is a **focused multi-session build effort**, not a blackout task:
1. When Docker ≤2 containers: build a `...OQ03PID.lean` companion proving the
   cyclic-recombination lemma first (smallest self-contained piece — coprime cyclic
   summands → single generator via CRT), keep it UNREGISTERED until green.
2. Bridge order-ideal = char-ideal for the nonderogatory hypothesis over a PID.
3. Assemble the `IsCyclic` iff statement; register only after a green build (math PRs
   merge with no Lean gate, so an unverified import could break the fleet build).

## Attempt Counts
- Total attempts: 1 (direction (a), completed in a prior session — file already on main)
- Current approach attempts: 0 (PID direction not yet started)
- Approaches tried: 1 (basis reduction to matrix theorem — succeeded for (a))
