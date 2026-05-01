# Research State: brouwer-fixed-point-oq-04-oq-02-incomplete-01

## Current State
**Phase**: RESOLVED — original axiom now a theorem (axiom moved upstream, not eliminated)
**Since**: 2026-04-27T18:25:00Z
**Iteration**: 2

## Current Focus

The original goal was to prove `axiom brouwer_product_simplex` in
`proofs/Proofs/BrouwerFixedPointOQ04OQ02.lean`, eliminating one assumption from the
parent gallery entry. **Inspecting the current Lean file at line 457 confirms that
this axiom has already been promoted to a theorem** (`theorem brouwer_product_simplex`,
proved from `brouwer_pi_compact_convex`). The file's own header (lines 34, 50)
documents this promotion: "The original `axiom brouwer_product_simplex` has been
replaced by a THEOREM that derives from `brouwer_pi_compact_convex`."

**Local axiom count: 0. Local sorry count: 0.** Verified by `grep -c "^axiom "`
returning 0 and a comment-stripped `sorry` count returning 0.

## Why parent meta still shows axiomCount: 1

`BrouwerFixedPointOQ04OQ02.lean` imports `Proofs.BrouwerFixedPointOQ04`, which
contains `axiom brouwer_pi_compact_convex` (the general Brouwer FPT for products of
compact convex sets). The 1 axiom counted in
`src/data/proofs/brouwer-fixed-point-oq-04-oq-02/meta.json` is this **inherited
import-chain axiom**, not the originally-targeted `brouwer_product_simplex`.

The metadata is therefore **internally consistent**:
- Parent `axiomCount: 1` correctly counts the inherited `brouwer_pi_compact_convex`.
- Parent `status: axiomatized` is correct because of this inherited axiom.
- Parent `badge: axiom` is correct.

## What this means for the incomplete-01 subproblem

The incomplete-01 subproblem's specific goal (eliminate `brouwer_product_simplex`)
**has been achieved**. The remaining `brouwer_pi_compact_convex` is a *different*
axiom that lives in a *different* file and corresponds to its own incomplete sub-
problem (potentially `brouwer-fixed-point-oq-04-incomplete-XX` if such exists).

Recommended pool action: **mark this incomplete-01 entry as `completed`** since
its specific axiom-elimination target has been met by a prior session. Future axiom-
removal effort on the Brouwer chain should target `brouwer_pi_compact_convex` in
`BrouwerFixedPointOQ04.lean`, not `brouwer_product_simplex` (already a theorem).

## Mathlib API Notes (Mathlib 4.26.0, for the next-level axiom)

If a future researcher targets `brouwer_pi_compact_convex` (the remaining inherited
axiom), the Mathlib bridge is:

| Symbol | Use |
|---|---|
| `Mathlib.Topology.MetricSpace.HausdorffDistance` (etc.) | Possibly Brouwer FPT for compact convex subsets of ℝⁿ |
| `Mathlib.Analysis.Convex.Combination` | Convex combinations |
| `Mathlib.Analysis.InnerProductSpace.PiL2` | Used: ∏ᵢ ℝ^kᵢ as Euclidean space |

A direct grep for `BrouwerFixedPoint` / `brouwer_fixed_point` in Mathlib returns
no top-level theorem matching the general compact-convex case in finite dimensions.
The `brouwer_pi_compact_convex` axiom likely needs to either be derived from
Mathlib's lower-dimensional Brouwer (if any) or formalized from Sperner's lemma —
which is itself the subject of the active marquee Sperner pipeline (per project
memory). Once Sperner lands, Brouwer FPT for compact convex sets follows as a
standard derivation.

## Blockers

None for this incomplete-01 entry — the goal is achieved and the metadata is
already correct. (Future Brouwer-chain axiom work is blocked on the upstream
Sperner pipeline.)

## Next Action

1. **Mark candidate-pool entry as `completed`**: this incomplete-01 problem's
   specific axiom-elimination target has been met.
2. (Optional, for a future session) If a separate `incomplete-02` entry exists
   for `brouwer_pi_compact_convex`, that is where to target next-level axiom work.
3. (Long-term) Once the marquee Sperner pipeline lands, derive
   `brouwer_pi_compact_convex` from Sperner's lemma and Brouwer's classical proof
   route, eliminating the last axiom in the Brouwer-Nash chain.

## Attempt Counts
- Total attempts: 1 (current-state verification, no code changes needed)
- Current approach attempts: 1
- Approaches tried: 1 (re-verification — confirmed axiom is now a theorem,
  recommended pool-status update to `completed`)
