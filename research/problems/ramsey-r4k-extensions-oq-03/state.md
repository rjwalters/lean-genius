# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 14 (PART XIV)

## Current Focus
Quantified the deletion window's growth (the direction flagged as the one genuine, non-
enumeration increment). Two axiom-free theorems in
`Proofs/RamseyR4kExtensionsOQ03Deletion.lean`:
- `deletionBound_mono_of_pred_subthreshold`: `deletionBound n k ≤ deletionBound (n+1) k`
  whenever `2·C(n,k−1) < 2^C(k,2)` — the deletion bound is nondecreasing in `n` exactly
  while the `(k−1)`-clique first moment stays below one quantum.
- `deletionBound_mono_of_unionFeasible`: same conclusion under `2·C(n,k) < 2^C(k,2)` and
  `C(n,k−1) ≤ C(n,k)`. Corollary: the deletion optimum lies at least as far out as (and,
  in the Ramsey regime, strictly beyond) the union optimum — the structural source of the
  alteration method's `≈ k` gain.

The engine is Pascal's rule `C(n+1,k) = C(n,k) + C(n,k−1)` (the exact binomial-ratio step)
plus a ℕ-floor "jump ≤ 1 per step" lemma; closed by `omega`. No `decide`, no probability.

## Active Approach
Elementary `Nat`-division monotonicity. docker-build clean (7744 jobs), Tier-A axiom-free
(`propext / Classical.choice / Quot.sound`).

## Attempt Count
- Total attempts: 14
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (VII), deletion method (VIII), k=7
  machine-checked witness + compile repair (IX), general M=1 gain theorem (X),
  avoidance_pos numeric premises (XI), k=8 witness via descFactorial (XII),
  general M-window unification theorem (XIII), deletion-window monotonicity via
  Pascal's rule (XIV)

## Blockers
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis. See sibling
  `lovasz-local-lemma-oq-01`.

## Next Action
The axiom-free line is now saturated: the deletion mechanism is stated at full generality
(`ramsey_deletion_window`, every M), with the window's *monotonic growth* now characterized
by the `(k−1)`-clique threshold (PART XIV), plus concrete k=6,7,8 witnesses. The only
remaining genuinely-mathematical increments both require the BLOCKED measure-theoretic LLL:
either (a) the `SymmetricLLLForRamsey` construction itself, or (b) a Stirling-based
*asymptotic* statement that the additive window width grows like a constant fraction of the
union value (needs real analysis / `Nat.choose` asymptotics beyond Pascal). Further concrete
k≥9 witnesses would be enumeration theater. Recommend releasing the claim; the natural next
worker should target the sibling `lovasz-local-lemma-oq-01` measure-theory core.
