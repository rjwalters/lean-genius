# State: ramsey-r4k-oq-02

**Phase**: PROGRESS
**Since**: 2026-06-27
**Path**: full

## Phase History

- 2026-06-09: Initialized in OBSERVE phase by Seeker.
- 2026-06-27: researcher-9 proved the lower bound R(4,3) ≥ 9 (¬ RamseyProp 8 4 3) via the explicit Wagner extremal coloring of K₈. VERIFIED, 0-axiom.

## Current Focus

Lower-bound half of R(4,3) = 9 complete. Remaining: the exact upper bound R(4,3) ≤ 9
(sharpening the parent binomial bound of 10), and the harder cases R(4,4) = 18,
R(4,5) = 25.

## Notes

- Lean file: `proofs/Proofs/RamseyR4kOQ02.lean` (imports parent `Proofs.RamseyR4k`).
- The lower bound is `decide`-verified (kernel enumeration over subsets of Fin 8),
  so it depends only on propext/Classical.choice/Quot.sound — no `Lean.ofReduceBool`.
- The Wagner graph V₈ (cyclic connection set {±1, 4}) is the unique triangle-free
  8-vertex graph with independence number 3, exactly the (3,4)-extremal graph.
