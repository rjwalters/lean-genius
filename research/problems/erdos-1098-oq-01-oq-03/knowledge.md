# Knowledge Base: erdos-1098-oq-01-oq-03

Neumann's theorem: `ω(Γ(G)) finite ⟺ [G : Z(G)] finite`. File:
`proofs/Proofs/Erdos1098OQ01OQ03.lean`.

## State (mature, COMPLETE)

- Easy direction fully proved with sharp bound: `clique_card_le_index`,
  `bounded_cliques_of_finite_index` (ω ≤ [G:Z(G)]).
- Hard direction is the single axiom `neumann_hard_direction`
  (`BoundedCliques G → (center G).index ≠ 0`, B. H. Neumann 1976).
- Prior session (researcher-10) localized the axiom's residual content to a
  finite-index core `H = ⋂_{a∈T} C_G(a)` via `center_finiteIndex_iff_relIndex_core`
  and the index tower `Subgroup.relIndex_mul_index`. That is the optimal
  localization; it does not remove the axiom.

## Axiom-elimination terminus (assessed 07-08, researcher-1)

**The axiom is NOT eliminable with current Mathlib.** The natural endgame is
`Subgroup.index_center_le_pow` + the instance `Subgroup.finiteIndex_center`
(`Mathlib/GroupTheory/Commutator/Finite.lean:54`), which give
`Finite (commutatorSet G) → FiniteIndex (center G)`. Two independent obstructions:

1. **The Mathlib instance requires `[Group.FG G]`.** Neumann's theorem is stated
   for *arbitrary* groups (no finite-generation hypothesis), so even the
   finite-commutatorSet ⟹ finite-index-center step is unavailable in the
   generality this problem needs. There is no non-FG version of
   `finiteIndex_center` in Mathlib (checked GroupTheory/{Commutator/Finite,
   Schreier, Transfer}).
2. **The remaining gap `BoundedCliques G → Finite (commutatorSet G)` IS the deep
   BFC content of Neumann's theorem itself** — bounded pairwise-non-commuting
   sets ⟹ finitely many commutator values. Proving it is not a Mathlib lookup;
   it is the whole theorem. (Confirmed by researcher-10; re-confirmed here.)

**Do not reclaim for axiom elimination.** Adding further lemmas on top of the
axiom is scaffolding, not formalization. A genuine de-axiomatization would
require either (a) a Mathlib PR giving `Finite (commutatorSet G) → FiniteIndex
(center G)` without `Group.FG`, or (b) a full Lean development of Neumann's
covering argument (BFC ⟹ finite commutatorSet), each ~hundreds of lines.

## Tangential (not pursued — does not advance the axiom)

- `Finite (commutatorSet G) ↔ (center G).index ≠ 0` holds for FG groups
  (forward = `finiteIndex_center`, reverse = cosets-mod-Z argument), but it is
  orthogonal to the open direction and gated by the same FG restriction.
