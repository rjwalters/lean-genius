# Current State

**Phase**: OBSERVE → ORIENT (S1 completed)
**Since**: 2026-05-11T22:30:00Z
**Iteration**: 1

## Current Focus

S1 OBSERVE survey (researcher-1, 2026-05-11): mathematical
specification + Mathlib gap inventory for the algorithmic
Szemerédi target.

Decoupling the constructive partition build in
`Proofs/SzemerediRegularity.lean:436` (`regularity_lemma_strong`,
opens `Classical`) from `Classical.choice` via the
Alon-Duke-Lefmann-Rödl-Yuster 1994 decidable surrogate for
`IsEpsilonRegular`.

## Active Approach

Three-target hierarchy:

- **Target A** — decidable surrogate `IsWitnessRegular G eps A B`
  that implies `IsEpsilonRegular G eps A B` (with a slack
  constant if needed). The surrogate quantifies over a specific
  finite family `S(A, G, B)` of subsets, polynomial in `|V|`.
- **Target B** — constructive witness extraction
  `witnessOfIrregular : ¬ IsWitnessRegular G eps A B → Σ' A' B', …`
  giving explicit subsets for irregular pairs.
- **Target C** — `def findRegularPartition (eps : ℚ) (G : SimpleGraph V) :
  Finset (Finset V)`, replacing the existential
  `regularity_lemma_strong` with a computable function via
  iterative refinement using `witnessOfIrregular`.

## Blockers

None for S2 (definitions + one-direction implication).

For S4 (partition refactor) the parent file's `Classical.choice`
usage at `SzemerediRegularity.lean:436` must be carefully
rewritten — this is a localized change but touches a 50-line
proof.

For S5 (Mathlib bridge): Mathlib's `SimpleGraph.szemeredi_regularity`
returns an existential; bridging requires extra glue work that is
worth deferring until S4 lands.

## Next Action

**S2 (next iteration)**: scaffold
`proofs/Proofs/SzemerediCoreOQ04.lean`.

Concrete deliverables:

1. `IsWitnessRegular G eps A B` — decidable surrogate. Quantifies
   over a specific finite family `S(A, G, B) : Finset (Finset V)`
   constructed from the adjacency pattern. The minimal viable
   choice is the family of "ε-grid neighborhoods"
   `{N(a) ∩ B | a ∈ A}` union complements — `|S| ≤ 2·|A|`, gives
   a decidable surrogate with slack constant 4.
2. `instance : Decidable (IsWitnessRegular G eps A B)` —
   automatic from the finite-quantifier form, requires only
   confirming the inner predicate is decidable (`Rat` arithmetic
   plus `Decidable` cardinality bounds).
3. `theorem witness_regular_implies_epsilon_regular`:
   `IsWitnessRegular G eps A B → IsEpsilonRegular G eps A B` —
   the directional implication that justifies replacing the
   universal-quantifier version with the decidable surrogate
   wherever IsEpsilonRegular is *consumed* (as opposed to
   *produced*) in the parent file.

Target: ~150 lines Lean, 0 sorries on the definition, ≤2 sorries
on the implication (flagged for Aristotle if the surrogate is the
strong "ε-grid" variant).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Open Questions for Future Iterations

- The exact slack constant in the ADLRY equivalence depends on
  the variant of the surrogate. **ε-grid** (`{N(a) ∩ B}`) gives
  slack 4. **Hypergraph-defect** gives slack 1 (no slack) but
  requires a more elaborate definition. For S2 start with ε-grid
  and revisit if the slack causes problems downstream.

- Should the surrogate live in `SzemerediCore` or in a new
  `SzemerediCoreOQ04`? `SzemerediCore` would touch the parent
  module and is a refactor; new file is cleaner and matches the
  gallery's existing `OQ` convention. Go with new file.

- Does the constructive partition function (Target C) need to be
  `noncomputable` because of `ℚ` arithmetic? `ℚ` is `Computable`,
  so no — keep it computable. (Confirm via S4 build.)

- The Mathlib regularity-lemma signature is slightly different —
  uses `≥ M(ε)` rather than `card V ≥ M`. Bridge work in S5 can
  defer; S2–S4 only target the gallery's own
  `regularity_lemma_strong`.
