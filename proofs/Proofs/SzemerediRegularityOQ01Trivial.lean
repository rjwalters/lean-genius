/-
  Szemerédi Regularity Lemma — OQ-01 (companion): the trivial-regularity threshold

  The sibling file `SzemerediRegularityOQ01.lean` develops structural facts about
  edge density and ε-regularity — symmetry, complement transfer, and
  **monotonicity in the parameter** (`isEpsilonRegular_mono`,
  `card_irregularOrderedPairs_antitone`: larger `eps` is a weaker requirement, so
  the irregular-pair count is non-increasing).

  This companion pins down the *endpoint* of that monotonicity: once `eps ≥ 1` the
  ε-regularity condition is **vacuously true for every pair**.  The reason is
  purely quantitative — edge densities always lie in `[0, 1]`
  (`edgeDensity_mem_Icc`), so for any subsets `A' ⊆ A`, `B' ⊆ B` the density gap
  satisfies

      `|d(A', B') − d(A, B)| ≤ 1 ≤ eps`,

  independently of the size conditions.  Consequently no pair can be irregular and
  the irregular-pair set is empty:

  * `isEpsilonRegular_of_one_le` — `1 ≤ eps ⟹ IsEpsilonRegular G eps A B` for all
    `A, B` (the trivial-regularity threshold).
  * `irregularOrderedPairs_eq_empty_of_one_le` — `1 ≤ eps ⟹` the ordered
    irregular pairs of any partition form the empty set.
  * `card_irregularOrderedPairs_eq_zero_of_one_le` — its cardinality is `0`, the
    exact value the antitone bound `card_irregularOrderedPairs_antitone` decreases
    towards.

  This is the sharp upper endpoint complementing the sibling's monotone
  bookkeeping: every graph is trivially `1`-regular, so the interesting regime of
  the regularity lemma is `0 < eps < 1`.

  All results are fully machine-checked (0 axioms, 0 sorries).
-/

import Mathlib
import Proofs.SzemerediRegularityOQ01

/-
v4.31 migration note: the three trivial-regularity-threshold theorems
(`isEpsilonRegular_of_one_le`, `irregularOrderedPairs_eq_empty_of_one_le`,
`card_irregularOrderedPairs_eq_zero_of_one_le`) are now all provided by the
imported parent `Proofs.SzemerediRegularityOQ01` in the same namespace
`Szemeredi.Regularity.OQ01`. Re-declaring them here triggered v4.31's
"already declared" error, so this companion is reduced to an import shim; all
three lemmas remain available transitively through the parent import.
-/

namespace Szemeredi.Regularity.OQ01

open Classical Szemeredi.Core Szemeredi.Regularity

end Szemeredi.Regularity.OQ01
