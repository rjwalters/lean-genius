/-
  Aristotle targets for Erdős Problem #631: List Chromatic Number of Planar Graphs
  Routine supporting lemmas for automated proof search.
  See Erdos631Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT theorems depending on sorry-defined concepts (listChromaticNumber, IsPlanar, IsOuterplanar)
  - NOT deep results about planar graphs or list coloring conjecture
  - Monotonicity of k-choosability: a well-defined predicate about list colorings
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)

  Included targets (1):
  - choosable_monotone_ari: IsKChoosable G k → IsKChoosable G (k+1)
    Proof: lists of size ≥ k+1 are in particular of size ≥ k, so apply k-choosability.
-/
import Proofs.Erdos631Problem
import Mathlib

namespace Erdos631Aristotle

open Erdos631

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Section 1: Monotonicity of k-Choosability

IsKChoosable G k says: for any color type C with lists of size ≥ k, a valid
list coloring exists. Since lists of size ≥ k+1 are in particular of size ≥ k,
k-choosability implies (k+1)-choosability.
-/

/-- k-choosability is monotone in k: k-choosable implies (k+1)-choosable.
If every list assignment with lists of size ≥ k admits a list coloring, then
so does every list assignment with lists of size ≥ k+1, because the latter
lists are also of size ≥ k. -/
theorem choosable_monotone_ari (G : SimpleGraph V) (k : ℕ) :
    IsKChoosable G k → IsKChoosable G (k + 1) := by
  sorry

end Erdos631Aristotle
