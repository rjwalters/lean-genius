/-
  Szemerédi Regularity Lemma — OQ-01: symmetry of edge density and ε-regularity

  The gallery file `SzemerediRegularity.lean` (bridged to Mathlib's
  `szemeredi_regularity`) develops the edge density `edgeDensity G A B` and the
  ε-regularity predicate `IsEpsilonRegular G eps A B`, but never records the basic
  structural fact that both are *symmetric* in their two vertex-set arguments:
  for an undirected graph the pair `(A, B)` and the pair `(B, A)` carry the same
  edge density, and one is ε-regular iff the other is.

  Standard textbook treatments state regularity for unordered pairs precisely
  because of this symmetry; this file supplies it formally.

  * `edgeDensity_comm`        — `d(A, B) = d(B, A)`, via the gallery's
    `edgeDensity_eq_mathlib` bridge and Mathlib's `SimpleGraph.edgeDensity_comm`.
  * `isEpsilonRegular_comm`   — `IsEpsilonRegular G ε A B ↔ IsEpsilonRegular G ε B A`:
    the ε-regularity witnesses `(A', B')` for one orientation are exactly the
    swapped witnesses for the other, and the density difference is unchanged by
    `edgeDensity_comm`.
  * `edgeDensity_empty_left` / `edgeDensity_empty_right` — the degenerate
    boundary values `d(∅, B) = d(A, ∅) = 0`.
  * `irregularPairs_swap_mem` — the set of ordered irregular pairs underlying
    `IsRegularPartition` is closed under swapping coordinates: irregularity is a
    symmetric relation on parts.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Szemerédi (1975); Komlós–Simonovits (1996).
-/

import Mathlib
import Proofs.SzemerediRegularity

namespace Szemeredi.Regularity.OQ01

open Classical Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Symmetry of edge density.**  For an undirected graph the edge density is
    unchanged by swapping the two vertex sets: `d(A, B) = d(B, A)`.  Proved by
    transporting along the gallery's `edgeDensity_eq_mathlib` bridge to Mathlib's
    `SimpleGraph.edgeDensity`, which is symmetric (`G.symm`). -/
theorem edgeDensity_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeDensity G A B = edgeDensity G B A := by
  rw [edgeDensity_eq_mathlib, edgeDensity_eq_mathlib, G.edgeDensity_comm]

/-- **Symmetry of ε-regularity.**  `IsEpsilonRegular G ε A B` holds iff
    `IsEpsilonRegular G ε B A`.  A witness `(A', B')` for the `(B, A)` orientation
    becomes the witness `(B', A')` for `(A, B)`, and the density difference
    `|d(A', B') − d(B, A)|` equals `|d(B', A') − d(A, B)|` by `edgeDensity_comm`. -/
theorem isEpsilonRegular_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    IsEpsilonRegular G eps A B ↔ IsEpsilonRegular G eps B A := by
  -- One implication suffices by symmetry of the statement.
  have key : ∀ X Y : Finset V, IsEpsilonRegular G eps X Y →
      IsEpsilonRegular G eps Y X := by
    intro X Y h A' B' hA' hB' hcA' hcB'
    have hxy := h B' A' hB' hA' hcB' hcA'
    rwa [edgeDensity_comm G B' A', edgeDensity_comm G X Y] at hxy
  exact ⟨key A B, key B A⟩

/-- The empty left set has zero edge density. -/
theorem edgeDensity_empty_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) : edgeDensity G ∅ B = 0 := by
  simp [edgeDensity]

/-- The empty right set has zero edge density. -/
theorem edgeDensity_empty_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : edgeDensity G A ∅ = 0 := by
  simp [edgeDensity]

/-- **Irregularity is a symmetric relation on parts.**  The ordered-pair set that
    `IsRegularPartition` thresholds — distinct parts that fail to be ε-regular —
    is closed under swapping coordinates.  Combined with `isEpsilonRegular_comm`,
    this shows the irregular pairs come in matched `(P, Q)`/`(Q, P)` transpositions. -/
theorem irregularPairs_swap_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) (P Q : Finset V)
    (_hP : P ∈ parts) (_hQ : Q ∈ parts)
    (hpair : P ≠ Q ∧ ¬IsEpsilonRegular G eps P Q) :
    Q ≠ P ∧ ¬IsEpsilonRegular G eps Q P := by
  refine ⟨fun h => hpair.1 h.symm, ?_⟩
  rw [isEpsilonRegular_comm]
  exact hpair.2

end Szemeredi.Regularity.OQ01
