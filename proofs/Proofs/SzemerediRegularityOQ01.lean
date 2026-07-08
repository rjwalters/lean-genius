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
  * `edgeDensity_compl` — **complement transfer**: for disjoint nonempty `A, B`,
    `d_{Gᶜ}(A, B) = 1 − d_G(A, B)`, via Mathlib's
    `SimpleGraph.edgeDensity_add_edgeDensity_compl` and the gallery bridge.
  * `edgeDensity_mem_Icc` — the range is packaged as a single membership
    `d(A, B) ∈ Set.Icc 0 1` for downstream positivity/interval reasoning.
  * `isEpsilonRegular_compl` — **complement regularity transfer**: for `0 < eps`
    and disjoint nonempty `A, B`, the pair is ε-regular in `Gᶜ` iff in `G`.  The
    ε-threshold forces every witness nonempty (empty witnesses cannot meet
    `|A'| ≥ eps·|A| > 0`), so `edgeDensity_compl` applies uniformly and the two
    density gaps agree in absolute value.

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

/-- **Complement transfer of edge density.**  For *disjoint*, nonempty vertex sets
    `A` and `B`, every cross pair is either a `G`-edge or a `Gᶜ`-edge (disjointness
    rules out the diagonal `a = b`), so the two densities are complementary:

        d_{Gᶜ}(A, B) = 1 − d_G(A, B).

    Proved by transporting both gallery densities to Mathlib via `edgeDensity_eq_mathlib`
    and invoking `SimpleGraph.edgeDensity_add_edgeDensity_compl`.  This is the density
    half of "regularity passes to the complement graph": the density *gap* on any
    disjoint sub-pair is preserved (`|d_{Gᶜ} − d_{Gᶜ}| = |d_G − d_G|`). -/
theorem edgeDensity_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty) (h : Disjoint A B) :
    edgeDensity Gᶜ A B = 1 - edgeDensity G A B := by
  have hsum := G.edgeDensity_add_edgeDensity_compl hA hB h
  rw [edgeDensity_eq_mathlib, edgeDensity_eq_mathlib]
  linarith [hsum]

/-- **Edge density lies in `[0, 1]`.**  Packages `edgeDensity_nonneg` and
    `edgeDensity_le_one` into a single interval membership, convenient for
    downstream positivity and `Set.Icc` reasoning. -/
theorem edgeDensity_mem_Icc (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : edgeDensity G A B ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨edgeDensity_nonneg G A B, edgeDensity_le_one G A B⟩

/-- **Complement regularity transfer.**  For a positive parameter `eps` and
    *disjoint*, nonempty vertex sets `A, B`, the pair `(A, B)` is ε-regular in the
    complement graph `Gᶜ` iff it is ε-regular in `G`:

        `IsEpsilonRegular Gᶜ eps A B ↔ IsEpsilonRegular G eps A B`.

    This upgrades the density identity `edgeDensity_compl` (`d_{Gᶜ} = 1 − d_G` on
    disjoint nonempty pairs) to the full ε-regularity predicate.  The subtlety
    flagged as a follow-up — that the ε-regularity witnesses `A' ⊆ A`, `B' ⊆ B`
    could be *empty*, where `edgeDensity_compl` does not apply — dissolves once
    `0 < eps`: a witness must satisfy `|A'| ≥ eps·|A| > 0` (as `A` is nonempty),
    forcing `A'` (and likewise `B'`) nonempty.  Every witness pair is therefore
    disjoint (subsets of the disjoint `A, B`) and nonempty, so `edgeDensity_compl`
    applies uniformly and the two density gaps agree in absolute value:

        `|d_{Gᶜ}(A', B') − d_{Gᶜ}(A, B)| = |d_G(A', B') − d_G(A, B)|`,

    since `(1 − x) − (1 − y) = −(x − y)`.  Both directions of the iff are then a
    single rewrite along this equality. -/
theorem isEpsilonRegular_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B) :
    IsEpsilonRegular Gᶜ eps A B ↔ IsEpsilonRegular G eps A B := by
  -- A witness meeting the ε-threshold against a nonempty set is itself nonempty.
  have hpos : ∀ S T : Finset V, T.Nonempty → (S.card : ℚ) ≥ eps * T.card →
      S.Nonempty := by
    intro S T hT hc
    rw [← Finset.card_pos]
    have h1 : (0 : ℚ) < eps * T.card :=
      mul_pos heps (by exact_mod_cast Finset.card_pos.mpr hT)
    exact_mod_cast lt_of_lt_of_le h1 hc
  -- On every valid witness pair the two density gaps have equal absolute value.
  have main : ∀ A' B' : Finset V, A' ⊆ A → B' ⊆ B →
      (A'.card : ℚ) ≥ eps * A.card → (B'.card : ℚ) ≥ eps * B.card →
      |edgeDensity Gᶜ A' B' - edgeDensity Gᶜ A B|
        = |edgeDensity G A' B' - edgeDensity G A B| := by
    intro A' B' hA' hB' hcA' hcB'
    have hA'ne : A'.Nonempty := hpos A' A hA hcA'
    have hB'ne : B'.Nonempty := hpos B' B hB hcB'
    have hdisj : Disjoint A' B' := hAB.mono hA' hB'
    rw [edgeDensity_compl G hA'ne hB'ne hdisj, edgeDensity_compl G hA hB hAB]
    have hrw : (1 - edgeDensity G A' B') - (1 - edgeDensity G A B)
        = -(edgeDensity G A' B' - edgeDensity G A B) := by ring
    rw [hrw, abs_neg]
  constructor
  · intro h A' B' hA' hB' hcA' hcB'
    rw [← main A' B' hA' hB' hcA' hcB']
    exact h A' B' hA' hB' hcA' hcB'
  · intro h A' B' hA' hB' hcA' hcB'
    rw [main A' B' hA' hB' hcA' hcB']
    exact h A' B' hA' hB' hcA' hcB'

end Szemeredi.Regularity.OQ01
