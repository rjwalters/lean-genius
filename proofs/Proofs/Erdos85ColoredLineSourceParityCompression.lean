import Proofs.Erdos85FinsetPairingWithParityLeftover
import Proofs.Erdos85BinaryCutGraphTwoPoleRoute

/-!
# Colored pole-line source compression

On an even-valent pole line, the zero coordinates of a binary potential pair
into two-ended relay columns with at most one leftover.  The leftover bit is
exactly the adjacency action of the potential at the pole, as asserted in
`(73rnz_cjic)`.
-/

open SimpleGraph

namespace Erdos85

/-- Neighbors on a pole line carrying potential value zero. -/
def f2ZeroNeighborSource
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (t : V → ZMod 2) (E : V) : Finset V :=
  (A.neighborFinset E).filter fun v => t v = 0

/-- On an even-valent line, zero-coordinate parity equals the adjacency
action on the one-coordinate support. -/
theorem f2ZeroNeighborSource_card_cast_eq_adjMatrix_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (t : V → ZMod 2) (E : V) (heven : Even (A.degree E)) :
    ((f2ZeroNeighborSource A t E).card : ZMod 2) =
      (A.adjMatrix (ZMod 2)).mulVec t E := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hdegreeZero : (A.degree E : ZMod 2) = 0 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk, Nat.cast_add]
    calc
      (k : ZMod 2) + k = 2 * k := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  calc
    ((f2ZeroNeighborSource A t E).card : ZMod 2) =
        ∑ v ∈ A.neighborFinset E, if t v = 0 then 1 else 0 := by
          simp [f2ZeroNeighborSource]
    _ = ∑ v ∈ A.neighborFinset E, (1 + t v) := by
      apply Finset.sum_congr rfl
      intro v _
      rcases hbinary (t v) with hv | hv
      · simp [hv]
      · simp only [hv, ↓reduceIte, zero_add]
        change (0 : ZMod 2) = 2
        exact htwo.symm
    _ = ((A.neighborFinset E).card : ZMod 2) +
        ∑ v ∈ A.neighborFinset E, t v := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ v ∈ A.neighborFinset E, t v := by
      rw [A.card_neighborFinset_eq_degree, hdegreeZero, zero_add]
    _ = (A.adjMatrix (ZMod 2)).mulVec t E := by
      rw [SimpleGraph.adjMatrix_mulVec_apply]

/-- **Colored line compression (`73rnz_cjic`).**  The zero-valued line
source has a pairable subsource and at most one owner leftover; the leftover
is present exactly when the adjacency action at the pole equals one. -/
theorem exists_coloredLine_pairing_with_owner_leftover
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (t : V → ZMod 2) (E : V) (heven : Even (A.degree E)) :
    ∃ R : Finset V, ∃ mate : V → V,
      R ⊆ f2ZeroNeighborSource A t E ∧
      (f2ZeroNeighborSource A t E \ R).card ≤ 1 ∧
      ((f2ZeroNeighborSource A t E \ R).card = 1 ↔
        (A.adjMatrix (ZMod 2)).mulVec t E = 1) ∧
      (∀ v ∈ R, mate v ∈ R) ∧
      (∀ v ∈ R, mate (mate v) = v) ∧
      (∀ v ∈ R, mate v ≠ v) := by
  obtain ⟨R, mate, hsub, hle, hleftover, hclosed, hinvol, hfree⟩ :=
    exists_pairable_subfinset_with_parity_leftover
      (f2ZeroNeighborSource A t E)
  refine ⟨R, mate, hsub, hle, ?_, hclosed, hinvol, hfree⟩
  rw [hleftover, ← ZMod.natCast_eq_one_iff_odd,
    f2ZeroNeighborSource_card_cast_eq_adjMatrix_mulVec A t E heven]

end Erdos85

#print axioms Erdos85.f2ZeroNeighborSource_card_cast_eq_adjMatrix_mulVec
#print axioms Erdos85.exists_coloredLine_pairing_with_owner_leftover
