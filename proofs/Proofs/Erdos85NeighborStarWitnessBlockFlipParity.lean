import Proofs.Erdos85NeighborStarFlipParity

/-!
# Flip parity over a block of witness labels

Summing the local neighbor-star activity/flip identity over a witness block
preserves parity.  For the residual-full witness block this is precisely the
count-level identity `(73rnz_cjibkzi)`.
-/

open SimpleGraph

namespace Erdos85

/-- Even form of the witness-block flip identity. -/
theorem even_sum_neighborStarFlipRepresentatives_iff_even_activityMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ y v, A.Adj y v → A.Adj y (mate y v))
    (hinvol : ∀ y v, A.Adj y v → mate y (mate y v) = v)
    (hfixed : ∀ y v, A.Adj y v → mate y v ≠ v)
    (R B : Finset V) :
    Even (∑ y ∈ R, (neighborStarFlipRepresentatives A mate y B).card) ↔
      Even (∑ y ∈ R, (A.neighborFinset y ∩ B).card) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert y R hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy,
        Nat.even_add, Nat.even_add,
        even_neighborStarFlipRepresentatives_iff_even_neighborSupport
          A mate hclosed hinvol hfixed y B,
        ih]

/-- **Witness-block activity equals flip parity (`73rnz_cjibkzi`).**  The
total number of `B`-crossing mate pairs carrying a witness label in `R` is
odd exactly when the total neighbor-star activity mass on `R` is odd. -/
theorem odd_sum_neighborStarFlipRepresentatives_iff_odd_activityMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ y v, A.Adj y v → A.Adj y (mate y v))
    (hinvol : ∀ y v, A.Adj y v → mate y (mate y v) = v)
    (hfixed : ∀ y v, A.Adj y v → mate y v ≠ v)
    (R B : Finset V) :
    Odd (∑ y ∈ R, (neighborStarFlipRepresentatives A mate y B).card) ↔
      Odd (∑ y ∈ R, (A.neighborFinset y ∩ B).card) := by
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, not_iff_not]
  exact even_sum_neighborStarFlipRepresentatives_iff_even_activityMass
    A mate hclosed hinvol hfixed R B

end Erdos85

#print axioms Erdos85.even_sum_neighborStarFlipRepresentatives_iff_even_activityMass
#print axioms Erdos85.odd_sum_neighborStarFlipRepresentatives_iff_odd_activityMass
