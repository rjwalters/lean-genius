import Proofs.Erdos85EnergyMinimalEdgeCover
import Proofs.Erdos85EvenPlaneOrderExistence

/-!
# Normal form for square-order nonexistence

Every square-order witness has an energy-minimal spanning replacement whose
edges are covered by degree-`d` vertices.  This is precisely the hypothesis
used throughout the parametric square-order incidence and defect theory.
-/

namespace Erdos85

open SimpleGraph

def SquareOrderTightMinimizer (d : Nat) : Prop :=
  ∃ (G : SimpleGraph (Fin (d * d))) (_ : DecidableRel G.Adj),
    ¬ containsC4 (Fin (d * d)) G ∧
    d ≤ G.minDegree ∧
    IsDegreeSquareMinimizer G d ∧
    ∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d

theorem c4FreeMinDegreeWitness_square_iff_tightMinimizer
    {d : Nat} (hd : 2 ≤ d) :
    C4FreeMinDegreeWitness (d * d) d ↔ SquareOrderTightMinimizer d := by
  constructor
  · rintro ⟨G, hdec, hmin, hfree⟩
    letI : DecidableRel G.Adj := hdec
    haveI : Nonempty (Fin (d * d)) := ⟨⟨0, by nlinarith⟩⟩
    obtain ⟨H, hHdec, hHfree, hHmin, hminimal, hcover, _hsaturated⟩ :=
      exists_degreeSquareMinimizer_with_tightCover_and_slideSaturation
        G hfree hmin
    exact ⟨H, hHdec, hHfree, hHmin, hminimal, hcover⟩
  · rintro ⟨G, hdec, hfree, hmin, _hminimal, _hcover⟩
    exact ⟨G, hdec, hmin, hfree⟩

theorem no_square_witness_iff_no_tightMinimizer
    {d : Nat} (hd : 2 ≤ d) :
    (¬ C4FreeMinDegreeWitness (d * d) d) ↔
      ¬ SquareOrderTightMinimizer d := by
  exact not_congr (c4FreeMinDegreeWitness_square_iff_tightMinimizer hd)

/-- The characteristic-two negative route may therefore assume all the
energy-minimal, tight-edge-cover structure used by the square-order library. -/
theorem not_erdos85Question_of_eventual_twoPower_no_tightMinimizer
    (hno : ∀ᶠ e in Filter.atTop,
      ¬ SquareOrderTightMinimizer (2 ^ e)) :
    ¬ Erdos85Question := by
  apply not_erdos85Question_of_eventual_twoPower_square_nonexistence
  filter_upwards [hno, Filter.eventually_ge_atTop 1] with e hnone he
  exact (no_square_witness_iff_no_tightMinimizer
    (d := 2 ^ e) (by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) he)).2 hnone

end Erdos85
