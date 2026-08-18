import Proofs.Erdos85ExcessOneKFourTerminal
import Proofs.Erdos85PlateauExcessParity

/-!
# Odd plateau excess starts at three

The `K₄` spectral terminal eliminates excess one at odd regular degree.
Combined with the parity of positive excess, this raises the first possible
odd-degree plateau stratum from `e = 1` to `e = 3`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- There is no odd-degree regular `C₄`-free graph at excess one. -/
theorem no_c4Free_regular_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) : False := by
  apply excessOne_KFour_defect_spectral_kill G hfree (by
    rcases hodd with ⟨k, hk⟩
    omega) hodd hreg hcard

/-- Odd-degree positive-excess plateau data cannot have excess one. -/
theorem PositiveExcessPlateauData.excess_ne_one_of_odd
    {m d e : ℕ} (hdata : PositiveExcessPlateauData m d e)
    (hd : 4 ≤ d) (hodd : Odd d) : e ≠ 1 := by
  intro he
  rcases hdata with
    ⟨hm, _heUpper, G, hdec, hfree, hreg, _hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  apply no_c4Free_regular_odd_excessOne G hfree hd hodd hreg
  simp only [Fintype.card_fin]
  omega

/-- The first possible positive excess at odd degree is at least three. -/
theorem PositiveExcessPlateauData.three_le_excess_of_odd
    {m d e : ℕ} (hdata : PositiveExcessPlateauData m d e)
    (hd : 4 ≤ d) (hodd : Odd d) : 3 ≤ e := by
  have heOdd : Odd e := hdata.excess_odd hodd
  have hne := hdata.excess_ne_one_of_odd hd hodd
  rcases heOdd with ⟨k, hk⟩
  omega

/-- Plateau-facing form: every odd-degree plateau core strictly below `d²`
has a positive odd excess in the interval `[3,d-4]`. -/
theorem C4PlateauCore.exists_odd_positiveExcessData_three_le
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d) (hodd : Odd d)
    (hcore : C4PlateauCore m d) (hsize : m < d * d) :
    ∃ e, Odd e ∧ 3 ≤ e ∧ PositiveExcessPlateauData m d e := by
  obtain ⟨e, heOdd, hdata⟩ :=
    hcore.exists_odd_positiveExcessData hm hd hodd hsize
  exact ⟨e, heOdd, hdata.three_le_excess_of_odd hd hodd, hdata⟩

end

end Erdos85
