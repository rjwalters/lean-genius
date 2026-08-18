import Proofs.Erdos85PlateauExcessStructure
import Proofs.Erdos85PositiveExcessLocalParity

/-!
# Excess parity inside an odd-degree plateau core

This file wires the uniform triangle-free-edge handshake obstruction into the
plateau reduction.  Below `d²`, an odd-degree plateau core already carries a
`PositiveExcessPlateauData` package; its excess must be odd.  Consequently the
remaining odd-degree plateau band consists only of odd excess strata.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The excess stored in odd-degree positive-excess plateau data is odd. -/
theorem PositiveExcessPlateauData.excess_odd
    {m d e : ℕ} (hdata : PositiveExcessPlateauData m d e)
    (hodd : Odd d) : Odd e := by
  rcases hdata with
    ⟨hme, _he, G, hdec, hfree, hreg, _hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  apply excess_odd_of_odd_degree_regular G hfree hodd hreg
  simpa [hme]

/-- **Odd plateau-band parity package.**  Every odd-degree plateau core below
`d²` has a positive-excess realization with odd excess `e ≤ d-4`. -/
theorem C4PlateauCore.exists_odd_positiveExcessData
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d) (hodd : Odd d)
    (hcore : C4PlateauCore m d) (hsize : m < d * d) :
    ∃ e, Odd e ∧ PositiveExcessPlateauData m d e := by
  obtain ⟨e, hdata⟩ :=
    hcore.exists_positiveExcessData_of_odd hm hd hodd hsize
  exact ⟨e, hdata.excess_odd hodd, hdata⟩

end

end Erdos85
