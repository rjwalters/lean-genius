import Proofs.Erdos85OneHighOddCycleBridge

/-! # Length classification for odd label-support cycles -/

namespace Erdos85

open SimpleGraph

/-- A simple cycle cannot be longer than its finite vertex type. -/
theorem IsCycle.length_le_fintype_card
    {V : Type*} [Fintype V] {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) :
    c.length ≤ Fintype.card V := by
  have h := hc.support_nodup.length_le_card
  rw [List.length_tail, c.length_support] at h
  exact h

/-- Every odd-support label cycle in the degree-eight one-high setting has
one of the six possible lengths `3,4,5,6,7,8`. -/
theorem oneHigh_oddLabelCycle_length_cases
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (hv : G.degree v = 8)
    (m : {z : V // z ∈ G.neighborSet v} ×
      {z : V // z ∈ G.neighborSet v} → ℕ)
    {l : {z : V // z ∈ G.neighborSet v}}
    {c : (oddExchangedKeyLabelGraph m).Walk l l}
    (hc : c.IsCycle) :
    c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨
      c.length = 6 ∨ c.length = 7 ∨ c.length = 8 := by
  have hlo : 3 ≤ c.length := hc.three_le_length
  have hhi : c.length ≤ 8 := by
    have hcard := IsCycle.length_le_fintype_card hc
    rw [SimpleGraph.card_neighborSet_eq_degree, hv] at hcard
    exact hcard
  omega

end Erdos85
