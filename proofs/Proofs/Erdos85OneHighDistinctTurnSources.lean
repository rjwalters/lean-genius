import Proofs.Erdos85OneHighOddLabelCycleSources

/-! # Distinct matching-edge sources at a label-cycle turn -/

namespace Erdos85

open SimpleGraph

noncomputable section

private theorem consecutive_minMax_pairs_ne
    {L : Type*} [LinearOrder L] {a b c : L}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (min a b, max a b) ≠ (min b c, max b c) := by
  intro hpair
  rcases le_total a b with habLe | hbaLe <;>
    rcases le_total b c with hbcLe | hcbLe
  · rw [min_eq_left habLe, max_eq_right habLe,
      min_eq_left hbcLe, max_eq_right hbcLe] at hpair
    exact hab (Prod.mk.inj hpair).1
  · rw [min_eq_left habLe, max_eq_right habLe,
      min_eq_right hcbLe, max_eq_left hcbLe] at hpair
    exact hac (Prod.mk.inj hpair).1
  · rw [min_eq_right hbaLe, max_eq_left hbaLe,
      min_eq_left hbcLe, max_eq_right hbcLe] at hpair
    exact hac (Prod.mk.inj hpair).2
  · rw [min_eq_right hbaLe, max_eq_left hbaLe,
      min_eq_right hcbLe, max_eq_left hcbLe] at hpair
    exact hbc (Prod.mk.inj hpair).1

/-- Exact key decorations of consecutive darts at a three-distinct-vertex
turn cannot select the same canonical matching-edge source. -/
theorem oneHigh_sourceColoring_cyclic_turn_sources_ne
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    {H : SimpleGraph {z : V // z ∈ G.neighborSet v}}
    {l : {z : V // z ∈ G.neighborSet v}} {c : H.Walk l l}
    (hc : c.IsCycle)
    (mate : OneHighAllMatchedVertices G v → OneHighAllMatchedVertices G v)
    (label : OneHighAllMatchedVertices G v →
      {z : V // z ∈ G.neighborSet v})
    (source : Fin c.length → OneHighAllMatchedVertices G v)
    (hkey : ∀ i : Fin c.length,
      exchangedMissPairKey mate label (source i) =
        (min (c.getVert i.1) (c.getVert (i.1 + 1)),
          max (c.getVert i.1) (c.getVert (i.1 + 1))))
    (i : Fin c.length)
    (hab : c.getVert i.1 ≠
      c.getVert (oneHighCycleNext c hc i).1)
    (hbc : c.getVert (oneHighCycleNext c hc i).1 ≠
      c.getVert
        (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)
    (hac : c.getVert i.1 ≠
      c.getVert
        (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1) :
    source i ≠ source (oneHighCycleNext c hc i) := by
  let j := oneHighCycleNext c hc i
  let k := oneHighCycleNext c hc j
  have hkeyI := hkey i
  have hkeyJ := hkey j
  rw [← getVert_oneHighCycleNext c hc i] at hkeyI
  rw [← getVert_oneHighCycleNext c hc j] at hkeyJ
  intro hs
  have heq := congrArg (exchangedMissPairKey mate label) hs
  rw [hkeyI, hkeyJ] at heq
  exact consecutive_minMax_pairs_ne hab hbc hac heq

end

end Erdos85
