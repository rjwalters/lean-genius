import Proofs.Erdos85BinarySquareRegularCapstone
import Proofs.Erdos85BinarySquareAllOddBipartitePartsExclusion

/-! # The connected nonbipartite binary-square interface

This module pins the remaining `A-REG-NONBIP-q2k` branch as an exact Lean
proposition.  It deliberately supplies no mechanism for proving the
proposition: that mathematical step remains open.  The theorem below records
only the safe direction from the stronger existing `A-REG` interface.
-/

open SimpleGraph

namespace Erdos85

/-- **A-REG-NONBIP-q2k** as a proposition: at binary square order, no regular
C4-free candidate has a connected, nonbipartite second-order defect graph.

This is a named socket for the sole open structural branch, not a Lean axiom.
-/
def BinarySquareConnectedNonbipartiteExclusion : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ∀ (G : SimpleGraph (Fin (2 ^ k * 2 ^ k)))
      (_ : DecidableRel G.Adj),
      ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G →
      (∀ x, G.degree x = 2 ^ k) →
      (secondOrderDefectGraph G).Connected →
      ¬ (secondOrderDefectGraph G).IsBipartite →
      False

/-- The uniform closed reduction that justifies the `nonbipartite` hypothesis
in the branch socket: every defect component of a binary-square regular
candidate admits no two-colouring of its induced edges. -/
theorem binarySquare_twoPow_regular_no_bipartite_defectComponent
    {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin (2 ^ k * 2 ^ k))) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ¬ ∃ col : Fin (2 ^ k * 2 ^ k) → Bool,
      ∀ x y, x ∈ c.supp → y ∈ c.supp →
        (secondOrderDefectGraph G).Adj x y → col x ≠ col y := by
  classical
  intro hbip
  obtain ⟨col, hcol⟩ := hbip
  obtain ⟨m, hm, _hsum⟩ :=
    binarySquare_regular_exists_defectComponent_partition
      G hfree (q := 2 ^ k) (by
        calc
          3 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)
      hreg (by simp)
  have hq4 : 4 ∣ 2 ^ k := by
    simpa using Nat.pow_dvd_pow 2 (show 2 ≤ k by omega)
  exact binarySquare_regular_no_bipartite_defectComponent
    G hfree (q := 2 ^ k) (by
      calc
        3 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk)
    hq4 hreg (by simp) m hm c col hcol

/-- Literal adapter to the nonbipartite hypothesis used by the branch socket:
the entire second-order defect graph is not Mathlib-bipartite. -/
theorem binarySquare_twoPow_regular_defectGraph_not_bipartite
    {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin (2 ^ k * 2 ^ k))) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G)
    (hreg : ∀ x, G.degree x = 2 ^ k) :
    ¬ (secondOrderDefectGraph G).IsBipartite := by
  classical
  intro hbip
  obtain ⟨C⟩ := hbip
  let encode : Fin 2 → Bool := fun i => decide (i = 1)
  have hencode : Function.Injective encode := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [encode]
  let c := (secondOrderDefectGraph G).connectedComponentMk
    (0 : Fin (2 ^ k * 2 ^ k))
  apply binarySquare_twoPow_regular_no_bipartite_defectComponent
    hk G hfree hreg c
  refine ⟨fun x => encode (C x), ?_⟩
  intro x y _hx _hy hxy
  exact fun heq => C.valid hxy (hencode heq)

/-- The full regular exclusion implies its connected nonbipartite subcase.
No converse is asserted here: mixed nonbipartite partitions remain a sibling
open case, not a proved reduction to the connected socket. -/
theorem binarySquareConnectedNonbipartiteExclusion_of_regularExclusion
    (h : BinarySquareRegularExclusion) :
    BinarySquareConnectedNonbipartiteExclusion := by
  intro k hk G hdec hfree hreg _hconn _hnotbip
  exact h k hk ⟨G, hdec, hfree, hreg⟩

end Erdos85

#print axioms Erdos85.binarySquareConnectedNonbipartiteExclusion_of_regularExclusion
#print axioms Erdos85.binarySquare_twoPow_regular_no_bipartite_defectComponent
#print axioms Erdos85.binarySquare_twoPow_regular_defectGraph_not_bipartite
