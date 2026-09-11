import Proofs.Erdos85DistanceLayers

/-!
# Odd-order obstruction below the minimum-degree square

Near-Moore regularity and the handshake parity identity rule out odd-order
C4-free graphs of odd minimum degree below the square threshold.
-/

namespace Erdos85

/-- An odd minimum degree cannot occur in a C4-free graph of odd order
strictly below its square: the near-Moore bound forces regularity. -/
theorem containsC4_of_odd_card_lt_minDegree_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hd : 2 ≤ d) (hodd : Odd d)
    (hmin : d ≤ G.minDegree)
    (hcardOdd : Odd (Fintype.card V))
    (hcard : Fintype.card V < d * d) :
    containsC4 V G := by
  by_contra hfree
  have hsub : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hthreshold : (d + 1) * (d - 1) + 1 = d * d := by
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree hd hmin
      (by simpa only [hthreshold] using hcard)
  have heven : Even (Fintype.card V) := by
    have h := G.even_card_odd_degree_vertices
    simpa [hreg, hodd] using h
  exact (Nat.not_even_iff_odd.mpr hcardOdd) heven

/-- The q=9 order79 case is impossible without any symmetry assumption. -/
theorem containsC4_of_card_seventyNine_minDegree_nine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 79)
    (hmin : 9 ≤ G.minDegree) :
    containsC4 V G := by
  apply containsC4_of_odd_card_lt_minDegree_square G (d := 9)
    (by norm_num) (by norm_num) hmin
  · rw [hcard]
    norm_num
  · rw [hcard]
    norm_num

end Erdos85
