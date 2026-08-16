import Proofs.Erdos85SquareOrderNonexistenceReduction
import Proofs.Erdos85SquareOrderHighIncidence

/-!
# Scalar census forced by a square-order tight minimizer

This packages the first uniform arithmetic consequences of the square-order
normal form.  If `h` is the number of degree-`d+1` vertices, handshake parity
fixes the parity of `d^3+h`; a nonempty high sector leaves at least `d+1` low
vertices and satisfies the high-incidence Cauchy polynomial.
-/

namespace Erdos85

open SimpleGraph

/-- The scalar conditions on the high sector used by the parametric
square-order nonexistence route. -/
def SquareOrderHighCensus (d h : Nat) : Prop :=
  Even (d * d * d + h) ∧
    h ≤ d * d ∧
    (h = 0 ∨
      d + 1 ≤ d * d - h ∧
      h * h + (3 * d + 1) * h ≤ d * d * d)

/-- Every tight minimizer has a high-sector cardinality satisfying the
uniform scalar census. -/
theorem squareOrderTightMinimizer_exists_highCensus
    {d : Nat} (hd : 2 ≤ d) (hminimizer : SquareOrderTightMinimizer d) :
    ∃ h, SquareOrderHighCensus d h := by
  classical
  rcases hminimizer with ⟨G, hdec, hfree, hmin, _hminimal, hcover⟩
  letI : DecidableRel G.Adj := hdec
  let H := squareOrderHighVertices G d
  refine ⟨H.card, ?_⟩
  have hcard : Fintype.card (Fin (d * d)) = d * d := by simp
  have hmindeg : ∀ x : Fin (d * d), d ≤ G.degree x := fun x =>
    hmin.trans (G.minDegree_le_degree x)
  have hparity := squareOrder_even_cube_add_card_high
    G hfree hd hmindeg (@hcover) hcard
  have htotal : H.card ≤ d * d := by
    have hle := Finset.card_le_card
      (show H ⊆ (Finset.univ : Finset (Fin (d * d))) by simp)
    simpa [H, hcard] using hle
  refine ⟨by simpa [H] using hparity, htotal, ?_⟩
  by_cases hzero : H.card = 0
  · exact Or.inl hzero
  · right
    have hpos : 0 < H.card := Nat.pos_of_ne_zero hzero
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hvdegree : G.degree v = d + 1 :=
      (Finset.mem_filter.mp hv).2
    have hneighborLow : G.neighborFinset v ⊆
        (Finset.univ : Finset (Fin (d * d))) \ H := by
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
      intro hxHigh
      have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp hx
      exact squareOrder_not_adj_degree_succ_of_tightEdgeCover
        G (@hcover) hvdegree (Finset.mem_filter.mp hxHigh).2 hvx
    have hlowCard := Finset.card_le_card hneighborLow
    have hlow : d + 1 ≤ d * d - H.card := by
      rw [G.card_neighborFinset_eq_degree, hvdegree,
        Finset.card_sdiff, Finset.card_univ, hcard] at hlowCard
      simpa only [Finset.inter_univ] using hlowCard
    have hpoly := squareOrder_high_count_polynomial_bound
      G hfree hd hmindeg (@hcover) hcard (by simpa [H] using hpos)
    exact ⟨hlow, by simpa [H] using hpoly⟩

/-- Consequently, eventual nonexistence of all arithmetically admissible
tight minimizers along powers of two is enough for the negative answer. -/
theorem not_erdos85Question_of_eventual_twoPower_no_censusMinimizer
    (hno : ∀ᶠ e in Filter.atTop,
      ¬ ∃ h, SquareOrderHighCensus (2 ^ e) h ∧
        SquareOrderTightMinimizer (2 ^ e)) :
    ¬ Erdos85Question := by
  apply not_erdos85Question_of_eventual_twoPower_no_tightMinimizer
  filter_upwards [hno, Filter.eventually_ge_atTop 1] with e hnone he htight
  obtain ⟨h, hcensus⟩ := squareOrderTightMinimizer_exists_highCensus
    (d := 2 ^ e) (by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) he) htight
  exact hnone ⟨h, hcensus, htight⟩

end Erdos85
