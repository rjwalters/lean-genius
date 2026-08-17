import Proofs.Erdos85BinarySquareOrderReduction
import Proofs.Erdos85SquareOrderHighIncidence

/-! # High-vertex count reduction at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a normalized minimum-degree-eight `C₄`-free graph on 64 vertices,
the degree-nine sector has one of only seven possible even cardinalities.

Parity comes from the handshake identity `8³ + h ≡ 0 (mod 2)`.  For a
nonempty high sector, the partial-design Cauchy inequality specializes to
`h² + 25h ≤ 512`, hence `h ≤ 13`. -/
theorem orderSixtyFour_high_count_cases
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    let h := (squareOrderHighVertices G 8).card
    h = 0 ∨ h = 2 ∨ h = 4 ∨ h = 6 ∨ h = 8 ∨ h = 10 ∨ h = 12 := by
  let h := (squareOrderHighVertices G 8).card
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  have heven := squareOrder_even_cube_add_card_high
    G hfree (d := 8) (by norm_num) hmin hcover hcard
  have hbound : h ≤ 13 := by
    by_cases hzero : h = 0
    · omega
    · have hpos : 0 < h := Nat.pos_of_ne_zero hzero
      have hcauchy := squareOrder_high_count_polynomial_bound
        G hfree (d := 8) (by norm_num) hmin hcover hcard hpos
      change h * h + (3 * 8 + 1) * h ≤ 8 * 8 * 8 at hcauchy
      nlinarith
  change Even (8 * 8 * 8 + h) at heven
  rcases heven with ⟨q, hq⟩
  omega

/-- At order 64, let `k(x)` count the degree-nine neighbors of `x` and let
`h` be the total number of degree-nine vertices.  Every local high incidence
is at most four, while the first two global moments are exactly `9h` and
`h(h+8)`.  These identities are the finite socket for excluding the seven
high-count cases above. -/
theorem orderSixtyFour_high_incidence_moments
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    let H := squareOrderHighVertices G 8
    let k : Fin 64 → Nat := fun x => (G.neighborFinset x ∩ H).card
    (∀ x, k x ≤ 4) ∧
      (∑ x : Fin 64, k x) = 9 * H.card ∧
      (∑ x : Fin 64, (k x) ^ 2) = H.card * (H.card + 8) := by
  classical
  dsimp only
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (d := 8) (by norm_num) hmin hcover hcard x with hx | hx
    · have hk := squareOrder_two_mul_highNeighborCount_le_degree
        G hfree (d := 8) (by norm_num) hmin hcover hcard hx
      omega
    · have hxH : x ∈ squareOrderHighVertices G 8 := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
      have hk := squareOrder_highNeighborCount_eq_zero_of_high G hcover hxH
      omega
  · simpa using squareOrder_sum_highNeighborCount_eq G 8
  · simpa using squareOrder_sum_highNeighborCount_sq_eq
      G hfree (d := 8) (by norm_num) hmin hcover hcard

end

end Erdos85
