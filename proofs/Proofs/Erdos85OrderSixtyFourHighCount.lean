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

/-- Convert bounded incidence moments into equations for the four positive
incidence multiplicities. -/
theorem orderSixtyFour_incidence_count_equations
    (k : Fin 64 → Nat) (hk : ∀ x, k x ≤ 4) :
    (∑ x : Fin 64, k x) =
        (Finset.univ.filter fun x => k x = 1).card +
        2 * (Finset.univ.filter fun x => k x = 2).card +
        3 * (Finset.univ.filter fun x => k x = 3).card +
        4 * (Finset.univ.filter fun x => k x = 4).card ∧
    (∑ x : Fin 64, (k x) ^ 2) =
        (Finset.univ.filter fun x => k x = 1).card +
        4 * (Finset.univ.filter fun x => k x = 2).card +
        9 * (Finset.univ.filter fun x => k x = 3).card +
        16 * (Finset.univ.filter fun x => k x = 4).card := by
  classical
  have hkform (x : Fin 64) : k x =
      (if k x = 1 then 1 else 0) +
      (if k x = 2 then 2 else 0) +
      (if k x = 3 then 3 else 0) +
      (if k x = 4 then 4 else 0) := by
    have hx := hk x
    interval_cases h : k x <;> simp [h]
  have hsqform (x : Fin 64) : (k x) ^ 2 =
      (if k x = 1 then 1 else 0) +
      (if k x = 2 then 4 else 0) +
      (if k x = 3 then 9 else 0) +
      (if k x = 4 then 16 else 0) := by
    have hx := hk x
    interval_cases h : k x <;> simp [h]
  constructor
  · calc
      (∑ x : Fin 64, k x) = ∑ x : Fin 64,
          ((if k x = 1 then 1 else 0) +
           (if k x = 2 then 2 else 0) +
           (if k x = 3 then 3 else 0) +
           (if k x = 4 then 4 else 0)) :=
        Finset.sum_congr rfl fun x _ => hkform x
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite, mul_comm]
  · calc
      (∑ x : Fin 64, (k x) ^ 2) = ∑ x : Fin 64,
          ((if k x = 1 then 1 else 0) +
           (if k x = 2 then 4 else 0) +
           (if k x = 3 then 9 else 0) +
           (if k x = 4 then 16 else 0)) :=
        Finset.sum_congr rfl fun x _ => hsqform x
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_ite, mul_comm]

/-- The four possible positive-incidence multiplicity profiles when the high
sector has cardinality four. -/
theorem orderSixtyFour_four_high_incidence_profiles
    (k : Fin 64 → Nat)
    (hk : ∀ x, k x ≤ 4)
    (hsum : (∑ x : Fin 64, k x) = 36)
    (hsq : (∑ x : Fin 64, (k x) ^ 2) = 48) :
    let n := fun i => (Finset.univ.filter fun x => k x = i).card
    (n 1 = 24 ∧ n 2 = 6 ∧ n 3 = 0 ∧ n 4 = 0) ∨
    (n 1 = 27 ∧ n 2 = 3 ∧ n 3 = 1 ∧ n 4 = 0) ∨
    (n 1 = 30 ∧ n 2 = 0 ∧ n 3 = 2 ∧ n 4 = 0) ∨
    (n 1 = 32 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 1) := by
  dsimp only
  have heq := orderSixtyFour_incidence_count_equations k hk
  have hn4 : (Finset.univ.filter fun x => k x = 4).card ≤ 1 := by omega
  interval_cases h4 : (Finset.univ.filter fun x => k x = 4).card
  · have hn3 : (Finset.univ.filter fun x => k x = 3).card ≤ 2 := by omega
    interval_cases h3 : (Finset.univ.filter fun x => k x = 3).card <;> omega
  · omega

/-- Graph-level specialization of the four-high profile inventory. -/
theorem orderSixtyFour_four_high_graph_profiles
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 4) :
    let H := squareOrderHighVertices G 8
    let k : Fin 64 → Nat := fun x => (G.neighborFinset x ∩ H).card
    let n := fun i => (Finset.univ.filter fun x => k x = i).card
    (n 1 = 24 ∧ n 2 = 6 ∧ n 3 = 0 ∧ n 4 = 0) ∨
    (n 1 = 27 ∧ n 2 = 3 ∧ n 3 = 1 ∧ n 4 = 0) ∨
    (n 1 = 30 ∧ n 2 = 0 ∧ n 3 = 2 ∧ n 4 = 0) ∨
    (n 1 = 32 ∧ n 2 = 0 ∧ n 3 = 0 ∧ n 4 = 1) := by
  classical
  dsimp only
  have hm := orderSixtyFour_high_incidence_moments G hfree hmin hcover
  dsimp only at hm
  apply orderSixtyFour_four_high_incidence_profiles
  · exact hm.1
  · simpa [hh] using hm.2.1
  · simpa [hh] using hm.2.2

/-- The numerical profile forced by the order-64 moments when there are two
high vertices: exactly one vertex sees both high vertices and exactly sixteen
vertices see one of them. -/
theorem orderSixtyFour_two_high_incidence_profile
    (k : Fin 64 → Nat)
    (hk : ∀ x, k x ≤ 4)
    (hsum : (∑ x : Fin 64, k x) = 18)
    (hsq : (∑ x : Fin 64, (k x) ^ 2) = 20) :
    (∀ x, k x ≤ 2) ∧
      (Finset.univ.filter fun x => k x = 2).card = 1 ∧
      (Finset.univ.filter fun x => k x = 1).card = 16 := by
  classical
  let t : Fin 64 → Nat := fun x => k x * (k x - 1)
  have hpoint (x : Fin 64) : (k x) ^ 2 = k x + t x := by
    have hx := hk x
    interval_cases h : k x <;> simp [t, h]
  have hdecomp : (∑ x : Fin 64, (k x) ^ 2) =
      (∑ x : Fin 64, k x) + ∑ x : Fin 64, t x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hpoint x
  have htsum : (∑ x : Fin 64, t x) = 2 := by omega
  have ht_le (x : Fin 64) : t x ≤ 2 := by
    have hx : t x ≤ ∑ y : Fin 64, t y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    omega
  have hk2 : ∀ x, k x ≤ 2 := by
    intro x
    have hx := hk x
    have ht := ht_le x
    interval_cases h : k x <;> simp [t, h] at ht ⊢
  have htform (x : Fin 64) : t x = if k x = 2 then 2 else 0 := by
    have hx := hk2 x
    interval_cases h : k x <;> simp [t, h]
  have hkform (x : Fin 64) : k x =
      (if k x = 2 then 2 else 0) + (if k x = 1 then 1 else 0) := by
    have hx := hk2 x
    interval_cases h : k x <;> simp [h]
  have htcard : (∑ x : Fin 64, t x) =
      2 * (Finset.univ.filter fun x => k x = 2).card := by
    simp_rw [htform]
    simp [Finset.sum_ite, mul_comm]
  have hkcard : (∑ x : Fin 64, k x) =
      2 * (Finset.univ.filter fun x => k x = 2).card +
        (Finset.univ.filter fun x => k x = 1).card := by
    calc
      (∑ x : Fin 64, k x) = ∑ x : Fin 64,
          ((if k x = 2 then 2 else 0) + (if k x = 1 then 1 else 0)) :=
        Finset.sum_congr rfl fun x _ => hkform x
      _ = (∑ x : Fin 64, if k x = 2 then 2 else 0) +
          ∑ x : Fin 64, if k x = 1 then 1 else 0 := Finset.sum_add_distrib
      _ = 2 * (Finset.univ.filter fun x => k x = 2).card +
          (Finset.univ.filter fun x => k x = 1).card := by
        simp [Finset.sum_ite, mul_comm]
  have hn2 : (Finset.univ.filter fun x => k x = 2).card = 1 := by omega
  refine ⟨hk2, hn2, ?_⟩
  omega

/-- Graph-level specialization of the two-high numerical profile. -/
theorem orderSixtyFour_two_high_graph_profile
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hh : (squareOrderHighVertices G 8).card = 2) :
    let H := squareOrderHighVertices G 8
    let k : Fin 64 → Nat := fun x => (G.neighborFinset x ∩ H).card
    (∀ x, k x ≤ 2) ∧
      (Finset.univ.filter fun x => k x = 2).card = 1 ∧
      (Finset.univ.filter fun x => k x = 1).card = 16 := by
  classical
  dsimp only
  have hm := orderSixtyFour_high_incidence_moments G hfree hmin hcover
  dsimp only at hm
  apply orderSixtyFour_two_high_incidence_profile
  · exact hm.1
  · simpa [hh] using hm.2.1
  · simpa [hh] using hm.2.2

end

end Erdos85
