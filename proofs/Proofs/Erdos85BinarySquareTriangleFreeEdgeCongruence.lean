import Proofs.Erdos85FifthMomentBridge
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger
import Proofs.Erdos85BinarySquareRegularParity

/-!
# A binary square-order congruence for triangle-free edges

At order `q²` with regular degree `q = 2^k`, the cubic color partition and
handshaking give the exact formula

`#E(triangleFreeEdgeGraph G) = 2^(3k-1) - 3 * #triangles(G)`.

Thus the mod-three constraint found at order 64 is uniform in the binary
square-order parameter.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem reachable_induction_of_adj_closed_binarySquare
    {V : Type*} (D : SimpleGraph V) (P : V → Prop)
    (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- Exact binary square-order triangle-free edge ledger. -/
theorem binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k)) :
    ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) =
      (2 : ℤ) ^ (3 * k - 1) -
        3 * (adjacencyTriangleMinorFinset G).card := by
  have hcolor :=
    trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree_of_regular
      G hfree hreg
  rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees]
    at hcolor
  have htri := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
    G (by
      rw [hcard]
      have htwo : 2 ≤ 2 ^ k := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith)
  rw [htri] at hcolor
  have hhand := (triangleFreeEdgeGraph G).sum_degrees_eq_twice_card_edges
  have hhandZ :
      (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
        2 * ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) := by
    exact_mod_cast hhand
  have hpow :
      (2 : ℤ) ^ k * (2 : ℤ) ^ k * (2 : ℤ) ^ k =
        2 * (2 : ℤ) ^ (3 * k - 1) := by
    rw [← pow_add, ← pow_add,
      show k + k + k = (3 * k - 1) + 1 by omega, pow_succ]
    ring
  rw [hcard] at hcolor
  norm_num at hcolor
  rw [hpow] at hcolor
  omega

/-- Congruence form: the triangle-free edge count differs from
`2^(3k-1)` by a multiple of three. -/
theorem binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k)) :
    ∃ z : ℤ,
      ((triangleFreeEdgeGraph G).edgeFinset.card : ℤ) =
        3 * z + (2 : ℤ) ^ (3 * k - 1) := by
  refine ⟨-((adjacencyTriangleMinorFinset G).card : ℤ), ?_⟩
  rw [binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
    G hfree hk hreg hcard]
  ring

/-- At every binary square order, the triangle-free edge graph is nonempty.
This is the uniform version of the order-64 necessity theorem. -/
theorem binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 1 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k)) :
    (triangleFreeEdgeGraph G).edgeFinset.Nonempty := by
  obtain ⟨z, hz⟩ :=
    binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
      G hfree hk hreg hcard
  by_contra hempty
  have hcardZero : (triangleFreeEdgeGraph G).edgeFinset.card = 0 := by
    rw [Finset.card_eq_zero]
    exact Finset.not_nonempty_iff_eq_empty.mp hempty
  have hzmod := congrArg (fun a : ℤ => (a : ZMod 3)) hz
  rw [hcardZero] at hzmod
  push_cast at hzmod
  have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [hthree, zero_mul, zero_add] at hzmod
  exact (pow_ne_zero (3 * k - 1) (by decide : (2 : ZMod 3) ≠ 0)) hzmod.symm

/-- Triangle-free degree two is constant on each connected component of the
internal ambient two-factor of a normalized size-two defect component. -/
theorem binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x y : c.supp)
    (hxy : (G.induce c.supp).Reachable x y) :
    (triangleFreeEdgeGraph G).degree x.1 = 2 ↔
      (triangleFreeEdgeGraph G).degree y.1 = 2 := by
  let H := G.induce c.supp
  have hstep : ∀ u v : c.supp, H.Adj u v →
      (triangleFreeEdgeGraph G).degree u.1 = 2 →
        (triangleFreeEdgeGraph G).degree v.1 = 2 := by
    intro u v huv hu
    exact
      (binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_adj
        G hfree hq hqEven hreg hcard c hc u v huv).mp hu
  constructor
  · exact reachable_induction_of_adj_closed_binarySquare H
      (fun u => (triangleFreeEdgeGraph G).degree u.1 = 2)
      hstep hxy
  · exact reachable_induction_of_adj_closed_binarySquare H
      (fun u => (triangleFreeEdgeGraph G).degree u.1 = 2)
      hstep hxy.symm

/-- In an all-size-two partition, the triangle-free graph is a disjoint union
of cycles on precisely the triangle-free-degree-two vertices.  Consequently
its edge count equals the order of that colored sector. -/
theorem binarySquare_regular_allSizeTwo_triangleFreeEdge_card_eq_colorOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = q * 2) :
    (triangleFreeEdgeGraph G).edgeFinset.card =
      ((Finset.univ : Finset V).filter fun x =>
        (triangleFreeEdgeGraph G).degree x = 2).card := by
  let T := triangleFreeEdgeGraph G
  let C := ((Finset.univ : Finset V).filter fun x => T.degree x = 2).card
  have hdegree : ∀ x : V, T.degree x = 0 ∨ T.degree x = 2 := by
    intro x
    let c := (secondOrderDefectGraph G).connectedComponentMk x
    exact binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree hq hqEven hreg hcard c (hall c)
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  have hsum : (∑ x : V, T.degree x) = 2 * C := by
    calc
      (∑ x : V, T.degree x) =
          ∑ x : V, if T.degree x = 2 then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hdegree x with hx | hx <;> simp [hx]
      _ = 2 * C := by
        simp only [C]
        rw [← Finset.sum_filter]
        simp [Nat.mul_comm]
  have hhand := T.sum_degrees_eq_twice_card_edges
  change T.edgeFinset.card = C
  omega

/-- Binary exact form: in an all-size-two partition, the total length of the
all-TF internal cycles is `2^(3k-1) - 3 t(G)`. -/
theorem binarySquare_regular_allSizeTwo_colorOrder_eq_pow_sub_three_mul_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = (2 ^ k) * 2) :
    (((Finset.univ : Finset V).filter fun x =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) =
      (2 : ℤ) ^ (3 * k - 1) -
        3 * (adjacencyTriangleMinorFinset G).card := by
  rw [← binarySquare_regular_allSizeTwo_triangleFreeEdge_card_eq_colorOrder
    G hfree (q := 2 ^ k) (by
      have : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega)
    (by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩)
    hreg hcard hall]
  exact
    binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
      G hfree (by omega) hreg hcard

/-- In an all-size-two defect partition at binary square order, some
component contains a vertex of triangle-free degree two.  Thus the uniform
nonempty-edge theorem seeds an all-triangle-free internal cycle in one of the
size-two blocks. -/
theorem binarySquare_regular_allSizeTwo_exists_triangleFreeDegreeTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = (2 ^ k) * 2) :
    ∃ (c : (secondOrderDefectGraph G).ConnectedComponent) (x : V),
      x ∈ c.supp ∧ (triangleFreeEdgeGraph G).degree x = 2 := by
  let T := triangleFreeEdgeGraph G
  have hnonempty : T.edgeFinset.Nonempty :=
    binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty
      G hfree (by omega) hreg hcard
  have hcardPos : 0 < T.edgeFinset.card := Finset.card_pos.mpr hnonempty
  have hhand := T.sum_degrees_eq_twice_card_edges
  have hsumPos : 0 < ∑ x : V, T.degree x := by
    rw [hhand]
    omega
  have hexists : ∃ x : V, 0 < T.degree x := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ x : V, T.degree x = 0 := by
      intro x
      have hx := hnone x
      omega
    simp_rw [hzero] at hsumPos
    simp at hsumPos
  obtain ⟨x, hxpos⟩ := hexists
  let c := (secondOrderDefectGraph G).connectedComponentMk x
  have hxmem : x ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
  have hq : 3 ≤ 2 ^ k := by
    have hfour : 4 ≤ 2 ^ k := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have heven : Even (2 ^ k) := by
    rw [Nat.even_pow]
    exact ⟨even_two, by omega⟩
  rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree hq heven hreg hcard c (hall c) ⟨x, hxmem⟩ with hzero | htwo
  · have : T.degree x = 0 := by simpa [T] using hzero
    omega
  · exact ⟨c, x, hxmem, htwo⟩

/-- Cycle-level form of the all-size-two seed: one internal ambient connected
component is entirely triangle-free-degree two. -/
theorem binarySquare_regular_allSizeTwo_exists_allTf_internalComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = (2 ^ k) * 2) :
    ∃ (c : (secondOrderDefectGraph G).ConnectedComponent) (x : c.supp),
      (triangleFreeEdgeGraph G).degree x.1 = 2 ∧
      ∀ y : c.supp, (G.induce c.supp).Reachable x y →
        (triangleFreeEdgeGraph G).degree y.1 = 2 := by
  obtain ⟨c, x, hxmem, hx⟩ :=
    binarySquare_regular_allSizeTwo_exists_triangleFreeDegreeTwo
      G hfree hk hreg hcard hall
  let xs : c.supp := ⟨x, hxmem⟩
  refine ⟨c, xs, hx, ?_⟩
  intro y hxy
  exact
    (binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
      G hfree (q := 2 ^ k) (by
        have : 4 ≤ 2 ^ k := by
          calc
            4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega)
      (by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩)
      hreg hcard c (hall c) xs y hxy).mp hx

end


end Erdos85

#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles
#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_card_eq_three_mul_add_pow
#print axioms
  Erdos85.binarySquare_regular_triangleFreeEdge_edgeFinset_nonempty
#print axioms
  Erdos85.binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
#print axioms
  Erdos85.binarySquare_regular_allSizeTwo_triangleFreeEdge_card_eq_colorOrder
#print axioms
  Erdos85.binarySquare_regular_allSizeTwo_colorOrder_eq_pow_sub_three_mul_triangles
#print axioms
  Erdos85.binarySquare_regular_allSizeTwo_exists_triangleFreeDegreeTwo
#print axioms
  Erdos85.binarySquare_regular_allSizeTwo_exists_allTf_internalComponent
