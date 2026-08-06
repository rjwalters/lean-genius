import Proofs.Erdos85ExcessDefectRegular

/-!
# Local parity at arbitrary positive excess

At order `d(d-1)+3+e`, the combined defect graph has degree `e+2`.
The triangle-free incident edges at a vertex form one part of its defect
neighbourhood, so there are at most `e+2` of them.  On the other hand, all
remaining incident edges are paired by edges of the induced neighbourhood;
the triangle-free count therefore has the same parity as `d`.

For excess two this leaves only `{0,2,4}` in even degree and `{1,3}` in odd
degree.  This is the local starting point for a canonical-form analysis of
the four-regular defect graph.
-/

open SimpleGraph

namespace Erdos85

/-- Triangle-free incident edges occupy part of the `(e+2)`-regular combined
defect neighbourhood. -/
theorem triangleFreeNeighbors_card_le_excess_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) :
    (triangleFreeNeighbors G x).card ≤ e + 2 := by
  have hsub : triangleFreeNeighbors G x ⊆
      (secondOrderDefectGraph G).neighborFinset x := by
    intro y hy
    rw [secondOrderDefectGraph_neighborFinset]
    exact Finset.mem_union_right _ hy
  calc
    (triangleFreeNeighbors G x).card ≤
        ((secondOrderDefectGraph G).neighborFinset x).card :=
      Finset.card_le_card hsub
    _ = (secondOrderDefectGraph G).degree x :=
      (secondOrderDefectGraph G).card_neighborFinset_eq_degree x
    _ = e + 2 :=
      secondOrderDefectGraph_degree_eq_excess_add_two
        G hfree hreg hcard x

/-- The triangle-free incident-edge count has the same parity as the ambient
regular degree. -/
theorem triangleFreeNeighbors_card_mod_two_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (x : V) :
    (triangleFreeNeighbors G x).card % 2 = d % 2 := by
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    G hfree hreg x
  let H := G.induce (G.neighborSet x)
  have hhand :
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
        2 * H.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H
  rw [hhand] at hsum
  omega

/-- At excess two and even degree, the local triangle-free degree is
`0`, `2`, or `4`. -/
theorem excessTwo_triangleFreeNeighbors_card_eq_zero_or_two_or_four_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) (x : V) :
    (triangleFreeNeighbors G x).card = 0 ∨
      (triangleFreeNeighbors G x).card = 2 ∨
      (triangleFreeNeighbors G x).card = 4 := by
  have hle := triangleFreeNeighbors_card_le_excess_add_two
    G hfree (e := 2) hreg (by omega) x
  have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
  obtain ⟨k, hk⟩ := heven
  omega

/-- At excess two and odd degree, the local triangle-free degree is `1` or
`3`. -/
theorem excessTwo_triangleFreeNeighbors_card_eq_one_or_three_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hodd : Odd d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) (x : V) :
    (triangleFreeNeighbors G x).card = 1 ∨
      (triangleFreeNeighbors G x).card = 3 := by
  have hle := triangleFreeNeighbors_card_le_excess_add_two
    G hfree (e := 2) hreg (by omega) x
  have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Odd excess-two terminal.**  No odd-degree regular `C₄`-free graph can
have order `d(d-1)+5`.  Every vertex would have odd degree in the
triangle-free-edge graph, whereas the ambient vertex set has odd cardinality,
contradicting the handshaking lemma. -/
theorem false_of_odd_regular_excessTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hodd : Odd d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) : False := by
  let T := triangleFreeEdgeGraph G
  have hall : ∀ x : V, Odd (T.degree x) := by
    intro x
    have hx := excessTwo_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hodd hreg hcard x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    rcases hx with hx | hx <;> rw [hx] <;> norm_num
  have hevenCard : Even (Fintype.card V) := by
    have hfilter :
        (Finset.univ.filter fun x : V => Odd (T.degree x)) = Finset.univ := by
      ext x
      simp [hall x]
    have hhand := T.even_card_odd_degree_vertices
    rw [hfilter, Finset.card_univ] at hhand
    exact hhand
  have hoddCard : Odd (Fintype.card V) := by
    rw [hcard]
    have hpred : Even (d - 1) := by
      apply (Nat.even_sub' (m := d) (n := 1) hodd.pos).2
      simpa using hodd
    exact (hpred.mul_left d).add_odd (by norm_num)
  obtain ⟨a, ha⟩ := hevenCard
  obtain ⟨b, hb⟩ := hoddCard
  omega

/-- **Uniform odd-degree excess parity.**  An odd-degree regular `C₄`-free
graph cannot have even second-order excess.  This removes every even stratum
of the positive-excess plateau band at once. -/
theorem false_of_odd_degree_even_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hodd : Odd d) (heven : Even e)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) : False := by
  let T := triangleFreeEdgeGraph G
  letI : DecidableRel T.Adj := Classical.decRel _
  have hall : ∀ x : V, Odd (T.degree x) := by
    intro x
    have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    apply Nat.odd_iff.mpr
    rw [hmod]
    exact Nat.odd_iff.mp hodd
  have hevenCard : Even (Fintype.card V) := by
    have hfilter :
        (Finset.univ.filter fun x : V => Odd (T.degree x)) = Finset.univ := by
      ext x
      simp [hall x]
    have hhand := T.even_card_odd_degree_vertices
    rw [hfilter, Finset.card_univ] at hhand
    exact hhand
  have hoddCard : Odd (Fintype.card V) := by
    rw [hcard]
    have hpred : Even (d - 1) := by
      apply (Nat.even_sub' (m := d) (n := 1) hodd.pos).2
      simpa using hodd
    have htail : Odd (3 + e) := by
      simpa [Nat.add_comm] using heven.add_odd (by norm_num : Odd 3)
    simpa [Nat.add_assoc] using (hpred.mul_left d).add_odd htail
  exact (Nat.not_even_iff_odd.mpr hoddCard) hevenCard

/-- Equivalently, every odd-degree regular `C₄`-free graph in the
second-order parametrization has odd excess. -/
theorem excess_odd_of_odd_degree_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) : Odd e := by
  rw [← Nat.not_even_iff_odd]
  exact fun heven =>
    false_of_odd_degree_even_excess G hfree hodd heven hreg hcard

end Erdos85
