import Mathlib

/-!
# A co-edge-regular square-order defect graph is disconnected

A `(q-1)`-regular graph on `q²` vertices cannot have a positive constant
number of common neighbours on every nonedge: the nonneighbours of one root
inject into its length-two walks, but there are already too many of them.
If the constant is zero, adjacency is transitive, so every connected component
is a clique.  These two elementary observations isolate a uniform child of the
connected A-REG obstruction without invoking the classification of geodetic
graphs.
-/

open SimpleGraph

namespace Erdos85

/-- If every nonedge has a positive number of common neighbours, the
nonneighbours of any root inject into the length-two walks from that root.
The deliberately relaxed `k²` bound is enough for the square-order consumer. -/
theorem card_sub_one_sub_degree_le_sq_of_nonadj_commonNeighbors_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {k mu : ℕ} (hreg : D.IsRegularOfDegree k)
    (hmu : ∀ x y, x ≠ y → ¬ D.Adj x y →
      Fintype.card (D.commonNeighbors x y) = mu)
    (hpos : 1 ≤ mu) (u : V) :
    Fintype.card V - 1 - k ≤ k * k := by
  classical
  let S := {y : V // y ≠ u ∧ ¬ D.Adj u y}
  let T := Σ z : {z : V // D.Adj u z}, {y : V // D.Adj z.1 y}
  let center : ∀ y : S, D.commonNeighbors u y.1 := fun y =>
    Classical.choice (Fintype.card_pos_iff.mp (by
      rw [hmu u y.1 y.2.1.symm y.2.2]
      omega : 0 < Fintype.card (D.commonNeighbors u y.1)))
  have hcenterAdj (y : S) :
      D.Adj u (center y).1 ∧ D.Adj y.1 (center y).1 := by
    have hc := (center y).2
    rw [SimpleGraph.mem_commonNeighbors] at hc
    exact hc
  let f : S → T := fun y =>
    ⟨⟨(center y).1, (hcenterAdj y).1⟩,
      ⟨y.1, (hcenterAdj y).2.symm⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hp := congrArg (fun p : T => p.2.1) hxy
    exact hp
  have hcardS : Fintype.card S = Fintype.card V - 1 - k := by
    have hklt : k < Fintype.card V := by
      simpa [hreg u] using D.degree_lt_card_verts u
    rw [Fintype.card_subtype]
    have hpartition :
        Finset.univ.filter (fun y => y ≠ u ∧ ¬ D.Adj u y) =
          Finset.univ \ insert u (D.neighborFinset u) := by
      ext y
      simp [D.mem_neighborFinset]
    rw [hpartition, Finset.card_sdiff]
    simp [D.card_neighborFinset_eq_degree, hreg u]
    omega
  have hcardT : Fintype.card T = k * k := by
    simp only [T, Fintype.card_sigma]
    have houter : Fintype.card {z : V // D.Adj u z} = k := by
      rw [Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => D.Adj u z) = D.neighborFinset u := by
        ext z
        simp [D.mem_neighborFinset]
      rw [heq, D.card_neighborFinset_eq_degree, hreg u]
    simp_rw [show ∀ z : {z : V // D.Adj u z},
        Fintype.card {y : V // D.Adj z.1 y} = k by
      intro z
      rw [Fintype.card_subtype]
      have heq : Finset.univ.filter (fun y => D.Adj z.1 y) = D.neighborFinset z.1 := by
        ext y
        simp [D.mem_neighborFinset]
      rw [heq, D.card_neighborFinset_eq_degree, hreg z.1]]
    simp [houter]
  rw [← hcardS, ← hcardT]
  exact Fintype.card_le_of_injective f hf

/-- Zero common-neighbour count on nonedges makes adjacency transitive along
every non-backtracking two-step walk. -/
theorem adj_trans_of_nonadj_commonNeighbors_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hzero : ∀ x y, x ≠ y → ¬ D.Adj x y →
      Fintype.card (D.commonNeighbors x y) = 0) :
    ∀ {x y z : V}, D.Adj x y → D.Adj y z → x ≠ z → D.Adj x z := by
  intro x y z hxy hyz hxz
  by_contra hxzAdj
  have hcard := hzero x z hxz hxzAdj
  have hy : y ∈ D.commonNeighbors x z := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hxy, hyz.symm⟩
  have hpos : 0 < Fintype.card (D.commonNeighbors x z) :=
    Fintype.card_pos_iff.mpr ⟨⟨y, hy⟩⟩
  omega

/-- A connected regular graph whose nonedges have zero common neighbours is
complete, hence has degree `|V|-1`. -/
theorem degree_eq_card_sub_one_of_connected_nonadj_commonNeighbors_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {k : ℕ} (hreg : D.IsRegularOfDegree k) (hconn : D.Connected)
    (hzero : ∀ x y, x ≠ y → ¬ D.Adj x y →
      Fintype.card (D.commonNeighbors x y) = 0) :
    k = Fintype.card V - 1 := by
  have htrans : ∀ {x y z : V},
      D.Adj x y → D.Adj y z → x ≠ z → D.Adj x z :=
    adj_trans_of_nonadj_commonNeighbors_zero D hzero
  have hcollapse : ∀ {x z : V}, D.Reachable x z → x = z ∨ D.Adj x z := by
    intro x z hreach
    obtain ⟨p⟩ := hreach
    induction p with
    | nil => exact Or.inl rfl
    | @cons x y z hxy p ih =>
        rcases ih with rfl | hxz
        · exact Or.inr hxy
        · by_cases h : x = z
          · exact Or.inl h
          · exact Or.inr (htrans hxy hxz h)
  let u : V := Classical.choice hconn.nonempty
  have hdegree := hreg u
  have hall : D.neighborFinset u = Finset.univ.erase u := by
    ext z
    simp only [D.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · exact fun huz => (D.ne_of_adj huz).symm
    · intro hzu
      rcases hcollapse (hconn u z) with h | h
      · exact (hzu h.symm).elim
      · exact h
  calc
    k = D.degree u := (hreg u).symm
    _ = (D.neighborFinset u).card := (D.card_neighborFinset_eq_degree u).symm
    _ = (Finset.univ.erase u).card := by rw [hall]
    _ = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]

/-- A co-edge-regular `(q-1)`-regular graph on `q²` vertices has zero
nonedge codegree and is disconnected. -/
theorem squareOrder_degree_pred_constant_nonadj_commonNeighbors_disconnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {q mu : ℕ} (hq : 2 ≤ q)
    (hcard : Fintype.card V = q * q)
    (hreg : D.IsRegularOfDegree (q - 1))
    (hmu : ∀ x y, x ≠ y → ¬ D.Adj x y →
      Fintype.card (D.commonNeighbors x y) = mu) :
    mu = 0 ∧ ¬ D.Connected := by
  have hmu0 : mu = 0 := by
    by_contra hne
    have hpos : 1 ≤ mu := Nat.one_le_iff_ne_zero.mpr hne
    let u : V := Classical.choice (Fintype.card_pos_iff.mp (by
      rw [hcard]
      positivity))
    have hb := card_sub_one_sub_degree_le_sq_of_nonadj_commonNeighbors_pos
      D hreg hmu hpos u
    rw [hcard] at hb
    have hsub : q * q - 1 - (q - 1) = q * (q - 1) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [hsub] at hb
    have hlt : (q - 1) * (q - 1) < q * (q - 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    exact (not_lt_of_ge hb) hlt
  refine ⟨hmu0, ?_⟩
  intro hconn
  have hdegree := degree_eq_card_sub_one_of_connected_nonadj_commonNeighbors_zero
    D hreg hconn (by simpa [hmu0] using hmu)
  rw [hcard] at hdegree
  have hqq : q < q * q := by nlinarith
  omega

#print axioms card_sub_one_sub_degree_le_sq_of_nonadj_commonNeighbors_pos
#print axioms adj_trans_of_nonadj_commonNeighbors_zero
#print axioms degree_eq_card_sub_one_of_connected_nonadj_commonNeighbors_zero
#print axioms squareOrder_degree_pred_constant_nonadj_commonNeighbors_disconnected

end Erdos85
