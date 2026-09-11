import Proofs.Erdos85PrimeOrbitMatching

namespace Erdos85

/-- A degree-nine fixed vertex with two fixed neighbours has seven moved neighbours. -/
theorem card_moved_neighbors_eq_seven_of_degree_nine_fixed_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) (u : V) (hu : τ u = u) (hdegree : G.degree u = 9)
    (hfixed : (G.induce {v : V | τ v = v}).degree ⟨u, hu⟩ = 2) :
    Fintype.card ({v : V | G.Adj u v ∧ τ v ≠ v} : Set V) = 7 := by
  classical
  let B : Set V := {v : V | G.Adj u v ∧ τ v ≠ v}
  let F : Set V := {v : V | τ v = v}
  have hfixedcard : ((G.neighborFinset u).filter (fun v => τ v = v)).card = 2 := by
    have heq : (G.neighborFinset u).filter (fun v => τ v = v) =
        G.neighborFinset u ∩ F.toFinset := by ext v; simp [F]
    rw [heq, ← G.map_neighborFinset_induce (⟨u, hu⟩ : F),
      Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree]
    exact hfixed
  have hBfilter : ((G.neighborFinset u).filter (fun v => τ v ≠ v)).card =
      Fintype.card B := by
    rw [← Set.toFinset_card]
    congr 1
    ext v
    simp [B]
  have hBcard : Fintype.card B = 7 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset u) (p := fun v => τ v = v)
    rw [hfixedcard, hBfilter, G.card_neighborFinset_eq_degree, hdegree] at h
    omega
  exact hBcard

/-- The moved neighbours of a fixed vertex with full degree nine and
    fixed-induced degree two form an independent seven-vertex orbit. -/
theorem not_adj_moved_neighbors_of_fixed_period_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (u : V) (hu : τ u = u) (hdegree : G.degree u = 9)
    (hfixed : (G.induce {v : V | τ v = v}).degree ⟨u, hu⟩ = 2)
    {x y : V} (hux : G.Adj u x) (huy : G.Adj u y)
    (hx : τ x ≠ x) (hy : τ y ≠ y) : ¬ G.Adj x y := by
  classical
  let B : Set V := {v : V | G.Adj u v ∧ τ v ≠ v}
  let F : Set V := {v : V | τ v = v}
  have hBcard : Fintype.card B = 7 :=
    card_moved_neighbors_eq_seven_of_degree_nine_fixed_two G τ u hu hdegree hfixed
  have hinj : Function.Injective τ := by
    intro a b hab
    have h := congrArg (τ^[6]) hab
    simpa only [← Function.iterate_succ_apply, hperiod, id_eq] using h
  let f : B → B := fun v => ⟨τ v,
    by
      constructor
      · simpa only [hu] using hmap v.property.1
      · intro h
        exact v.property.2 (hinj h)⟩
  have hiter : ∀ n (v : B), (f^[n] v).val = τ^[n] v.val := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih => intro v; simp only [Function.iterate_succ_apply', f, ih]
  have hfperiod : f^[7] = id := by
    funext v
    apply Subtype.ext
    rw [hiter]
    exact congrFun hperiod v.val
  have hffree : ∀ v : B, f v ≠ v := by
    intro v h
    exact v.property.2 (congrArg Subtype.val h)
  have hfmap : ∀ {a b : B}, (G.induce B).Adj a b → (G.induce B).Adj (f a) (f b) := by
    intro a b hab
    exact hmap hab
  have hBdegree : ∀ v : B, (G.induce B).degree v ≤ 1 := by
    intro v
    change ((G.induce B).neighborFinset v).card ≤ 1
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply Subtype.ext
    by_contra hab
    have hva := ((G.induce B).mem_neighborFinset v a).mp ha
    have hvb := ((G.induce B).mem_neighborFinset v b).mp hb
    exact hfree (containsC4_of_two_common (G.ne_of_adj v.property.1) hab
      a.property.1.symm hva.symm b.property.1.symm hvb.symm)
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact not_adj_of_prime_card_free_map_degree_le_one (G.induce B) f hBcard
    (by norm_num : Odd 7) hfperiod hffree hfmap hBdegree ⟨x, hux, hx⟩ ⟨y, huy, hy⟩

end Erdos85
