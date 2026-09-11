import Proofs.Erdos85DistanceLayers
import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos85GadgetCounting
import Mathlib.GroupTheory.Perm.Cycle.Type


/-!
# Fixed neighbours of a moved vertex

In a C4-free graph, a vertex moved by an adjacency-preserving map has at
most one fixed neighbour. No bijectivity or finite-order hypothesis is needed.
This supplies the boundary bound in prime-order fixed-point arguments.
-/

namespace Erdos85

/-- Two fixed neighbours of a moved vertex coincide. -/
theorem fixed_neighbors_eq_of_moved {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {x u v : V} (hx : τ x ≠ x)
    (hu : τ u = u) (hv : τ v = v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) : u = v := by
  by_contra huv
  have hτxu : G.Adj (τ x) u := by simpa only [hu] using hmap hxu
  have hτxv : G.Adj (τ x) v := by simpa only [hv] using hmap hxv
  exact hfree (containsC4_of_two_common huv (Ne.symm hx)
    hxu hxv hτxu hτxv)

/-- The fixed neighbours of a moved vertex form a subsingleton set. -/
theorem fixed_neighborSet_subsingleton_of_moved {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {x : V} (hx : τ x ≠ x) :
    Set.Subsingleton {u : V | G.Adj x u ∧ τ u = u} := by
  intro u hu v hv
  exact fixed_neighbors_eq_of_moved hfree τ hmap hx hu.2 hv.2 hu.1 hv.1

end Erdos85


namespace Erdos85

/-- Removing the fixed vertices lowers the degree of a moved vertex by at most one. -/
theorem degree_le_moved_degree_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (x : ({v : V | τ v ≠ v} : Set V)) :
    G.degree x ≤ (G.induce {v : V | τ v ≠ v}).degree x + 1 := by
  classical
  have hfixed : ((G.neighborFinset x).filter (fun u => τ u = u)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu hv
    exact fixed_neighbors_eq_of_moved hfree τ hmap x.property hu.2 hv.2 hu.1 hv.1
  have hpart := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset x) (p := fun u => τ u = u)
  have hmove : ((G.neighborFinset x).filter (fun u => τ u ≠ u)).card =
      (G.induce {v : V | τ v ≠ v}).degree x := by
    have heq : (G.neighborFinset x).filter (fun u => τ u ≠ u) =
        G.neighborFinset x ∩ ({v : V | τ v ≠ v} : Set V).toFinset := by
      ext u
      simp
    rw [heq, ← G.map_neighborFinset_induce x, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
  rw [hmove, G.card_neighborFinset_eq_degree] at hpart
  omega

/-- A nonempty moved induced graph has minimum degree at least the original minus one. -/
theorem minDegree_sub_one_le_moved_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    G.minDegree - 1 ≤ (G.induce {v : V | τ v ≠ v}).minDegree := by
  classical
  obtain ⟨x, hx⟩ := hmoved
  letI : Nonempty ({v : V | τ v ≠ v} : Set V) := ⟨⟨x, hx⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  have h₁ := G.minDegree_le_degree v
  have h₂ := degree_le_moved_degree_add_one G hfree τ hmap v
  omega

end Erdos85


namespace Erdos85

/-- A nonidentity adjacency-preserving map of a C4-free graph of minimum
    degree at least nine moves at least fifty-seven vertices. -/
theorem fiftySeven_le_card_moved
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    57 ≤ Fintype.card ({v : V | τ v ≠ v} : Set V) := by
  classical
  let M : Set V := {v : V | τ v ≠ v}
  let H := G.induce M
  have hHfree : ¬ containsC4 M H := by
    rintro ⟨f, hf, hadj⟩
    apply hfree
    exact ⟨fun i => (f i).val, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hHmin : 8 ≤ H.minDegree := by
    have h := minDegree_sub_one_le_moved_minDegree G hfree τ hmap hmoved
    change G.minDegree - 1 ≤ H.minDegree at h
    omega
  obtain ⟨x, hx⟩ := hmoved
  let v : M := ⟨x, hx⟩
  have hdegree : 8 ≤ H.degree v := hHmin.trans (H.minDegree_le_degree v)
  have hbound := one_add_degree_add_mul_sub_two_le_card_of_minDegree H hHfree hHmin v
  norm_num only [Nat.reduceSub] at hbound
  change 57 ≤ Fintype.card M
  omega

end Erdos85


namespace Erdos85

/-- Boundary counting for the fixed set of an adjacency-preserving map in a
regular C4-free graph. Each moved vertex has at most one fixed neighbour. -/
theorem fixed_degree_sum_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hreg : ∀ v, G.degree v = d)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) :
    (d + 1) * Fintype.card ({v : V | τ v = v} : Set V) ≤
      (∑ v : ({v : V | τ v = v} : Set V),
        (G.induce {v : V | τ v = v}).degree v) + Fintype.card V := by
  classical
  let F : Set V := {v : V | τ v = v}
  let b : V → ℕ := fun v => (G.neighborFinset v ∩ F.toFinset).card
  have htotal : (∑ v : V, b v) = d * Fintype.card F := by
    have h := sum_card_neighbor_inter_eq_sum_degree G F.toFinset
    change (∑ v : V, b v) = _ at h
    simpa [hreg, Nat.mul_comm] using h
  have hinside : ∀ v : F, b v = (G.induce F).degree v := by
    intro v
    dsimp [b]
    rw [← G.map_neighborFinset_induce v, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
  have houtside : ∀ v : (Fᶜ : Set V), b v ≤ 1 := by
    intro v
    apply Finset.card_le_one.mpr
    intro u hu w hw
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Set.mem_toFinset] at hu hw
    exact fixed_neighbors_eq_of_moved hfree τ hmap v.property hu.2 hw.2 hu.1 hw.1
  have hsumoutside : (∑ v : (Fᶜ : Set V), b v) ≤ Fintype.card (Fᶜ : Set V) := by
    calc
      (∑ v : (Fᶜ : Set V), b v) ≤ ∑ _v : (Fᶜ : Set V), 1 := Finset.sum_le_sum (fun v _ => houtside v)
      _ = Fintype.card (Fᶜ : Set V) := by simp
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ F) b
  have hcard := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ F) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hcard
  simp only [hinside] at hsplit
  rw [htotal] at hsplit
  change Fintype.card F + Fintype.card (Fᶜ : Set V) = Fintype.card V at hcard
  change (∑ v : F, (G.induce F).degree v) +
    (∑ v : (Fᶜ : Set V), b v) = d * Fintype.card F at hsplit
  change (d + 1) * Fintype.card F ≤ (∑ v : F, (G.induce F).degree v) + Fintype.card V
  nlinarith

end Erdos85


namespace Erdos85

/-- At a fixed vertex of a prime-period adjacency-preserving map, the full
and fixed-induced degrees have equal residues modulo that prime. -/
theorem degree_modEq_fixed_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) {p : ℕ} [Fact p.Prime]
    (hperiod : τ^[p] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (v : V) (hv : τ v = v) :
    G.degree v ≡ (G.induce {u : V | τ u = u}).degree ⟨v, hv⟩ [MOD p] := by
  classical
  let F : Set V := {u : V | τ u = u}
  let f : Function.End (G.neighborSet v) := fun w =>
    ⟨τ w, by
      change G.Adj v (τ w)
      simpa only [hv] using hmap w.property⟩
  have hiter : ∀ n (w : G.neighborSet v),
      (f^[n] w).val = τ^[n] w.val := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      simp only [Function.iterate_succ_apply', f, ih]
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    change f^[p] = id
    funext w
    apply Subtype.ext
    rw [hiter]
    exact congrFun hperiod w.val
  let e : f.fixedPoints ≃ (G.induce F).neighborSet (⟨v, hv⟩ : F) :=
    { toFun := fun w => ⟨⟨w.val.val, congrArg Subtype.val w.property⟩, w.val.property⟩
      invFun := fun w => ⟨⟨w.val.val, w.property⟩, Subtype.ext w.val.property⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  have hcard : Fintype.card f.fixedPoints =
      (G.induce F).degree (⟨v, hv⟩ : F) := by
    rw [Fintype.card_congr e, SimpleGraph.card_neighborSet_eq_degree]
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  simpa only [G.card_neighborSet_eq_degree, hcard] using h

/-- A fixed vertex of degree nine has four or nine fixed neighbours under
an adjacency-preserving map whose fifth iterate is the identity. -/
theorem fixed_degree_four_or_nine_of_period_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) (hperiod : τ^[5] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (v : V) (hv : τ v = v) (hdegree : G.degree v = 9) :
    (G.induce {u : V | τ u = u}).degree ⟨v, hv⟩ = 4 ∨
      (G.induce {u : V | τ u = u}).degree ⟨v, hv⟩ = 9 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := degree_modEq_fixed_degree G τ hperiod hmap v hv
  let F : Set V := {u : V | τ u = u}
  let x : F := ⟨v, hv⟩
  have hle : (G.induce F).degree x ≤ G.degree v := by
    have h := Finset.card_le_card
      (Finset.inter_subset_left : G.neighborFinset v ∩ F.toFinset ⊆ G.neighborFinset v)
    rw [← G.map_neighborFinset_induce x, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at h
    exact h
  rw [hdegree] at hmod
  change 9 % 5 = (G.induce F).degree x % 5 at hmod
  change (G.induce F).degree x = 4 ∨ (G.induce F).degree x = 9
  rw [hdegree] at hle
  omega

end Erdos85


/-!
# Degree-two-or-nine reduction for the order-seven fixed graph

The boundary inequality and the C₄-free degree moment bound restrict a
nonempty fixed graph to order 8 (ambient order 78), or order 3 or 10
(ambient order 80). Every vertex then has degree two. The hypotheses that
come from the automorphism action remain explicit in this counting lemma.
-/

namespace Erdos85

/-- The fixed-graph counting reduction used for order-seven automorphisms. -/
theorem two_nine_degrees_boundary_reduction
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {N : ℕ} (hN : N = 78 ∨ N = 80)
    (hhi : Fintype.card V ≤ 23)
    (hmod : Fintype.card V ≡ N [MOD 7])
    (hdegrees : ∀ v, G.degree v = 2 ∨ G.degree v = 9)
    (hboundary : 10 * Fintype.card V ≤ (∑ v : V, G.degree v) + N) :
    ((N = 78 ∧ Fintype.card V = 8) ∨
      (N = 80 ∧ (Fintype.card V = 3 ∨ Fintype.card V = 10))) ∧
    (∀ v, G.degree v = 2) := by
  classical
  have hlo : 3 ≤ Fintype.card V := by
    let v : V := Classical.choice inferInstance
    have hdeg := hdegrees v
    have hlt := G.degree_lt_card_verts v
    omega
  have hpoint : ∀ v : V, 10 * G.degree v ≤ 2 * (G.degree v).choose 2 + 18 := by
    intro v
    rcases hdegrees v with h | h <;> norm_num [h, Nat.choose]
  have hsum : 10 * (∑ v : V, G.degree v) ≤
      2 * (∑ v : V, (G.degree v).choose 2) + 18 * Fintype.card V := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using h
  have hcherry := sum_degree_choose_two_le_card_choose_two_of_not_containsC4 G hfree
  have hchoose := two_mul_choose_two (Fintype.card V)
  have hpred : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have hmoment : 83 * Fintype.card V ≤
      Fintype.card V * Fintype.card V + 10 * N := by
    nlinarith
  have hcases : (N = 78 ∧ Fintype.card V = 8) ∨
      (N = 80 ∧ (Fintype.card V = 3 ∨ Fintype.card V = 10)) := by
    change Fintype.card V % 7 = N % 7 at hmod
    rcases hN with rfl | rfl
    · have hc : Fintype.card V = 8 ∨ Fintype.card V = 15 ∨ Fintype.card V = 22 := by omega
      rcases hc with h | h | h
      · exact Or.inl ⟨rfl, h⟩
      · norm_num [h] at hmoment
      · norm_num [h] at hmoment
    · have hc : Fintype.card V = 3 ∨ Fintype.card V = 10 ∨ Fintype.card V = 17 := by omega
      rcases hc with h | h | h
      · exact Or.inr ⟨rfl, Or.inl h⟩
      · exact Or.inr ⟨rfl, Or.inr h⟩
      · norm_num [h] at hmoment
  refine ⟨hcases, ?_⟩
  intro v
  rcases hdegrees v with hv | hv
  · exact hv
  · have hlt := G.degree_lt_card_verts v
    have hcard : Fintype.card V = 10 := by
      rcases hcases with ⟨_, h⟩ | ⟨_, h | h⟩ <;> omega
    have hsum_lower : 27 ≤ ∑ w : V, G.degree w := by
      calc
        27 = ∑ w : V, (2 + if w = v then 7 else 0) := by
          simp [Finset.sum_add_distrib, hcard]
        _ ≤ ∑ w : V, G.degree w := by
          apply Finset.sum_le_sum
          intro w _
          by_cases hw : w = v
          · subst w
            simp [hv]
          · simp only [hw, if_false, add_zero]
            rcases hdegrees w with h | h <;> omega
    have hsum_upper : (∑ w : V, G.degree w) ≤ 27 := by
      norm_num [hcard, Nat.choose] at hcherry
      rw [hcard] at hsum
      omega
    have hhand := G.sum_degrees_eq_twice_card_edges
    omega

end Erdos85


/-!
# Fixed graph of a period-seven map at order 78 or 80

This assembles the fixed-degree congruence, moved-vertex lower bound and
boundary counting into the first half of the order-seven obstruction. It
does not yet exclude the remaining fixed configurations.
-/

namespace Erdos85

/-- The fixed graph of a nonidentity period-seven map has order 8 at ambient
order 78, or order 3 or 10 at ambient order 80, and is two-regular. -/
theorem fixed_graph_of_period_seven_card_seventyEight_or_eighty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78 ∨ Fintype.card V = 80)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    ((Fintype.card V = 78 ∧ Fintype.card ({v : V | τ v = v} : Set V) = 8) ∨
      (Fintype.card V = 80 ∧
        (Fintype.card ({v : V | τ v = v} : Set V) = 3 ∨
         Fintype.card ({v : V | τ v = v} : Set V) = 10))) ∧
    (∀ v : ({u : V | τ u = u} : Set V),
      (G.induce {u : V | τ u = u}).degree v = 2) := by
  classical
  let F : Set V := {u : V | τ u = u}
  let M : Set V := {u : V | τ u ≠ u}
  let H := G.induce F
  let f : Function.End V := τ
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hf : f ^ 7 ^ 1 = 1 := by
    rw [pow_one]
    exact hperiod
  have hmod : Fintype.card F ≡ Fintype.card V [MOD 7] := by
    have h := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) hf
    exact h.symm
  have hFpos : 0 < Fintype.card F := by
    have h := hmod
    change Fintype.card F % 7 = Fintype.card V % 7 at h
    rcases hcard with hc | hc <;> rw [hc] at h <;> omega
  letI : Nonempty F := Fintype.card_pos_iff.mp hFpos
  have hreg : ∀ v, G.degree v = 9 :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by norm_num) hmin (by omega)
  have hHfree : ¬ containsC4 F H := by
    rintro ⟨g, hg, hadj⟩
    exact hfree ⟨fun i => (g i).val, Subtype.val_injective.comp hg,
      fun i j hij => hadj i j hij⟩
  have hdegrees : ∀ x : F, H.degree x = 2 ∨ H.degree x = 9 := by
    intro x
    have hm := degree_modEq_fixed_degree G τ hperiod hmap x.val x.property
    change G.degree x % 7 = H.degree x % 7 at hm
    rw [hreg] at hm
    have hle : H.degree x ≤ G.degree x := by
      have h := Finset.card_le_card
        (Finset.inter_subset_left : G.neighborFinset x ∩ F.toFinset ⊆ G.neighborFinset x)
      rw [← G.map_neighborFinset_induce x, Finset.card_map,
        SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at h
      exact h
    rw [hreg] at hle
    omega
  have hM := fiftySeven_le_card_moved G hfree hmin τ hmap hmoved
  change 57 ≤ Fintype.card M at hM
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun u => τ u = u) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hpart
  change Fintype.card F + Fintype.card M = Fintype.card V at hpart
  have hhi : Fintype.card F ≤ 23 := by omega
  have hboundary := fixed_degree_sum_boundary G hfree hreg τ hmap
  exact two_nine_degrees_boundary_reduction H hHfree hcard hhi hmod hdegrees hboundary

end Erdos85

#print axioms Erdos85.two_nine_degrees_boundary_reduction
#print axioms Erdos85.fixed_graph_of_period_seven_card_seventyEight_or_eighty
