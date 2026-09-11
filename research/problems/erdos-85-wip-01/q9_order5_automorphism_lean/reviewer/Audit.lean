import Proofs.Erdos85Problem
import Proofs.Erdos85GadgetCounting
import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos85DistanceLayers
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

/-- The fixed-graph moment obstruction used for order-five automorphisms.
The boundary hypothesis is the degree-sum inequality supplied by at most
one fixed neighbour per moved vertex in an ambient graph of order at most 80. -/
theorem containsC4_of_four_nine_degrees_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlo : 14 ≤ Fintype.card V) (hhi : Fintype.card V ≤ 23)
    (hdegrees : ∀ v, G.degree v = 4 ∨ G.degree v = 9)
    (hboundary : 10 * Fintype.card V ≤ (∑ v : V, G.degree v) + 80) :
    containsC4 V G := by
  by_contra hfree
  have hpoint : ∀ v : V, 12 * G.degree v ≤ 2 * (G.degree v).choose 2 + 36 := by
    intro v
    rcases hdegrees v with h | h <;> norm_num [h, Nat.choose]
  have hsum : 12 * (∑ v : V, G.degree v) ≤
      2 * (∑ v : V, (G.degree v).choose 2) + 36 * Fintype.card V := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using h
  have hcherry := sum_degree_choose_two_le_card_choose_two_of_not_containsC4 G hfree
  have hchoose := two_mul_choose_two (Fintype.card V)
  have hpred : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have hmoment : 85 * Fintype.card V ≤
      Fintype.card V * Fintype.card V + 960 := by
    nlinarith
  have hinterval : Fintype.card V * Fintype.card V + 322 ≤
      37 * Fintype.card V := by
    nlinarith
  nlinarith

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
# Strict order bound at the C₄-free tight point

The existing friendship-theorem argument on `Fin (k * (k - 1) + 1)` is
transported to arbitrary finite vertex types. Together with the distance-layer
bound, it gives a strict lower bound on the order of every nonempty C₄-free
graph of minimum degree at least `k ≥ 3`. This applies directly to induced
fixed and moved vertex subsets in the automorphism arguments for Erdős 85.
-/

namespace Erdos85

/-- The tight-point obstruction on any finite vertex type. -/
theorem containsC4_of_card_eq_tight_minDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 3 ≤ k)
    (hcard : Fintype.card V = k * (k - 1) + 1)
    (hmin : k ≤ G.minDegree) : containsC4 V G := by
  classical
  let H := G.overFin hcard
  let e : G ≃g H := G.overFinIso hcard
  have hminH : k ≤ H.minDegree := by
    rw [← e.minDegree_eq]
    exact hmin
  obtain ⟨f, hf, hadj⟩ := containsC4_of_tight_minDegree hk H hminH
  refine ⟨fun i => e.symm (f i), e.symm.injective.comp hf, ?_⟩
  intro i j hij
  exact e.symm.map_adj_iff.mpr (hadj i j hij)

/-- A nonempty C₄-free graph lies strictly above the minimum-degree tight point. -/
theorem tight_order_lt_card_of_minDegree
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 3 ≤ k)
    (hmin : k ≤ G.minDegree) :
    k * (k - 1) + 1 < Fintype.card V := by
  classical
  let x : V := Classical.choice inferInstance
  have hbound := one_add_degree_add_mul_sub_two_le_card_of_minDegree G hfree hmin x
  have hdeg : k ≤ G.degree x := hmin.trans (G.minDegree_le_degree x)
  have hmul := Nat.mul_le_mul_right (k - 2) hdeg
  have hsub : k - 1 = (k - 2) + 1 := by omega
  have hle : k * (k - 1) + 1 ≤ Fintype.card V := by
    rw [hsub]
    nlinarith
  have hne : Fintype.card V ≠ k * (k - 1) + 1 := by
    intro heq
    exact hfree (containsC4_of_card_eq_tight_minDegree G hk heq hmin)
  omega

end Erdos85


namespace Erdos85

/-- Below order 81, a nonidentity period-five adjacency-preserving map of
    a C4-free minimum-degree-nine graph has no fixed vertices. -/
theorem no_fixed_points_of_period_five_card_le_eighty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V ≤ 80)
    (τ : V → V) (hperiod : τ^[5] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) : ∀ v, τ v ≠ v := by
  classical
  have hreg : ∀ v, G.degree v = 9 :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by norm_num) hmin (by omega)
  intro v hv
  let F : Set V := {u : V | τ u = u}
  let M : Set V := {u : V | τ u ≠ u}
  let H := G.induce F
  letI : Nonempty F := ⟨⟨v, hv⟩⟩
  have hHfree : ¬ containsC4 F H := by
    rintro ⟨f, hf, hadj⟩
    exact hfree ⟨fun i => (f i).val, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hdegrees : ∀ x : F, H.degree x = 4 ∨ H.degree x = 9 := by
    intro x
    exact fixed_degree_four_or_nine_of_period_five G τ hperiod hmap x.val x.property (hreg x.val)
  have hHmin : 4 ≤ H.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro x
    rcases hdegrees x with h | h <;> omega
  have hlo : 14 ≤ Fintype.card F := by
    have h := tight_order_lt_card_of_minDegree H hHfree (by norm_num : 3 ≤ 4) hHmin
    omega
  have hM := fiftySeven_le_card_moved G hfree hmin τ hmap hmoved
  change 57 ≤ Fintype.card M at hM
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun u => τ u = u) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hpart
  change Fintype.card F + Fintype.card M = Fintype.card V at hpart
  have hhi : Fintype.card F ≤ 23 := by omega
  have hboundary := fixed_degree_sum_boundary G hfree hreg τ hmap
  change 10 * Fintype.card F ≤ (∑ x : F, H.degree x) + Fintype.card V at hboundary
  exact hHfree (containsC4_of_four_nine_degrees_boundary H hlo hhi hdegrees (by omega))

/-- A C4-free order-78 minimum-degree-nine graph has no nonidentity
    adjacency-preserving map whose fifth iterate is the identity. -/
theorem no_nonidentity_period_five_of_card_seventyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78)
    (τ : V → V) (hperiod : τ^[5] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) : τ = id := by
  classical
  by_contra hne
  have hmoved : ∃ x, τ x ≠ x := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hfix := no_fixed_points_of_period_five_card_le_eighty G hfree hmin
    (by omega) τ hperiod hmap hmoved
  let f : Function.End V := τ
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hf : f ^ 5 ^ 1 = 1 := by
    rw [pow_one]
    exact hperiod
  letI : IsEmpty f.fixedPoints := ⟨fun x => hfix x.val x.property⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf
  change Fintype.card V % 5 = Fintype.card f.fixedPoints % 5 at hmod
  simp [hcard] at hmod

end Erdos85
#print axioms Erdos85.no_fixed_points_of_period_five_card_le_eighty
#print axioms Erdos85.no_nonidentity_period_five_of_card_seventyEight
