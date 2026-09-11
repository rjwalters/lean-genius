import Mathlib.Dynamics.PeriodicPts.Lemmas
import Proofs.Erdos85FixedBoundary
import Proofs.Erdos85FixedNeighbors
import Proofs.Erdos85GadgetCounting
import Proofs.Erdos85MovedCard
import Proofs.Erdos85PrimeFixedDegree
import Proofs.Erdos85Problem
import Proofs.Erdos85TwoNineDegreeReduction

namespace Erdos85

/-- A free prime-period map on a set of prime cardinality has a single orbit. -/
theorem exists_iterate_eq_of_prime_card
    {V : Type*} [Fintype V] (τ : V → V) {p : ℕ} [Fact p.Prime]
    (hcard : Fintype.card V = p) (hperiod : τ^[p] = id)
    (hfix : ∀ v, τ v ≠ v) (x y : V) :
    ∃ i : Fin p, τ^[i.val] x = y := by
  classical
  have hmin : Function.minimalPeriod τ x = p :=
    Function.minimalPeriod_eq_prime (congrFun hperiod x) (hfix x)
  let f : Fin p → V := fun i => τ^[i.val] x
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by simpa only [hmin] using i.isLt) (by simpa only [hmin] using j.isLt)).mp hij
  have hsurj : Function.Surjective f := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective f hinj h
    simp only [Fintype.card_fin, hcard, lt_self_iff_false] at hlt
  exact hsurj y

/-- An invariant matching on a free orbit of odd prime size has no edges. -/
theorem not_adj_of_prime_card_free_map_degree_le_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) {p : ℕ} [Fact p.Prime]
    (hcard : Fintype.card V = p) (hodd : Odd p)
    (hperiod : τ^[p] = id) (hfix : ∀ v, τ v ≠ v)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hdegree : ∀ v, G.degree v ≤ 1) (x y : V) : ¬ G.Adj x y := by
  classical
  intro hxy
  have hiter : ∀ n, G.Adj (τ^[n] x) (τ^[n] y) := by
    intro n
    induction n with
    | zero => exact hxy
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using hmap ih
  have hreg : ∀ v, G.degree v = 1 := by
    intro v
    obtain ⟨i, hi⟩ := exists_iterate_eq_of_prime_card τ hcard hperiod hfix x v
    apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    refine ⟨τ^[i.val] y, ?_, ?_⟩
    · simpa only [hi] using hiter i.val
    · intro w hw
      have hle : (G.neighborFinset v).card ≤ 1 := hdegree v
      apply Finset.card_le_one.mp hle
      · exact (G.mem_neighborFinset v w).mpr hw
      · exact (G.mem_neighborFinset v (τ^[i.val] y)).mpr
          (by simpa only [hi] using hiter i.val)
  have heven : Even (Fintype.card V) := by
    have h := G.even_card_odd_degree_vertices
    simpa [hreg] using h
  rw [hcard] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end Erdos85

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

namespace Erdos85

/-- The moved neighbours attached to a given vertex. -/
def movedNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (τ : V → V) (u : V) : Finset V :=
  (G.neighborFinset u).filter (fun x => τ x ≠ x)

@[simp] theorem mem_movedNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (τ : V → V) (u x : V) :
    x ∈ movedNeighborFinset G τ u ↔ G.Adj u x ∧ τ x ≠ x := by
  simp [movedNeighborFinset]

/-- Attached sets of distinct fixed vertices are disjoint. -/
theorem movedNeighborFinset_disjoint_of_fixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {u v : V} (hu : τ u = u) (hv : τ v = v) (huv : u ≠ v) :
    Disjoint (movedNeighborFinset G τ u) (movedNeighborFinset G τ v) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_movedNeighborFinset] at hx hy
  exact huv (fixed_neighbors_eq_of_moved hfree τ hmap hx.2 hu hv hx.1.symm hy.1.symm)

/-- Adjacent fixed centres have no edges between their attached sets. -/
theorem not_adj_movedNeighborFinset_of_fixed_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    {u v x y : V} (hu : τ u = u) (hv : τ v = v) (huv : G.Adj u v)
    (hx : x ∈ movedNeighborFinset G τ u) (hy : y ∈ movedNeighborFinset G τ v) :
    ¬ G.Adj x y := by
  rw [mem_movedNeighborFinset] at hx hy
  intro hxy
  have huy : u ≠ y := by intro h; subst y; exact hy.2 hu
  have hvx : v ≠ x := by intro h; subst x; exact hx.2 hv
  exact hfree (containsC4_of_two_common huy hvx huv.symm hy.1 hx.1.symm hxy)

/-- Any vertex other than a centre meets its attached set at most once. -/
theorem card_neighbor_inter_movedNeighborFinset_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V) {u x : V} (hxu : x ≠ u) :
    (G.neighborFinset x ∩ movedNeighborFinset G τ u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_movedNeighborFinset] at ha hb
  by_contra hab
  exact hfree (containsC4_of_two_common hxu hab ha.1.symm ha.2.1.symm hb.1.symm hb.2.1.symm)

/-- Cardinal form of the seven attached neighbours. -/
theorem card_movedNeighborFinset_eq_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) (u : V) (hu : τ u = u) (hdegree : G.degree u = 9)
    (hfixed : (G.induce {v : V | τ v = v}).degree ⟨u, hu⟩ = 2) :
    (movedNeighborFinset G τ u).card = 7 := by
  classical
  have h := card_moved_neighbors_eq_seven_of_degree_nine_fixed_two G τ u hu hdegree hfixed
  have heq : movedNeighborFinset G τ u =
      ({x : V | G.Adj u x ∧ τ x ≠ x} : Set V).toFinset := by ext x; simp
  rw [heq, Set.toFinset_card]
  exact h

end Erdos85

namespace Erdos85

/-- Three attached sets at a fixed vertex and its two fixed neighbours
force at least77 moved vertices. -/
theorem seventySeven_le_card_moved_of_fixed_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 9)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hfixed : ∀ x : ({v : V | τ v = v} : Set V),
      (G.induce {v : V | τ v = v}).degree x = 2)
    {u v w : V} (hu : τ u = u) (hv : τ v = v) (hw : τ w = w)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : v ≠ w) :
    77 ≤ Fintype.card ({x : V | τ x ≠ x} : Set V) := by
  classical
  let A := movedNeighborFinset G τ u
  let B := movedNeighborFinset G τ v
  let C := movedNeighborFinset G τ w
  let M := Finset.univ.filter (fun x : V => τ x ≠ x)
  let T := A ∪ B ∪ C
  let D := M \ T
  have hA : A.card = 7 := card_movedNeighborFinset_eq_seven G τ u hu (hreg u) (hfixed ⟨u, hu⟩)
  have hB : B.card = 7 := card_movedNeighborFinset_eq_seven G τ v hv (hreg v) (hfixed ⟨v, hv⟩)
  have hC : C.card = 7 := card_movedNeighborFinset_eq_seven G τ w hw (hreg w) (hfixed ⟨w, hw⟩)
  have hAB : Disjoint A B := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hu hv (G.ne_of_adj huv)
  have hAC : Disjoint A C := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hu hw (G.ne_of_adj huw)
  have hBC : Disjoint B C := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hv hw hvw
  have hT : T.card = 21 := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint hAB, hA, hB, hC]
  have hTM : T ⊆ M := by
    intro x hx
    simp only [T, Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    all_goals
      simp only [A, B, C, mem_movedNeighborFinset] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx.2⟩
  have hDM : D.card + 21 = M.card := by
    have h := Finset.card_sdiff_add_card_eq_card hTM
    simpa only [hT] using h
  let b : V → ℕ := fun x => (G.neighborFinset x ∩ A).card
  have hzero : ∀ x, x ≠ u → x ∉ D → b x = 0 := by
    intro x hxu hxD
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨hxa, ha⟩ := Finset.mem_inter.mp ha
    have hxa := (G.mem_neighborFinset x a).mp hxa
    have ha' := (mem_movedNeighborFinset G τ u a).mp ha
    by_cases hxf : τ x = x
    · exact hxu (fixed_neighbors_eq_of_moved hfree τ hmap ha'.2 hxf hu hxa.symm ha'.1.symm)
    · have hxM : x ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxf⟩
      have hxT : x ∈ T := by
        by_contra h
        exact hxD (Finset.mem_sdiff.mpr ⟨hxM, h⟩)
      simp only [T, Finset.mem_union] at hxT
      rcases hxT with (hxA | hxB) | hxC
      · have hx' := (mem_movedNeighborFinset G τ u x).mp hxA
        exact not_adj_moved_neighbors_of_fixed_period_seven G hfree τ hperiod hmap
          u hu (hreg u) (hfixed ⟨u, hu⟩) hx'.1 ha'.1 hx'.2 ha'.2 hxa
      · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ hu hv huv ha hxB hxa.symm
      · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ hu hw huw ha hxC hxa.symm
  have hpoint : ∀ x : V, b x ≤ (if x = u then A.card else 0) + (if x ∈ D then 1 else 0) := by
    intro x
    by_cases hxu : x = u
    · have hle : b x ≤ A.card := Finset.card_le_card Finset.inter_subset_right
      simp only [if_pos hxu]
      omega
    · have hle : b x ≤ 1 := card_neighbor_inter_movedNeighborFinset_le_one G hfree τ hxu
      by_cases hxD : x ∈ D
      · simpa only [if_neg hxu, if_pos hxD, zero_add] using hle
      · rw [hzero x hxu hxD]
        exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  have htotal : (∑ x : V, b x) = 63 := by
    rw [show (∑ x : V, b x) = ∑ a ∈ A, G.degree a from sum_card_neighbor_inter_eq_sum_degree G A]
    simp [hreg, hA]
  have hcap : 63 ≤ 7 + D.card := by
    simpa [Finset.sum_add_distrib, htotal, hA] using hsum
  have hMcard : M.card = Fintype.card ({x : V | τ x ≠ x} : Set V) := by
    rw [← Set.toFinset_card]
    congr 1
    ext x
    simp [M]
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

namespace Erdos85

/-- The attached-set incidence bound leaves only ambient order80 and
    exactly three fixed vertices in a nonidentity period-seven action. -/
theorem card_eighty_fixed_three_of_period_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78 ∨ Fintype.card V = 80)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    Fintype.card V = 80 ∧ Fintype.card ({v : V | τ v = v} : Set V) = 3 := by
  classical
  obtain ⟨hcases, hfixed⟩ := fixed_graph_of_period_seven_card_seventyEight_or_eighty
    G hfree hmin hcard τ hperiod hmap hmoved
  let F : Set V := {v : V | τ v = v}
  let M : Set V := {v : V | τ v ≠ v}
  have hpos : 0 < Fintype.card F := by
    rcases hcases with ⟨_, h⟩ | ⟨_, h | h⟩ <;> change Fintype.card F = _ at h <;> omega
  letI : Nonempty F := Fintype.card_pos_iff.mp hpos
  let u : F := Classical.choice inferInstance
  have hpair : ((G.induce F).neighborFinset u).card = 2 := hfixed u
  obtain ⟨v, w, hvw, hset⟩ := Finset.card_eq_two.mp hpair
  have huv : G.Adj u.val v.val := by
    have hmem : v ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u v).mp hmem
  have huw : G.Adj u.val w.val := by
    have hmem : w ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u w).mp hmem
  have hreg : ∀ x, G.degree x = 9 :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by norm_num) hmin (by omega)
  have hM := seventySeven_le_card_moved_of_fixed_neighbors G hfree hreg τ hperiod hmap
    hfixed u.property v.property w.property huv huw (fun h => hvw (Subtype.ext h))
  change 77 ≤ Fintype.card M at hM
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun x => τ x = x) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hpart
  change Fintype.card F + Fintype.card M = Fintype.card V at hpart
  change Fintype.card V = 80 ∧ Fintype.card F = 3
  rcases hcases with ⟨hN, hF⟩ | ⟨hN, hF | hF⟩
  all_goals
    change Fintype.card F = _ at hF
    omega

/-- At order78 a period-seven adjacency-preserving map is the identity. -/
theorem no_nonidentity_period_seven_of_card_seventyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) : τ = id := by
  classical
  by_contra hne
  have hmoved : ∃ x, τ x ≠ x := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have h := (card_eighty_fixed_three_of_period_seven G hfree hmin (Or.inl hcard)
    τ hperiod hmap hmoved).1
  omega

end Erdos85

namespace Erdos85

/-- Equality at77 moved vertices forces every residual vertex to meet
    the attached set at the centre. -/
theorem exists_attached_neighbor_of_moved_card_seventySeven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 9)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hfixed : ∀ x : ({v : V | τ v = v} : Set V),
      (G.induce {v : V | τ v = v}).degree x = 2)
    (hMcard : Fintype.card ({x : V | τ x ≠ x} : Set V) = 77)
    {u v w : V} (hu : τ u = u) (hv : τ v = v) (hw : τ w = w)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : v ≠ w)
    {x : V} (hxmoved : τ x ≠ x)
    (hxout : x ∉ movedNeighborFinset G τ u ∪ movedNeighborFinset G τ v ∪ movedNeighborFinset G τ w) :
    ∃ a ∈ movedNeighborFinset G τ u, G.Adj x a := by
  classical
  let A := movedNeighborFinset G τ u
  let B := movedNeighborFinset G τ v
  let C := movedNeighborFinset G τ w
  let M := Finset.univ.filter (fun x : V => τ x ≠ x)
  let T := A ∪ B ∪ C
  let D := M \ T
  have hA : A.card = 7 := card_movedNeighborFinset_eq_seven G τ u hu (hreg u) (hfixed ⟨u, hu⟩)
  have hB : B.card = 7 := card_movedNeighborFinset_eq_seven G τ v hv (hreg v) (hfixed ⟨v, hv⟩)
  have hC : C.card = 7 := card_movedNeighborFinset_eq_seven G τ w hw (hreg w) (hfixed ⟨w, hw⟩)
  have hAB : Disjoint A B := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hu hv (G.ne_of_adj huv)
  have hAC : Disjoint A C := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hu hw (G.ne_of_adj huw)
  have hBC : Disjoint B C := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hv hw hvw
  have hT : T.card = 21 := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint hAB, hA, hB, hC]
  have hTM : T ⊆ M := by
    intro x hx
    simp only [T, Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    all_goals
      simp only [A, B, C, mem_movedNeighborFinset] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx.2⟩
  have hDM : D.card + 21 = M.card := by
    have h := Finset.card_sdiff_add_card_eq_card hTM
    simpa only [hT] using h
  let b : V → ℕ := fun x => (G.neighborFinset x ∩ A).card
  have hzero : ∀ x, x ≠ u → x ∉ D → b x = 0 := by
    intro x hxu hxD
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨hxa, ha⟩ := Finset.mem_inter.mp ha
    have hxa := (G.mem_neighborFinset x a).mp hxa
    have ha' := (mem_movedNeighborFinset G τ u a).mp ha
    by_cases hxf : τ x = x
    · exact hxu (fixed_neighbors_eq_of_moved hfree τ hmap ha'.2 hxf hu hxa.symm ha'.1.symm)
    · have hxM : x ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxf⟩
      have hxT : x ∈ T := by
        by_contra h
        exact hxD (Finset.mem_sdiff.mpr ⟨hxM, h⟩)
      simp only [T, Finset.mem_union] at hxT
      rcases hxT with (hxA | hxB) | hxC
      · have hx' := (mem_movedNeighborFinset G τ u x).mp hxA
        exact not_adj_moved_neighbors_of_fixed_period_seven G hfree τ hperiod hmap
          u hu (hreg u) (hfixed ⟨u, hu⟩) hx'.1 ha'.1 hx'.2 ha'.2 hxa
      · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ hu hv huv ha hxB hxa.symm
      · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ hu hw huw ha hxC hxa.symm
  have hpoint : ∀ x : V, b x ≤ (if x = u then A.card else 0) + (if x ∈ D then 1 else 0) := by
    intro x
    by_cases hxu : x = u
    · have hle : b x ≤ A.card := Finset.card_le_card Finset.inter_subset_right
      simp only [if_pos hxu]
      omega
    · have hle : b x ≤ 1 := card_neighbor_inter_movedNeighborFinset_le_one G hfree τ hxu
      by_cases hxD : x ∈ D
      · simpa only [if_neg hxu, if_pos hxD, zero_add] using hle
      · rw [hzero x hxu hxD]
        exact Nat.zero_le _
  have hM : M.card = 77 := by
    have heq : M = ({x : V | τ x ≠ x} : Set V).toFinset := by ext x; simp [M]
    rw [heq, Set.toFinset_card, hMcard]
  have hD : D.card = 56 := by omega
  have htotal : (∑ x : V, b x) = 63 := by
    rw [show (∑ x : V, b x) = ∑ a ∈ A, G.degree a from sum_card_neighbor_inter_eq_sum_degree G A]
    simp [hreg, hA]
  have hsumEq : (∑ x : V, b x) =
      ∑ x : V, ((if x = u then A.card else 0) + (if x ∈ D then 1 else 0)) := by
    simp [Finset.sum_add_distrib, htotal, hA, hD]
  have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun z _ => hpoint z)).mp hsumEq
  have hxD : x ∈ D := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxmoved⟩, hxout⟩
  have hxu : x ≠ u := by intro h; subst x; exact hxmoved hu
  have hbx : b x = 1 := by
    simpa only [if_neg hxu, if_pos hxD, zero_add] using hall x (Finset.mem_univ x)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset x ∩ A).card by change 0 < b x; rw [hbx]; decide)
  exact ⟨a, (Finset.mem_inter.mp ha).2, (G.mem_neighborFinset x a).mp (Finset.mem_inter.mp ha).1⟩

end Erdos85

/-!
# A second-neighbour cover bounds degree

In a C₄-free graph, if every neighbour of `a` has a neighbour in a finite set
`B` not containing `a`, then `degree a ≤ card B`. Choosing such a neighbour
defines an injection: two preimages would be two common neighbours of `a`
and a vertex of `B`. This packages the final eight-walk/seven-endpoint
pigeonhole step in the order-seven argument for Erdős problem 85.
-/

namespace Erdos85

/-- A second-neighbour cover excluding the centre has at least its degree. -/
theorem degree_le_card_of_neighbor_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (a : V) (B : Finset V) (ha : a ∉ B)
    (hcover : ∀ u, G.Adj a u → ∃ b ∈ B, G.Adj u b) :
    G.degree a ≤ B.card := by
  classical
  let f : G.neighborSet a → B := fun u =>
    ⟨(hcover u u.property).choose, (hcover u u.property).choose_spec.1⟩
  have hfadj : ∀ u : G.neighborSet a, G.Adj u (f u) := by
    intro u
    exact (hcover u u.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hab : a ≠ (f u).val := by
      intro heq
      exact ha (heq.symm ▸ (f u).property)
    have hvb : G.Adj v (f u) := by
      rw [huv]
      exact hfadj v
    exact hfree (containsC4_of_two_common hab hne
      u.property.symm (hfadj u) v.property.symm hvb)
  have h := Fintype.card_le_of_injective f hinj
  simpa only [G.card_neighborSet_eq_degree, Fintype.card_coe] using h

/-- Too few second-neighbour endpoints force a C₄. -/
theorem containsC4_of_neighbor_cover_card_lt_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (ha : a ∉ B)
    (hcover : ∀ u, G.Adj a u → ∃ b ∈ B, G.Adj u b)
    (hcard : B.card < G.degree a) : containsC4 V G := by
  by_contra hfree
  exact (Nat.not_le_of_lt hcard) (degree_le_card_of_neighbor_cover G hfree a B ha hcover)

end Erdos85

namespace Erdos85

/-- At order78 or80, every period-seven adjacency-preserving map of a
    C4-free minimum-degree-nine graph is the identity. -/
theorem no_nonidentity_period_seven_of_card_seventyEight_or_eighty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78 ∨ Fintype.card V = 80)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) : τ = id := by
  classical
  by_contra hne
  have hmoved : ∃ x, τ x ≠ x := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨hN, hF⟩ := card_eighty_fixed_three_of_period_seven G hfree hmin hcard τ hperiod hmap hmoved
  have hfixed := (fixed_graph_of_period_seven_card_seventyEight_or_eighty
    G hfree hmin hcard τ hperiod hmap hmoved).2
  have hreg : ∀ x, G.degree x = 9 :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by norm_num) hmin (by omega)
  let F : Set V := {x : V | τ x = x}
  let M : Set V := {x : V | τ x ≠ x}
  change Fintype.card F = 3 at hF
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun x => τ x = x) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hpart
  change Fintype.card F + Fintype.card M = Fintype.card V at hpart
  have hM : Fintype.card M = 77 := by omega
  letI : Nonempty F := Fintype.card_pos_iff.mp (by omega)
  let u : F := Classical.choice inferInstance
  have hpair : ((G.induce F).neighborFinset u).card = 2 := hfixed u
  obtain ⟨v, w, hvw, hset⟩ := Finset.card_eq_two.mp hpair
  have huv : G.Adj u.val v.val := by
    have hmem : v ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u v).mp hmem
  have huw : G.Adj u.val w.val := by
    have hmem : w ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u w).mp hmem
  have huvne : u ≠ v := by intro h; have := G.ne_of_adj huv; exact this (congrArg Subtype.val h)
  have huwne : u ≠ w := by intro h; have := G.ne_of_adj huw; exact this (congrArg Subtype.val h)
  have hall : ∀ z : F, z = u ∨ z = v ∨ z = w := by
    have heq : ({u, v, w} : Finset F) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [hF, huvne, huwne, hvw]
    intro z
    have hz : z ∈ ({u, v, w} : Finset F) := by rw [heq]; exact Finset.mem_univ z
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hvwadj : G.Adj v.val w.val := by
    have htwo : 1 < ((G.induce F).neighborFinset v).card := by
      change 1 < (G.induce F).degree v
      rw [hfixed v]
      decide
    obtain ⟨z, hz, hzu⟩ := Finset.exists_mem_ne htwo u
    have hvz := ((G.induce F).mem_neighborFinset v z).mp hz
    rcases hall z with h | h | h
    · exact False.elim (hzu h)
    · subst z
      exact False.elim (G.irrefl hvz)
    · subst z
      exact hvz
  let A := movedNeighborFinset G τ u.val
  let B := movedNeighborFinset G τ v.val
  let C := movedNeighborFinset G τ w.val
  have hA : A.card = 7 := card_movedNeighborFinset_eq_seven G τ u.val u.property (hreg _) (hfixed u)
  have hB : B.card = 7 := card_movedNeighborFinset_eq_seven G τ v.val v.property (hreg _) (hfixed v)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have ha' := (mem_movedNeighborFinset G τ u.val a).mp ha
  let E := insert v.val B
  have hvB : v.val ∉ B := by simp [B]
  have hE : E.card = 8 := by rw [Finset.card_insert_of_notMem hvB, hB]
  have haE : a ∉ E := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · subst a
      exact ha'.2 v.property
    · have hd := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap u.property v.property (G.ne_of_adj huv)
      exact Finset.disjoint_left.mp hd ha h
  have hcover : ∀ z, G.Adj a z → ∃ b ∈ E, G.Adj z b := by
    intro z haz
    by_cases hzu : z = u.val
    · subst z
      exact ⟨v.val, Finset.mem_insert_self _ _, huv⟩
    · have hzmoved : τ z ≠ z := by
        intro hz
        exact hzu (fixed_neighbors_eq_of_moved hfree τ hmap ha'.2 hz u.property haz ha'.1.symm)
      have hzout : z ∉ A ∪ B ∪ C := by
        intro h
        rcases Finset.mem_union.mp h with h | hC
        · rcases Finset.mem_union.mp h with hA | hB
          · have hz' := (mem_movedNeighborFinset G τ u.val z).mp hA
            exact not_adj_moved_neighbors_of_fixed_period_seven G hfree τ hperiod hmap
              u.val u.property (hreg _) (hfixed u) ha'.1 hz'.1 ha'.2 hz'.2 haz
          · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ u.property v.property huv ha hB haz
        · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ u.property w.property huw ha hC haz
      have hzout' : z ∉ B ∪ A ∪ C := by simpa only [Finset.union_comm] using hzout
      obtain ⟨b, hb, hzb⟩ := exists_attached_neighbor_of_moved_card_seventySeven G hfree hreg τ hperiod hmap
        hfixed hM v.property u.property w.property huv.symm hvwadj (G.ne_of_adj huw) hzmoved hzout'
      exact ⟨b, Finset.mem_insert_of_mem hb, hzb⟩
  exact hfree (containsC4_of_neighbor_cover_card_lt_degree G a E haE hcover (by rw [hE, hreg]; decide))

end Erdos85

#print axioms Erdos85.exists_attached_neighbor_of_moved_card_seventySeven
#print axioms Erdos85.no_nonidentity_period_seven_of_card_seventyEight_or_eighty
