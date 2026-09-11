import Proofs.Erdos85FixedBoundary
import Proofs.Erdos85FixedNeighbors
import Proofs.Erdos85GadgetCounting
import Proofs.Erdos85MovedCard
import Proofs.Erdos85PrimeFixedDegree
import Proofs.Erdos85PrimeOrbitMatching
import Proofs.Erdos85TwoNineDegreeReduction


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

#print axioms Erdos85.seventySeven_le_card_moved_of_fixed_neighbors

#print axioms Erdos85.card_eighty_fixed_three_of_period_seven

#print axioms Erdos85.no_nonidentity_period_seven_of_card_seventyEight
