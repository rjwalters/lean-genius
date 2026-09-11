import Proofs.Erdos85PrimeFixedDegree
import Proofs.Erdos85FixedBoundary
import Proofs.Erdos85MovedCard
import Proofs.Erdos85TwoNineDegreeReduction

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
