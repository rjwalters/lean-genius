import Proofs.Erdos85PrimeFixedDegree
import Proofs.Erdos85FixedBoundary
import Proofs.Erdos85FourNineDegreeObstruction
import Proofs.Erdos85MovedCard
import Proofs.Erdos85TightCardinality

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
