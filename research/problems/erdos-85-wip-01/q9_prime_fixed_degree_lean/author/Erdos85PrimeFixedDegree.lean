import Proofs.Erdos85Problem
import Mathlib.GroupTheory.Perm.Cycle.Type

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
