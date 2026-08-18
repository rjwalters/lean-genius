import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # Cycle-type matching for bipartite two-factor shadows

A two-regular bipartite block is the union of two perfect matchings.  If the
matchings are encoded by equivalences `f g : S ≃ T`, its distance-two shadows
on the two shores are the permutations `f⁻¹g` and `gf⁻¹`.  They are conjugate
across `f`, hence have identical cycle data.  This is independent of the
order-64 census and is the q-generic algebra behind owner-factor cycle-type
matching.
-/

namespace Erdos85

open Equiv

/-- The distance-two shadow on the source shore of two perfect matchings. -/
def bipartiteLeftShadow {S T : Type*} (f g : S ≃ T) : Equiv.Perm S :=
  g.trans f.symm

/-- The distance-two shadow on the target shore of two perfect matchings. -/
def bipartiteRightShadow {S T : Type*} (f g : S ≃ T) : Equiv.Perm T :=
  f.symm.trans g

/-- Conjugacy of permutations whose underlying finite types may differ. -/
def PermConjugateAcross {S T : Type*} (p : Equiv.Perm S)
    (q : Equiv.Perm T) : Prop :=
  ∃ e : S ≃ T, ∀ x, e (p x) = q (e x)

/-- The two shore shadows of a bipartite two-factor are conjugate. -/
theorem bipartiteShadows_conjugateAcross {S T : Type*} (f g : S ≃ T) :
    PermConjugateAcross (bipartiteLeftShadow f g)
      (bipartiteRightShadow f g) := by
  refine ⟨f, fun x => ?_⟩
  simp [bipartiteLeftShadow, bipartiteRightShadow]

theorem perm_pow_intertwine {S T : Type*}
    {p : Equiv.Perm S} {q : Equiv.Perm T} (e : S ≃ T)
    (he : ∀ x, e (p x) = q (e x)) (n : ℕ) (x : S) :
    e ((p ^ n) x) = (q ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change e ((p ^ n) (p x)) = (q ^ n) (q (e x))
      rw [ih, he x]

theorem PermConjugateAcross.pow_apply {S T : Type*}
    {p : Equiv.Perm S} {q : Equiv.Perm T}
    (h : PermConjugateAcross p q) (n : ℕ) :
    ∃ e : S ≃ T, ∀ x, e ((p ^ n) x) = (q ^ n) (e x) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, perm_pow_intertwine e he n⟩

/-- Fixed points of every power correspond across a cross-type conjugacy. -/
noncomputable def PermConjugateAcross.fixedPointEquiv {S T : Type*}
    {p : Equiv.Perm S} {q : Equiv.Perm T}
    (h : PermConjugateAcross p q) (n : ℕ) :
    {x : S // (p ^ n) x = x} ≃ {y : T // (q ^ n) y = y} := by
  let e := h.choose
  have he : ∀ x, e (p x) = q (e x) := h.choose_spec
  have hpow : ∀ x, e ((p ^ n) x) = (q ^ n) (e x) :=
    perm_pow_intertwine e he n
  refine
    { toFun := fun x => ⟨e x, ?_⟩
      invFun := fun y => ⟨e.symm y, ?_⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  · rw [← hpow, x.property]
  · apply e.injective
    rw [e.apply_symm_apply, hpow, e.apply_symm_apply, y.property]

/-- Every power of the two shadows has the same number of fixed points.
This is a cycle-type-complete invariant for finite permutations. -/
theorem bipartiteShadows_fixedPoint_card_eq {S T : Type*}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (f g : S ≃ T) (n : ℕ) :
    Fintype.card {x : S // ((bipartiteLeftShadow f g) ^ n) x = x} =
      Fintype.card {y : T // ((bipartiteRightShadow f g) ^ n) y = y} := by
  classical
  exact Fintype.card_congr
    ((bipartiteShadows_conjugateAcross f g).fixedPointEquiv n)

/-- The cycle profile records the number of fixed points of every power. -/
def permutationCycleProfile (S : Type*) [Fintype S] [DecidableEq S]
    (p : Equiv.Perm S) : ℕ → ℕ :=
  fun n => Fintype.card {x : S // (p ^ n) x = x}

/-- Exact q-generic cycle-profile matching for the two shore shadows. -/
theorem bipartiteShadows_cycleProfile_eq {S T : Type*}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (f g : S ≃ T) :
    permutationCycleProfile S (bipartiteLeftShadow f g) =
      permutationCycleProfile T (bipartiteRightShadow f g) := by
  funext n
  exact bipartiteShadows_fixedPoint_card_eq f g n

theorem bipartiteLeftShadow_apply_eq_iff {S T : Type*}
    (f g : S ≃ T) (x : S) :
    bipartiteLeftShadow f g x = x ↔ g x = f x := by
  change f.symm (g x) = x ↔ g x = f x
  constructor
  · intro h
    rw [← f.apply_symm_apply (g x), h]
  · intro h
    rw [h, f.symm_apply_apply]

theorem bipartiteRightShadow_apply_eq_iff {S T : Type*}
    (f g : S ≃ T) (y : T) :
    bipartiteRightShadow f g y = y ↔ f.symm y = g.symm y := by
  simp [bipartiteRightShadow, Equiv.eq_symm_apply]

end Erdos85
