/-
  Aristotle targets for Erdős Problem #601
  Routine supporting lemmas for automated proof search.
  See Erdos601Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (P(α) for general limit ordinals)
  - Known results from Mathlib: ordinal arithmetic, transfinite induction,
    logical equivalences
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos601Aristotle

open Ordinal Cardinal

/-- Transfinite induction on ordinals.
    This is a well-known principle, available in Mathlib as Ordinal.induction. -/
theorem transfinite_induction (P : Ordinal → Prop)
    (h0 : P 0)
    (hS : ∀ α, P α → P (α + 1))
    (hL : ∀ α, α.IsLimit → (∀ β < α, P β) → P α) :
    ∀ α, P α := by
  intro α
  induction α using Ordinal.induction with
  | h α ih =>
    rcases Ordinal.zero_or_succ_or_limit α with rfl | ⟨β, rfl⟩ | hα
    · exact h0
    · exact hS β (ih β (Ordinal.lt_succ β))
    · exact hL α hα ih

/-- The ordinal hierarchy: ω < ω₁. -/
theorem omega_lt_omega1 : ω < Ordinal.omega1 :=
  Ordinal.omega0_lt_omega1

private theorem one_lt_omega1 : (1 : Ordinal) < Ordinal.omega1 :=
  Ordinal.one_lt_omega.trans Ordinal.omega0_lt_omega1

/-- ω₁ < ω₁ ^ ω (ordinal exponentiation). -/
theorem omega1_lt_omega1_pow_omega : Ordinal.omega1 < Ordinal.omega1 ^ ω := by
  conv_lhs => rw [← Ordinal.opow_one Ordinal.omega1]
  exact Ordinal.opow_lt_opow_right one_lt_omega1 Ordinal.one_lt_omega

/-- ω₁ ^ ω < ω₁ ^ (ω + 1). -/
theorem omega1_pow_omega_lt_succ : Ordinal.omega1 ^ ω < Ordinal.omega1 ^ (ω + 1) :=
  Ordinal.opow_lt_opow_right one_lt_omega1 (Ordinal.lt_succ ω)

/-- ω₁ ^ (ω + 1) < ω₁ ^ (ω + 2). -/
theorem omega1_pow_succ_lt : Ordinal.omega1 ^ (ω + 1) < Ordinal.omega1 ^ (ω + 2) :=
  Ordinal.opow_lt_opow_right one_lt_omega1 (Ordinal.lt_succ (ω + 1))

/-- A disjunction P ∨ Q is equivalent to (¬P → Q) when decidable. -/
theorem or_iff_not_imp {P Q : Prop} : (P ∨ Q) ↔ (¬P → Q) :=
  or_iff_not_imp_left

/-- If a set is finite, it has no injective map from ℕ. -/
theorem Finite.no_injective_nat {V : Type*} [Finite V] :
    ¬∃ f : ℕ → V, Function.Injective f := by
  intro ⟨f, hf⟩
  exact not_injective_infinite_finite f hf

/-- No infinite path in a graph on a finite vertex set. -/
theorem finite_no_infinite_path {V : Type*} [Finite V] (G : SimpleGraph V) :
    ¬∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1)) := by
  intro ⟨f, hf, _⟩
  exact not_injective_infinite_finite f hf

/-- Helper: resolving a disjunction when the left disjunct is false. -/
theorem resolve_left_or {P Q : Prop} (h : P ∨ Q) (hnp : ¬P) : Q :=
  h.resolve_left hnp

/-- If α < β then α ≠ β (ordinal strict order). -/
theorem ordinal_lt_ne {α β : Ordinal} (h : α < β) : α ≠ β :=
  ne_of_lt h

/-- ω + 1 > ω (successor ordinal). -/
theorem omega_lt_omega_succ : ω < ω + 1 :=
  Ordinal.lt_succ ω

/-- ω + 2 = (ω + 1) + 1. -/
theorem omega_add_two : ω + 2 = (ω + 1) + 1 := by
  omega

/-- ω + 1 < ω + 2 (strict ordinal inequality). -/
theorem omega_succ_lt_omega_add_two : ω + 1 < ω + 2 :=
  Ordinal.lt_succ (ω + 1)

/-- If a property holds for all β < α and α is a limit ordinal,
    then the property is determined by its values below α. -/
theorem limit_determined_by_below (α : Ordinal) (hα : α.IsLimit)
    (P : Ordinal → Prop) (h : ∀ β < α, P β) : ∀ β < α, P β :=
  h

/-- The image of an injective function from ℕ is infinite. -/
theorem injective_nat_image_infinite {V : Type*} (f : ℕ → V) (hf : Function.Injective f) :
    Set.Infinite (Set.range f) :=
  Set.infinite_range_of_injective hf

end Erdos601Aristotle
