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
  sorry

/-- The ordinal hierarchy: ω < ω₁. -/
theorem omega_lt_omega1 : ω < Ordinal.omega1 := by
  sorry

/-- ω₁ < ω₁ ^ ω (ordinal exponentiation). -/
theorem omega1_lt_omega1_pow_omega : Ordinal.omega1 < Ordinal.omega1 ^ ω := by
  sorry

/-- ω₁ ^ ω < ω₁ ^ (ω + 1). -/
theorem omega1_pow_omega_lt_succ : Ordinal.omega1 ^ ω < Ordinal.omega1 ^ (ω + 1) := by
  sorry

/-- ω₁ ^ (ω + 1) < ω₁ ^ (ω + 2). -/
theorem omega1_pow_succ_lt : Ordinal.omega1 ^ (ω + 1) < Ordinal.omega1 ^ (ω + 2) := by
  sorry

/-- A disjunction P ∨ Q is equivalent to (¬P → Q) when decidable. -/
theorem or_iff_not_imp {P Q : Prop} : (P ∨ Q) ↔ (¬P → Q) := by
  sorry

/-- If a set is finite, it has no injective map from ℕ. -/
theorem Finite.no_injective_nat {V : Type*} [Finite V] :
    ¬∃ f : ℕ → V, Function.Injective f := by
  sorry

/-- No infinite path in a graph on a finite vertex set.
    An "infinite path" is an injective ℕ-indexed sequence of adjacent vertices. -/
theorem finite_no_infinite_path {V : Type*} [Finite V] (G : SimpleGraph V) :
    ¬∃ f : ℕ → V, Function.Injective f ∧ ∀ n, G.Adj (f n) (f (n + 1)) := by
  sorry

end Erdos601Aristotle
