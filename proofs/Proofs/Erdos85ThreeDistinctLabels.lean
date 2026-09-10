import Mathlib

namespace Erdos85

/-- Package three distinct witnesses, retaining a predicate attached to each row. -/
theorem three_distinct_labels {V : Type*} (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (P : Fin 3 → V → Prop) (h₀ : P 0 a) (h₁ : P 1 b) (h₂ : P 2 c) :
    ∃ s : Fin 3 → V, Function.Injective s ∧ ∀ k, P k (s k) := by
  refine ⟨![a,b,c], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro k
    fin_cases k <;> simpa

end Erdos85
#print axioms Erdos85.three_distinct_labels
