/-
Zeckendorf Representation OQ-01: Zeckendorf's Theorem (Existence and Uniqueness)

**Zeckendorf's theorem** (1972): every natural number `n` has a *unique* representation
as a sum of non-consecutive Fibonacci numbers — i.e. as `∑ fib aᵢ` where the index
list `a` is strictly decreasing with gaps `≥ 2` (so no two consecutive Fibonacci
numbers appear).

Mathlib formalizes the canonical algorithm (`Nat.zeckendorf`, greedy: repeatedly
subtract the largest Fibonacci number `≤ n`), the validity predicate
`List.IsZeckendorfRep` (gap-`≥2` chain on the index list), the round-trip lemmas, and
packages the whole thing as the equivalence `Nat.zeckendorfEquiv : ℕ ≃ {l // IsZeckendorfRep l}`.
This entry surfaces Zeckendorf's theorem as the two consumer statements a reader
expects — **existence** and **uniqueness** — and records the bijection.

Main results:
  • `zeckendorf_existence`  — every `n` is the Fibonacci-sum of some valid representation.
  • `zeckendorf_uniqueness` — two valid representations with the same Fibonacci-sum are equal.
  • `zeckendorf_unique`     — existence + uniqueness bundled as `∃!`.
  • `zeckendorf_bijective`  — the representation map `ℕ ≃ {l // IsZeckendorfRep l}` is a bijection.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- E. Zeckendorf, *Représentation des nombres naturels par une somme de nombres de
  Fibonacci ou de nombres de Lucas* (1972).
- Mathlib `Nat.zeckendorfEquiv`, `Nat.sum_zeckendorf_fib`, `Nat.zeckendorf_sum_fib`
  (Data/Nat/Fib/Zeckendorf.lean).
-/

import Mathlib

namespace ZeckendorfRepresentationOQ01

open Nat

/-- **Existence.** Every natural number `n` is the sum of the Fibonacci numbers indexed
    by a valid (non-consecutive) Zeckendorf representation. The witness is the canonical
    greedy representation `Nat.zeckendorf n`. -/
theorem zeckendorf_existence (n : ℕ) :
    ∃ l : List ℕ, List.IsZeckendorfRep l ∧ (l.map Nat.fib).sum = n :=
  ⟨Nat.zeckendorf n, isZeckendorfRep_zeckendorf n, sum_zeckendorf_fib n⟩

/-- **Uniqueness.** Two valid Zeckendorf representations with the same Fibonacci-sum are
    identical. Both equal the canonical representation of that common sum. -/
theorem zeckendorf_uniqueness {l₁ l₂ : List ℕ}
    (h₁ : List.IsZeckendorfRep l₁) (h₂ : List.IsZeckendorfRep l₂)
    (h : (l₁.map Nat.fib).sum = (l₂.map Nat.fib).sum) : l₁ = l₂ := by
  have e₁ := zeckendorf_sum_fib h₁
  have e₂ := zeckendorf_sum_fib h₂
  rw [← e₁, ← e₂, h]

/-- **Zeckendorf's theorem.** Every `n` has a *unique* representation as a sum of
    non-consecutive Fibonacci numbers. -/
theorem zeckendorf_unique (n : ℕ) :
    ∃! l : List ℕ, List.IsZeckendorfRep l ∧ (l.map Nat.fib).sum = n := by
  refine ⟨Nat.zeckendorf n, ⟨isZeckendorfRep_zeckendorf n, sum_zeckendorf_fib n⟩, ?_⟩
  rintro l ⟨hl, hsum⟩
  exact zeckendorf_uniqueness hl (isZeckendorfRep_zeckendorf n) (by rw [hsum, sum_zeckendorf_fib])

/-- The Zeckendorf representation map is a bijection between `ℕ` and the set of valid
    (non-consecutive) Fibonacci index lists. -/
theorem zeckendorf_bijective : Function.Bijective Nat.zeckendorfEquiv :=
  Nat.zeckendorfEquiv.bijective

/-! ## A concrete representation: 100 = 89 + 8 + 3 = fib 11 + fib 6 + fib 4

The index list `[11, 6, 4]` is strictly decreasing with gaps `≥ 2`, so it is a valid
Zeckendorf representation, and its Fibonacci-sum is `89 + 8 + 3 = 100`. -/

example : (([11, 6, 4].map Nat.fib).sum) = 100 := by decide
example : Nat.fib 11 = 89 ∧ Nat.fib 6 = 8 ∧ Nat.fib 4 = 3 := by decide

#check @zeckendorf_existence
#check @zeckendorf_uniqueness
#check @zeckendorf_unique
#check @zeckendorf_bijective

end ZeckendorfRepresentationOQ01
