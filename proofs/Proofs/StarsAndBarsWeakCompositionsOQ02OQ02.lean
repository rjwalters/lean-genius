import Mathlib.Data.Sym.Card
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositionsOQ02

/-
# Reflection Symmetry of Bounded Weak Compositions (`n ↦ kb − n`)

## What This Proves

The parent entry (`StarsAndBarsWeakCompositionsOQ02.lean`) counts the *bounded weak
compositions* of `n` into `k` parts with every part `≤ b`:

  `B(k, n, b) := #{f : Fin k → ℕ | ∑ i, f i = n, ∀ i, f i ≤ b}`,

and gives the inclusion–exclusion closed form
`B(k,n,b) = ∑_{j} (−1)^j C(k,j) C(n − (b+1)j + k − 1, …)`.

This entry proves the **reflection symmetry**

  `B(k, n, b) = B(k, k·b − n, b)`   (for `n ≤ k·b`),

by exhibiting the explicit bijection

  `f  ↦  (i ↦ b − f i)`,

which sends a composition of `n` (all parts `≤ b`) to a composition of `k·b − n`
(all parts `≤ b`), and is its own inverse up to the two sum-constraints. The map is
a genuine involution on the *shape* `i ↦ b − f i`; the two sum constraints `∑ f = n`
and `∑ f = kb − n` make domain and codomain distinct subtypes, so we package it as an
`Equiv` (`reflectEquiv`) whose `toFun` and `invFun` are both the reflection.

## Why it matters

`B(k, n, b)` is exactly the coefficient of `qⁿ` in the Gaussian binomial coefficient
`[k + b ; b]_q` (the `q`-analogue of `C(k+b, b)`). The reflection `n ↦ kb − n` is the
combinatorial witness of the palindromic symmetry of Gaussian binomial coefficients
`[m ; r]_q = [m ; r]_{q⁻¹} · q^{r(m−r)}`, specialised to `q = 1`. We do not formalise
`q`-binomials here; we prove the underlying finite bijection, which is the `q = 1`
content of that symmetry and is `Mathlib`-gap-free at that level.

## Free corollary

Combining the card symmetry with the parent's closed form yields an identity between
two inclusion–exclusion alternating sums (`closedForm_reflect`): the alternating sum
evaluated at `n` equals the one evaluated at `k·b − n`.

**Sorry count**: 0.  **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

open Finset

namespace StarsAndBarsReflect

/-- Bounded weak compositions of `n` into `k` parts, each part `≤ b`
(the type counted by the parent entry). -/
abbrev BC (k n b : ℕ) : Type := {f : Fin k → ℕ // (∑ i, f i = n) ∧ ∀ i, f i ≤ b}

/-- The total budget `∑ i, b = k·b` distributed over `k` parts. -/
private theorem sum_const_b (k b : ℕ) : ∑ _i : Fin k, b = k * b := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The reflection bijection.**  When `n ≤ k·b`, complementing each part
`f i ↦ b − f i` is a bijection from the bounded weak compositions of `n` onto those
of `k·b − n` (parts stay `≤ b`, and the total flips from `n` to `k·b − n`). -/
def reflectEquiv (k n b : ℕ) (hn : n ≤ k * b) : BC k n b ≃ BC k (k * b - n) b where
  toFun f := ⟨fun i => b - f.val i, by
    refine ⟨?_, fun i => Nat.sub_le _ _⟩
    rw [Finset.sum_tsub_distrib univ (fun i _ => f.2.2 i), sum_const_b, f.2.1]⟩
  invFun g := ⟨fun i => b - g.val i, by
    refine ⟨?_, fun i => Nat.sub_le _ _⟩
    rw [Finset.sum_tsub_distrib univ (fun i _ => g.2.2 i), sum_const_b, g.2.1,
      Nat.sub_sub_self hn]⟩
  left_inv f := by
    apply Subtype.ext; funext i
    exact Nat.sub_sub_self (f.2.2 i)
  right_inv g := by
    apply Subtype.ext; funext i
    exact Nat.sub_sub_self (g.2.2 i)

/-- **Reflection symmetry of the bounded-composition count.**
`B(k, n, b) = B(k, k·b − n, b)` whenever `n ≤ k·b`. -/
theorem card_boundedComposition_reflect (k n b : ℕ) (hn : n ≤ k * b) :
    Fintype.card (BC k n b) = Fintype.card (BC k (k * b - n) b) :=
  Fintype.card_congr (reflectEquiv k n b hn)

/-- The reflection is an involution: applying it twice returns to `B(k, n, b)`, since
`k·b − (k·b − n) = n`.  (Consistency check on `reflectEquiv`.) -/
theorem card_boundedComposition_reflect_reflect (k n b : ℕ) (hn : n ≤ k * b) :
    Fintype.card (BC k (k * b - (k * b - n)) b) = Fintype.card (BC k n b) := by
  rw [Nat.sub_sub_self hn]

/-- **Closed-form corollary.**  The parent's inclusion–exclusion alternating sum is
invariant under `n ↦ k·b − n`.  Both sides equal `(B(k, n, b) : ℤ)` by the parent's
`card_boundedComposition` together with the reflection symmetry. -/
theorem closedForm_reflect (k n b : ℕ) (hn : n ≤ k * b) :
    (∑ j ∈ Finset.range (k + 1), (k.choose j : ℤ) * ((-1 : ℤ) ^ j *
        (if (b + 1) * j ≤ n then
          ((n - (b + 1) * j + k - 1).choose (n - (b + 1) * j) : ℤ) else 0)))
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℤ) * ((-1 : ℤ) ^ j *
        (if (b + 1) * j ≤ k * b - n then
          ((k * b - n - (b + 1) * j + k - 1).choose (k * b - n - (b + 1) * j) : ℤ)
            else 0)) := by
  rw [← StarsAndBarsBounded.card_boundedComposition k n b,
      ← StarsAndBarsBounded.card_boundedComposition k (k * b - n) b]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (card_boundedComposition_reflect k n b hn)

end StarsAndBarsReflect
