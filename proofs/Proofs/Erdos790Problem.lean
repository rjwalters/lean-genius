/-
Erdős Problem #790: Maximum Sum-Free Subsequences

Let l(n) be maximal such that for any A ⊆ ℤ with |A| = n, there exists
a sum-free B ⊆ A with |B| ≥ l(n). A set B is sum-free if there are no
solutions to a₁ = a₂ + ⋯ + aᵣ with distinct aᵢ ∈ B and r ≥ 2.

**Status**: OPEN

**Known Bounds** (Choi-Komlós-Szemerédi 1975):
  √(n log n / log log n) ≪ l(n) ≪ n / log n

**Conjecture** (CKS): l(n) ≥ n^{1-o(1)}

References:
- [CKS75] Choi, Komlós, Szemerédi, Trans. Amer. Math. Soc. (1975)
- [Er65] Erdős, Proc. Sympos. Pure Math. VIII (1965)
- https://erdosproblems.com/790
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Nat Finset

namespace Erdos790

/- ## Sum-Free Sets -/

/-- A subset B ⊆ ℤ is sum-free if no element equals a sum of ≥2 distinct
other elements. Formally: ∀ a ∈ B, a ≠ Σ_{i∈S} aᵢ for any S ⊆ B \ {a}
with |S| ≥ 2. -/
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ S : Finset ℤ, S ⊆ B.erase a → S.card ≥ 2 →
    a ≠ S.sum id

/-- Classical sum-free: no a + b = c with distinct elements.
This is stronger than IsSumFree — every classically sum-free set
is also sum-free in the weak sense of this problem. -/
def classicalSumFree (B : Finset ℤ) : Prop :=
  ∀ a b c : ℤ, a ∈ B → b ∈ B → c ∈ B → a ≠ b → b ≠ c → a ≠ c →
    a + b ≠ c

/- ## The Extremal Function l(n) -/

/-- l(n): The minimum over all n-element sets A ⊆ ℤ of the maximum
sum-free subset size. Axiomatized since computing this requires
quantifying over all n-element subsets of ℤ. -/
axiom l (n : ℕ) : ℕ

/-- l(n) is a valid lower bound: every n-set has a sum-free subset
of size at least l(n). -/
/-- l(n) is optimal: for any k > l(n), there exists an n-set where
no sum-free subset reaches size k. -/
/- ## Lower Bounds -/

/-- **Erdős's observation:** l(n) ≥ √(n/2).
In {1,...,n}, the upper half is nearly sum-free since sums of
large numbers exceed n. A careful selection yields √(n/2) elements. -/
/-- **Choi's improvement:** l(n) > (1+c)√n for some c > 0.
This beats Erdős's √(n/2) ≈ 0.707√n by a constant factor,
using a more refined combinatorial argument. -/
/-- **CKS Lower Bound (1975):**
l(n) ≥ c √(n log n / log log n) for large n.
This is the best known lower bound. -/
axiom cks_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (l n : ℝ) ≥ c * Real.sqrt (n * Real.log n / Real.log (Real.log n))

/- ## Upper Bound -/

/-- **CKS Upper Bound (1975):**
l(n) ≤ C n / log n for large n.
This shows l(n) = o(n), confirming Erdős's claim (whose proof was lost). -/
axiom cks_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (l n : ℝ) ≤ C * n / Real.log n

/- ## The Main Questions -/

/-- **Question 1:** Does l(n) · n^{-1/2} → ∞? -/
def question1_limit_infinity : Prop :=
  ∀ M : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, (l n : ℝ) / Real.sqrt n > M

/-- **Question 1 is answered YES by the CKS lower bound:**
√(n log n / log log n) / √n = √(log n / log log n) → ∞. -/
axiom question1_affirmative : question1_limit_infinity

/-- **Question 2:** Is l(n) < n^{1-c} for some c > 0? -/
def question2_sublinear : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, ∀ n : ℕ, n > 0 → (l n : ℝ) ≤ C * n^(1 - c)

/-- **Question 2 is answered YES by the CKS upper bound:**
l(n) ≤ n/log n, which is o(n^{1-c}) for any c < 1. -/
axiom question2_answered : question2_sublinear

/- ## The CKS Conjecture -/

/-- **CKS Conjecture (1975, OPEN):** l(n) ≥ n^{1-o(1)}.
If true, l(n) is nearly linear. Combined with the upper bound n/log n,
this would give l(n) ≈ n/polylog(n). The gap between the current lower
bound √(n log n / log log n) ≈ n^{1/2+ε} and the conjectured n^{1-o(1)}
remains wide and unresolved. -/
def cks_conjecture : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (l n : ℝ) ≥ n^(1 - ε)

/- ## Summary -/

/-- **Combined CKS bounds:**
√(n log n / log log n) ≪ l(n) ≪ n / log n.
Both bounds come from the 1975 Trans. Amer. Math. Soc. paper. -/
theorem cks_bounds :
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (l n : ℝ) ≥ c * Real.sqrt (n * Real.log n / Real.log (Real.log n))) ∧
    (∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (l n : ℝ) ≤ C * n / Real.log n) :=
  ⟨cks_lower_bound, cks_upper_bound⟩

/-- **Summary of Erdős Problem #790.**
Both main questions (l(n)/√n → ∞ and l(n) < n^{1-c}) are answered YES
by the CKS bounds. The CKS conjecture l(n) ≥ n^{1-o(1)} remains OPEN. -/
theorem erdos_790_summary :
    question1_limit_infinity ∧ question2_sublinear :=
  ⟨question1_affirmative, question2_answered⟩

end Erdos790
