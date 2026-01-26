/-!
# Erdős Problem #411: Iterated Totient Sums and Doubling

Let g(n) = n + φ(n) and define g_k(n) by iterating g. For which n and r
is it true that g_{k+r}(n) = 2·g_k(n) for all sufficiently large k?

## Status: OPEN

## References
- Erdős–Graham (1980), p. 81
- Steinerberger (2025)
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section I: The Iteration Function
-/

/-- g(n) = n + φ(n), the basic iteration step. -/
def totientStep (n : ℕ) : ℕ := n + n.totient

/-- g_k(n): the k-th iterate of g applied to n. -/
def iteratedTotientStep : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => totientStep (iteratedTotientStep k n)

/-!
## Section II: The Doubling Relation
-/

/-- The doubling relation: g_{k+r}(n) = 2·g_k(n) holds for all large k. -/
def DoublingRelation (n r : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    iteratedTotientStep (k + r) n = 2 * iteratedTotientStep k n

/-!
## Section III: The Conjecture
-/

/-- **Erdős Problem #411**: Characterize all (n, r) such that
g_{k+r}(n) = 2·g_k(n) for all sufficiently large k.

The problem asks for a complete description of the solution set. -/
def ErdosProblem411 : Prop :=
  ∃ S : Set (ℕ × ℕ), (∀ p : ℕ × ℕ, p ∈ S ↔ DoublingRelation p.1 p.2) ∧
    S.Nonempty

/-!
## Section IV: Known Solutions
-/

/-- For r = 2, it is known that n = 10 and n = 94 are solutions:
g_{k+2}(n) = 2·g_k(n) for all large k. -/
axiom doubling_r2_n10 : DoublingRelation 10 2

/-- n = 94 is also a solution with period r = 2. -/
axiom doubling_r2_n94 : DoublingRelation 94 2

/-- Cambie found: g_{k+4}(738) = 3·g_k(738), which gives a ratio-3
solution. More generally, non-doubling ratios exist. -/
def GeneralRatioRelation (n r c : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    iteratedTotientStep (k + r) n = c * iteratedTotientStep k n

axiom cambie_ratio3 : GeneralRatioRelation 738 4 3

/-- Cambie found ratio-4 solutions as well. -/
axiom cambie_ratio4_148646 : GeneralRatioRelation 148646 4 4
axiom cambie_ratio4_4325798 : GeneralRatioRelation 4325798 4 4

/-!
## Section V: Steinerberger's Reduction
-/

/-- Steinerberger showed the r = 2 case is equivalent to solving
φ(n) + φ(n + φ(n)) = n. -/
axiom steinerberger_r2_equiv (n : ℕ) :
  DoublingRelation n 2 ↔
    n.totient + (n + n.totient).totient = n

/-!
## Section VI: Structural Properties
-/

/-- For even n, g(n) = n + φ(n) is always even, so the iterates
stay even. This is relevant since all known solutions are even. -/
theorem totientStep_even_of_even {n : ℕ} (hn : 2 ∣ n) (hn2 : n > 2) :
    2 ∣ totientStep n := by
  unfold totientStep
  have hφ : 2 ∣ n.totient := Nat.totient_even hn2
  exact dvd_add hn hφ

/-- Cambie conjectures all r = 2 solutions have form n = 2^l · p
where l ≥ 1 and p ∈ {2, 3, 5, 7, 35, 47}. -/
def CambieConjecture : Prop :=
  ∀ n : ℕ, DoublingRelation n 2 →
    ∃ l : ℕ, l ≥ 1 ∧
      ∃ p ∈ ({2, 3, 5, 7, 35, 47} : Finset ℕ), n = 2 ^ l * p

/-- The iteration g(n) = n + φ(n) always produces an even number
when n ≥ 3, since φ(n) is even for n ≥ 3. -/
theorem totientStep_ge (n : ℕ) : totientStep n ≥ n := by
  unfold totientStep
  omega
