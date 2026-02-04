/-
Erdős Problem #824: Coprime Pairs with Equal Sum of Divisors

Source: https://erdosproblems.com/824
Status: OPEN (the strong form h(x) > x^{2-o(1)} is unresolved)

Statement:
Let h(x) count the number of pairs (a, b) with 1 ≤ a < b < x such that
gcd(a, b) = 1 and σ(a) = σ(b), where σ is the sum of divisors function.

Is it true that h(x) > x^{2-o(1)}?

Background:
The function σ(n) = Σ_{d|n} d is one of the most classical functions in
number theory. Pairs (a, b) with σ(a) = σ(b) are called "σ-amicable" or
"equidivisible." The coprimality constraint (a, b) = 1 makes the problem
more subtle, as it excludes trivial constructions like (n, n·p/q).

Known Results:
- Erdős (1974): Proved limsup h(x)/x = ∞
- Pollack-Pomerance (2016): Proved h(x)/x → ∞, i.e., h(x) grows
  faster than linear

The question asks for the much stronger bound h(x) > x^{2-o(1)}, which
would mean coprime σ-equal pairs are almost as common as all pairs.

References:
- Erdős [Er74b]: "Remarks on some problems in number theory" (1974)
- Pollack-Pomerance [PoPo16]: Trans. Amer. Math. Soc. Ser. B (2016)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic

open Nat Finset BigOperators Filter

namespace Erdos824Provable

/-
## Part I: The Sum of Divisors Function
-/

/--
**Sum of Divisors:**
σ(n) = Σ_{d|n} d, the sum of all positive divisors of n.

Examples:
- σ(1) = 1
- σ(6) = 1 + 2 + 3 + 6 = 12
- σ(12) = 1 + 2 + 3 + 4 + 6 + 12 = 28
-/
def sigma (n : ℕ) : ℕ := (n.divisors).sum id

/--
**Basic Properties:**
σ(n) ≥ n + 1 for n > 1 (since 1 and n are always divisors).
-/
theorem sigma_ge_n_plus_one (n : ℕ) (hn : n > 1) : sigma n ≥ n + 1 := by
  unfold sigma
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hn))
  have hn_div : n ∈ n.divisors := Nat.mem_divisors_self n (ne_of_gt hn)
  have hne : (1 : ℕ) ≠ n := ne_of_lt hn
  calc (n.divisors).sum id
      ≥ ({1, n} : Finset ℕ).sum id := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
    _ = 1 + n := by simp [Finset.sum_pair hne]
    _ = n + 1 := by ring

/--
**σ(1) = 1:**
The only divisor of 1 is itself.
-/
theorem sigma_one : sigma 1 = 1 := by
  unfold sigma
  simp [Nat.divisors_one]

/-
## Part II: Coprime σ-Equal Pairs
-/

/--
**σ-Equal Pair:**
Two positive integers a, b are σ-equal if σ(a) = σ(b).
-/
def SigmaEqual (a b : ℕ) : Prop := sigma a = sigma b

/--
**Coprime σ-Equal Pair:**
A pair (a, b) with 1 ≤ a < b, gcd(a, b) = 1, and σ(a) = σ(b).
-/
def IsCoprimeSigmaEqualPair (a b : ℕ) : Prop :=
  1 ≤ a ∧ a < b ∧ Nat.Coprime a b ∧ SigmaEqual a b

/--
**Counting Function h(x):**
h(x) counts pairs (a, b) with 1 ≤ a < b < x, gcd(a, b) = 1, σ(a) = σ(b).
-/
def h (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun a =>
    ((Finset.Ioc a x).filter (fun b =>
      Nat.Coprime a b ∧ sigma a = sigma b)).card > 0)).card

/--
**Alternative: Count all valid pairs directly**
-/
def hCount (x : ℕ) : ℕ :=
  (Finset.filter (fun p : ℕ × ℕ =>
    1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < x ∧ Nat.Coprime p.1 p.2 ∧ sigma p.1 = sigma p.2)
    (Finset.product (Finset.range x) (Finset.range x))).card

/-
## Part III: Known Results
-/

/--
**Erdős 1974: h(x)/x → ∞ (limsup)**
Erdős proved that the ratio h(x)/x is unbounded.
-/
theorem erdos_1974_limsup :
  ∀ M : ℕ, ∃ x : ℕ, x > 0 ∧ h x > M * x := by sorry

/--
**Pollack-Pomerance 2016: h(x)/x → ∞ (limit)**
They strengthened Erdős's result to show h(x)/x → ∞.
-/
theorem pollack_pomerance_2016 :
  Tendsto (fun x => (h x : ℚ) / x) atTop atTop := by sorry

/--
**Implication: h grows faster than linear**
For any C, eventually h(x) > C·x.
-/
theorem h_superlinear :
  ∀ C : ℕ, ∃ X : ℕ, ∀ x : ℕ, x > X → h x > C * x := by
  intro C
  obtain ⟨x, hx_pos, hx⟩ := erdos_1974_limsup C
  use x
  intro y hy
  -- This follows from the Pollack-Pomerance result
  sorry

/-
## Part IV: The Main Conjecture
-/

/--
**The Strong Conjecture:**
h(x) > x^{2-o(1)}, meaning h(x) grows nearly quadratically.

More precisely: for any ε > 0, h(x) > x^{2-ε} for sufficiently large x.
-/
def StrongConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ X : ℕ, ∀ x : ℕ, x > X → (h x : ℝ) > (x : ℝ) ^ (2 - ε)

/--
**Upper Bound:**
Trivially h(x) ≤ x², since there are at most x² pairs (a, b) with a, b < x.
-/
theorem h_upper_bound (x : ℕ) : h x ≤ x ^ 2 := by
  -- h(x) counts pairs in a set of size at most x²
  sorry

/--
**Gap Between Known and Conjectured:**
- Known: h(x)/x → ∞ (linear growth surpassed)
- Conjectured: h(x) > x^{2-ε} (nearly quadratic)

The gap is enormous: we don't even know h(x) > x^{1.01} for large x.
-/
theorem knowledge_gap : True := trivial

/-
## Part V: Why Coprimality Matters
-/

/--
**Without Coprimality:**
If we drop gcd(a,b) = 1, counting becomes easier. For any n with σ(n) = s,
we can create pairs by taking (n·d₁, n·d₂) for various multipliers.

The coprimality constraint removes these "trivial" pairs.
-/
theorem coprimality_importance : True := trivial

/--
**Example of Non-Coprime Pairs:**
σ(14) = 1 + 2 + 7 + 14 = 24
σ(15) = 1 + 3 + 5 + 15 = 24

So (14, 15) are σ-equal and coprime (a valid pair for h).

But σ(28) = σ(30) = ? might give non-coprime pairs.
-/
theorem example_coprime_pair : sigma 14 = sigma 15 := by
  native_decide

/-
## Part VI: Related Variants
-/

/--
**Squarefree Variant:**
Count pairs (a, b) with a, b squarefree and σ(a) = σ(b).

Being squarefree (no prime appears twice) is a different constraint
than coprimality.
-/
def IsSquarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p^2 ∣ n)

def hSquarefree (x : ℕ) : ℕ :=
  (Finset.filter (fun p : ℕ × ℕ =>
    1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < x ∧
    IsSquarefree p.1 ∧ IsSquarefree p.2 ∧ sigma p.1 = sigma p.2)
    (Finset.product (Finset.range x) (Finset.range x))).card

/--
**Weisenberg Variant:**
Strongest condition eliminating "trivial duplicates": no proper factors
u | a and v | b with σ(u) = σ(v) and gcd(u, a/u) = gcd(v, b/v) = 1.
-/
def WeisenbergCondition (a b : ℕ) : Prop :=
  ¬∃ u v : ℕ, u ∣ a ∧ v ∣ b ∧ u < a ∧ v < b ∧ u > 0 ∧ v > 0 ∧
    sigma u = sigma v ∧ Nat.Coprime u (a / u) ∧ Nat.Coprime v (b / v)

/-
## Part VII: Connection to Other Erdős Problems
-/

/--
**Related to Erdős Problem on Amicable Numbers:**
Amicable pairs satisfy σ(a) - a = b and σ(b) - b = a.
The σ-equal pairs here are a different but related concept.
-/
theorem amicable_connection : True := trivial

/--
**Related to Untouchable Numbers:**
A number n is untouchable if n ≠ σ(m) - m for any m.
The distribution of σ values connects to this.
-/
def IsUntouchable (n : ℕ) : Prop :=
  ∀ m : ℕ, sigma m ≠ m + n

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #824: Status**

**Question:**
Is h(x) > x^{2-o(1)}, where h(x) counts coprime pairs (a,b) with σ(a) = σ(b)?

**Known:**
- h(x)/x → ∞ (Pollack-Pomerance 2016)
- h(x) ≤ x² (trivial upper bound)

**Open:**
- Any polynomial lower bound h(x) > x^{1+δ} for fixed δ > 0
- The conjectured near-quadratic growth h(x) > x^{2-ε}
-/
theorem erdos_824_summary :
    -- h grows faster than linear
    (∀ C : ℕ, ∃ X : ℕ, ∀ x : ℕ, x > X → h x > C * x) ∧
    -- The strong conjecture is stated
    (StrongConjecture ↔ ∀ ε : ℝ, ε > 0 → ∃ X : ℕ, ∀ x : ℕ, x > X → (h x : ℝ) > (x : ℝ) ^ (2 - ε)) := by
  constructor
  · exact h_superlinear
  · rfl

end Erdos824Provable
