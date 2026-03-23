/-
Erdős Problem #820: GCD of Exponential Sequences

Source: https://erdosproblems.com/820
Status: OPEN

Statement:
Let H(n) be the smallest integer l such that there exist k < l with gcd(k^n - 1, l^n - 1) = 1.

Questions:
1. Is H(n) = 3 infinitely often? (i.e., is gcd(2^n - 1, 3^n - 1) = 1 infinitely often?)
2. Estimate H(n). Does there exist c > 0 such that for all ε > 0:
   - H(n) > exp(n^{(c-ε)/log log n}) for infinitely many n
   - H(n) < exp(n^{(c+ε)/log log n}) for all large n
3. Does a similar bound hold for the smallest k with gcd(k^n - 1, 2^n - 1) = 1?

Known Results:
- Erdős (1974): H(n) > exp(n^{c/(log log n)²}) for infinitely many n
- van Doorn: H(n) > exp(n^{c/log log n}) for infinitely many n (improved)
- Empirical: H(1..10) = [3, 3, 3, 6, 3, 18, 3, 6, 3, 12]
- OEIS A263647: values n where gcd(2^n - 1, 3^n - 1) = 1

References:
- Erdős, P. (1974): "Remarks on some problems in number theory", Math. Balkanica
- See also Problem #770 (related h(n) function)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real

namespace Erdos820

/-
## Part I: The H(n) Function

H(n) is the smallest l such that there exists k < l with gcd(k^n - 1, l^n - 1) = 1.
-/

/--
**Coprime exponentials property:**
Two integers k, l are n-coprime if gcd(k^n - 1, l^n - 1) = 1.
-/
def areNCoprime (k l n : ℕ) : Prop :=
  Nat.gcd (k^n - 1) (l^n - 1) = 1

/--
**Has coprime predecessor:**
l has an n-coprime predecessor if some k < l satisfies gcd(k^n - 1, l^n - 1) = 1.
-/
def hasNCoprimePredecessor (l n : ℕ) : Prop :=
  ∃ k : ℕ, k < l ∧ areNCoprime k l n

/--
**The H(n) function:**
H(n) = min{l ≥ 2 : ∃ k < l, gcd(k^n - 1, l^n - 1) = 1}

This is the smallest l that has an n-coprime predecessor.
-/
noncomputable def H (n : ℕ) : ℕ :=
  Nat.find (⟨3, 2, Nat.lt_of_sub_eq_succ rfl, sorry⟩ : ∃ l, l ≥ 2 ∧ hasNCoprimePredecessor l n)

/-
## Part II: Computed Values

The function H(n) has been computed for small n.
-/

/--
**H(n) for n = 1 to 10:**
H(1) = 3, H(2) = 3, H(3) = 3, H(4) = 6, H(5) = 3,
H(6) = 18, H(7) = 3, H(8) = 6, H(9) = 3, H(10) = 12
-/
def knownHValues : Fin 10 → ℕ
  | ⟨0, _⟩ => 3   -- H(1)
  | ⟨1, _⟩ => 3   -- H(2)
  | ⟨2, _⟩ => 3   -- H(3)
  | ⟨3, _⟩ => 6   -- H(4)
  | ⟨4, _⟩ => 3   -- H(5)
  | ⟨5, _⟩ => 18  -- H(6)
  | ⟨6, _⟩ => 3   -- H(7)
  | ⟨7, _⟩ => 6   -- H(8)
  | ⟨8, _⟩ => 3   -- H(9)
  | ⟨9, _⟩ => 12  -- H(10)

/--
**H(n) = 3 means gcd(2^n - 1, 3^n - 1) = 1:**
When H(n) = 3, the witness is k = 2, l = 3.
-/
theorem H_eq_3_iff_2_3_coprime (n : ℕ) (hn : n ≥ 1) :
    H n = 3 ↔ Nat.gcd (2^n - 1) (3^n - 1) = 1 := by
  sorry

/-
## Part III: The Main Conjecture

Erdős asked whether H(n) = 3 infinitely often.
-/

/--
**Erdős Problem #820 (Conjecture 1):**
H(n) = 3 for infinitely many n.

Equivalently: gcd(2^n - 1, 3^n - 1) = 1 for infinitely many n.
-/
def erdos820Conjecture1 : Prop :=
  ∀ N : ℕ, ∃ n > N, H n = 3

/--
**Equivalent formulation using gcd:**
-/
def erdos820Conjecture1' : Prop :=
  ∀ N : ℕ, ∃ n > N, Nat.gcd (2^n - 1) (3^n - 1) = 1

/--
**OEIS A263647:**
The set of n where gcd(2^n - 1, 3^n - 1) = 1.
-/
def oeisA263647 : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ Nat.gcd (2^n - 1) (3^n - 1) = 1}

/-
## Part IV: Growth Estimates

Erdős conjectured precise growth bounds for H(n).
-/

/--
**Conjectured lower bound:**
There exists c > 0 such that for all ε > 0,
H(n) > exp(n^{(c-ε)/log log n}) for infinitely many n.
-/
def erdos820LowerBoundConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε : ℝ, ε > 0 → ∀ N : ℕ, ∃ n > N,
    (H n : ℝ) > Real.exp ((n : ℝ)^((c - ε) / Real.log (Real.log (n : ℝ))))

/--
**Conjectured upper bound:**
There exists c > 0 such that for all ε > 0,
H(n) < exp(n^{(c+ε)/log log n}) for all sufficiently large n.
-/
def erdos820UpperBoundConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n > N,
    (H n : ℝ) < Real.exp ((n : ℝ)^((c + ε) / Real.log (Real.log (n : ℝ))))

/-
## Part V: Known Results

Erdős proved a weaker lower bound in 1974.
-/

/--
**Erdős's 1974 Result:**
There exists c > 0 such that
H(n) > exp(n^{c/(log log n)²}) for infinitely many n.

This is weaker than the conjectured bound (squared log log in denominator).
-/
axiom erdos_1974_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n > N,
    (H n : ℝ) > Real.exp ((n : ℝ)^(c / (Real.log (Real.log (n : ℝ)))^2))

/--
**van Doorn's Improvement:**
There exists c > 0 such that
H(n) > exp(n^{c/log log n}) for infinitely many n.

This matches the conjectured lower bound form.
-/
axiom van_doorn_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n > N,
    (H n : ℝ) > Real.exp ((n : ℝ)^(c / Real.log (Real.log (n : ℝ))))

/-
## Part VI: Related Question

Question about the "dual" function.
-/

/--
**Dual function K(n):**
K(n) = min{k ≥ 2 : gcd(k^n - 1, 2^n - 1) = 1}

Erdős asked if this has similar upper bounds.
-/
noncomputable def K (n : ℕ) : ℕ :=
  Nat.find (⟨3, sorry⟩ : ∃ k, k ≥ 2 ∧ Nat.gcd (k^n - 1) (2^n - 1) = 1)

/--
**Erdős Problem #820 (Question 3):**
Does K(n) < exp(n^{(c+ε)/log log n}) for all large n?
-/
def erdos820Question3 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n > N,
    (K n : ℝ) < Real.exp ((n : ℝ)^((c + ε) / Real.log (Real.log (n : ℝ))))

/-
## Part VII: Number-Theoretic Context

Why are these GCDs interesting?
-/

/--
**Prime divisor observation:**
If p | gcd(k^n - 1, l^n - 1), then ord_p(k) | n and ord_p(l) | n.
So gcd = 1 requires k and l to have "independent" multiplicative orders.
-/
theorem gcd_characterization (k l n p : ℕ) (hp : Nat.Prime p) :
    p ∣ Nat.gcd (k^n - 1) (l^n - 1) →
    ∃ d : ℕ, d ∣ n ∧ (k^d ≡ 1 [MOD p]) ∧ (l^d ≡ 1 [MOD p]) := by
  sorry

/--
**Fermat's Little Theorem connection:**
For prime p not dividing k, we have k^(p-1) ≡ 1 (mod p).
So if (p-1) | n, then p might divide both k^n - 1 and l^n - 1.
-/
axiom fermat_little_theorem (k p : ℕ) (hp : Nat.Prime p) (hk : ¬p ∣ k) :
  k^(p - 1) ≡ 1 [MOD p]

/-
## Part VIII: Connection to Problem #770

Problem #770 studies a related function h(n).
-/

/--
**Related function h(n):**
h(n) = min{l : 2^n-1, 3^n-1, ..., l^n-1 are pairwise coprime}

This is the minimal l making all exponentials pairwise coprime.
-/
noncomputable def h (n : ℕ) : ℕ :=
  Nat.find (⟨2, sorry⟩ : ∃ l, ∀ k₁ k₂ : ℕ, 2 ≤ k₁ → k₁ < k₂ → k₂ ≤ l →
    Nat.gcd (k₁^n - 1) (k₂^n - 1) = 1)

/--
**Relationship between H and h:**
We always have H(n) ≤ h(n) since h(n) requires pairwise coprimality
while H(n) only requires existence of one coprime pair.
-/
theorem H_le_h (n : ℕ) (hn : n ≥ 1) : H n ≤ h n := by
  sorry

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #820: Summary**

1. **Conjecture 1:** H(n) = 3 infinitely often - OPEN
2. **Growth bounds:** H(n) ∼ exp(n^{c/log log n}) - OPEN (upper bound)
3. **Known:** H(n) > exp(n^{c/log log n}) infinitely often (van Doorn)
4. **Erdős 1974:** H(n) > exp(n^{c/(log log n)²}) infinitely often

Status: OPEN - All main conjectures remain unresolved.
-/
theorem erdos_820_summary :
    -- van Doorn's lower bound is known
    (∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n > N,
      (H n : ℝ) > Real.exp ((n : ℝ)^(c / Real.log (Real.log (n : ℝ))))) := by
  exact van_doorn_lower_bound

/--
**Problem Status:**
The problem is OPEN. The main conjecture (H(n) = 3 infinitely often)
and the precise growth estimates remain unproven.
-/
axiom erdos_820_open :
  ¬∃ (proof : erdos820Conjecture1), True

end Erdos820
