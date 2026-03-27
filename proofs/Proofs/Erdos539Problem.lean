/-
  Erdős Problem #539: GCD-Reduced Quotients

  Source: https://erdosproblems.com/539
  Status: OPEN (bounds established, exact behavior unknown)

  Statement:
  Let h(n) be such that for any set A ⊆ ℕ of size n, the set
    { a / gcd(a,b) : a, b ∈ A }
  has size at least h(n). Estimate h(n).

  Known Results:
  - Erdős-Szemerédi: n^{1/2} ≪ h(n) ≪ n^{1-c} for some c > 0
  - Freiman-Lev: h(n) ≪ n^{2/3} (improved upper bound)

  The problem connects GCD structure with additive combinatorics.

  References:
  - [Er73] Erdős, "Problems and results on combinatorial number theory" (1973)
  - [GrRo99] Granville-Roesler, geometric reformulation
  - Freiman-Lev upper bound improvement
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators Nat

namespace Erdos539

/-
## Part I: The GCD-Reduced Quotient Set
-/

/-- The GCD-reduced quotient a / gcd(a, b). -/
def gcdQuotient (a b : ℕ) : ℕ := a / Nat.gcd a b

/-- Basic property: gcdQuotient a b is always well-defined. -/
theorem gcdQuotient_pos (a b : ℕ) (ha : a > 0) (hb : b > 0) :
    gcdQuotient a b > 0 := by
  unfold gcdQuotient
  have hgcd : Nat.gcd a b > 0 := Nat.gcd_pos_of_pos_left b ha
  have hdiv : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  exact Nat.div_pos (Nat.le_of_dvd ha hdiv) hgcd

/-- gcd(a,b) divides a, so a / gcd(a,b) is an integer. -/
theorem gcdQuotient_is_nat (a b : ℕ) :
    gcdQuotient a b * Nat.gcd a b = a := by
  unfold gcdQuotient
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left a b)

/-- The GCD-reduced quotient set of A. -/
def gcdQuotientSet (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun ab => gcdQuotient ab.1 ab.2)

/-- The size of the GCD-reduced quotient set. -/
def gcdQuotientSize (A : Finset ℕ) : ℕ :=
  (gcdQuotientSet A).card

/-
## Part II: The Function h(n)
-/

/-- h(n) = minimum size of gcdQuotientSet over all n-element sets A ⊆ ℕ. -/
noncomputable def h (n : ℕ) : ℕ :=
  if n = 0 then 0
  else ⨅ (A : Finset ℕ) (_ : A.card = n) (_ : ∀ a ∈ A, a > 0),
       gcdQuotientSize A

/-- The quotient set always contains some elements. -/
theorem quotient_set_nonempty (A : Finset ℕ) (hne : A.Nonempty) (hpos : ∀ a ∈ A, a > 0) :
    (gcdQuotientSet A).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  use gcdQuotient a a
  unfold gcdQuotientSet
  simp only [mem_image, mem_product]
  exact ⟨(a, a), ⟨ha, ha⟩, rfl⟩

/-- gcdQuotient a a = 1 for a > 0. -/
theorem gcdQuotient_self (a : ℕ) (ha : a > 0) : gcdQuotient a a = 1 := by
  unfold gcdQuotient
  simp [Nat.gcd_self, Nat.div_self ha]

/-- 1 is always in the quotient set (if A is nonempty with positive elements). -/
theorem one_in_quotient_set (A : Finset ℕ) (hne : A.Nonempty) (hpos : ∀ a ∈ A, a > 0) :
    1 ∈ gcdQuotientSet A := by
  obtain ⟨a, ha⟩ := hne
  unfold gcdQuotientSet
  simp only [mem_image, mem_product]
  exact ⟨(a, a), ⟨ha, ha⟩, gcdQuotient_self a (hpos a ha)⟩

/-
## Part III: Erdős-Szemerédi Bounds
-/

/-- Combined Erdős-Szemerédi result: n^{1/2} ≪ h(n) ≪ n^{1-c}. -/
def ErdosSzemeredi_Bounds : Prop :=
  (∃ c₁ > 0, ∀ n ≥ 2, (h n : ℝ) ≥ c₁ * n^(1/2 : ℝ)) ∧
  (∃ c₂ > 0, c₂ < 1 ∧ ∀ n ≥ 2, (h n : ℝ) ≤ n^(1 - c₂))

/-
## Part IV: Freiman-Lev Improvement
-/

/-- The improved bounds: n^{1/2} ≪ h(n) ≪ n^{2/3}. -/
def ImprovedBounds : Prop :=
  (∃ c > 0, ∀ n ≥ 2, (h n : ℝ) ≥ c * n^(1/2 : ℝ)) ∧
  (∃ C > 0, ∀ n ≥ 2, (h n : ℝ) ≤ C * n^(2/3 : ℝ))

/-
## Part V: Examples
-/

/-- For A = {a, 2a, ..., na}, the quotient set is smaller. -/
def arithmeticProgression (a n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => a * (i + 1))

/-- Geometric progressions {a^0, a^1, ..., a^{n-1}} give smaller quotient sets. -/
def geometricProgression (a n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => a^i)

/-
## Part VI: Connection to GCD Structure
-/

/-- The GCD matrix of a set A. -/
def gcdMatrix (A : Finset ℕ) : ℕ → ℕ → ℕ :=
  fun i j => if hi : i ∈ A then if hj : j ∈ A then Nat.gcd i j else 0 else 0

/-- The quotient matrix. -/
def quotientMatrix (A : Finset ℕ) : ℕ → ℕ → ℕ :=
  fun i j => if hi : i ∈ A then if hj : j ∈ A then gcdQuotient i j else 0 else 0

/-
## Part VII: Geometric Reformulation (Granville-Roesler)
-/

/-
## Part VIII: Special Sets with Small Quotient Sets
-/

/-- Sets with small quotient sets exist. -/
def extremalSets : Prop :=
  ∀ n : ℕ, n ≥ 2 →
    ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a > 0) ∧
      (gcdQuotientSize A : ℝ) ≤ (n : ℝ)^(2/3 : ℝ)

/-
## Part IX: The Erdős Question
-/

/-- **The main open question:** Does h(n) = Θ(n^α) for some specific
    exponent α? The current bounds give 1/2 ≤ α ≤ 2/3. -/
def ErdosQuestion539 : Prop :=
  ∃ α : ℝ, (1 : ℝ)/2 ≤ α ∧ α ≤ 2/3 ∧
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        c₁ * (n : ℝ)^α ≤ (h n : ℝ) ∧ (h n : ℝ) ≤ c₂ * (n : ℝ)^α

/-- **Refined question:** Is the true exponent α closer to 1/2 or 2/3?
    Evidence from extremal constructions suggests α may be 2/3. -/
def openExponentQuestion : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (h n : ℝ) ≥ c * (n : ℝ)^(2/3 - ε)

/-
## Part X: Summary
-/

/-- **Erdős Problem #539: OPEN (bounds established)**

Question: For A ⊆ ℕ of size n, what is the minimum size of
{ a / gcd(a,b) : a, b ∈ A }?

Known Bounds:
- Lower: n^{1/2} (Erdős-Szemerédi)
- Upper: n^{2/3} (Freiman-Lev, improving n^{1-c})

The exact behavior remains open.
-/

end Erdos539
