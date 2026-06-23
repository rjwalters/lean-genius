/-
Erdős Problem #785: Exact Additive Complements

Source: https://erdosproblems.com/785
Status: SOLVED (Sárközy-Szemerédi 1994)

Statement:
Let A, B ⊆ ℕ be infinite sets such that A + B contains all large integers.
Let A(x) = |A ∩ [1,x]| and B(x) = |B ∩ [1,x]|.

If A(x)B(x) ~ x, is it true that A(x)B(x) - x → ∞ as x → ∞?

Background:
Sets A and B with A + B ⊇ {n : n ≥ N₀} and A(x)B(x) ~ x are called
"exact additive complements" - they are as sparse as possible while
still covering all large integers.

Key Results:
- Danzer (1964): Exact additive complements exist
- Sárközy-Szemerédi (1994): YES, A(x)B(x) - x → ∞
- Ruzsa (2017): For any w(x) → ∞, ∃ A,B with A(x)B(x) - x < w(x) infinitely often

Tags: additive-combinatorics, sumsets, complement-sets
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

open Nat Set Finset

namespace Erdos785

/-
## Part I: Sumsets and Additive Complements
-/

/--
**Sumset:**
A + B = {a + b : a ∈ A, b ∈ B}
-/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
**Counting Function:**
A(x) = |A ∩ [1, x]|
-/
noncomputable def countingFunction (A : Set ℕ) (x : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 x).ncard

/--
**Alternative with Finset:**
A(x) for finite computation.
-/
def countingFunctionFinite (A : Finset ℕ) (x : ℕ) : ℕ :=
  (A.filter (fun n => 1 ≤ n ∧ n ≤ x)).card

/--
**Covers All Large Integers:**
A + B ⊇ {n : n ≥ N₀} for some N₀.
-/
def CoversLargeIntegers (A B : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A B

/--
**Additive Complement Pair:**
A and B are additive complements if their sumset covers all large integers.
-/
def IsAdditiveComplement (A B : Set ℕ) : Prop :=
  CoversLargeIntegers A B ∧ A.Infinite ∧ B.Infinite

/-
## Part II: Exact Additive Complements
-/

/--
**Product Asymptotic to x:**
A(x)B(x) ~ x means A(x)B(x)/x → 1.
-/
def ProductAsymptoticToX (A B : Set ℕ) : Prop :=
  Filter.Tendsto (fun x => (countingFunction A x * countingFunction B x : ℝ) / x)
    Filter.atTop (nhds 1)

/--
**Exact Additive Complement:**
A, B with A + B covering all large integers and A(x)B(x) ~ x.
These are "optimally sparse" complement pairs.
-/
def IsExactAdditiveComplement (A B : Set ℕ) : Prop :=
  IsAdditiveComplement A B ∧ ProductAsymptoticToX A B

/-
## Part III: The Main Question
-/

/--
**The Erdős-Danzer Question:**
For exact additive complements, does A(x)B(x) - x → ∞?
-/
def ErdosDanzerQuestion : Prop :=
  ∀ A B : Set ℕ, IsExactAdditiveComplement A B →
    Filter.Tendsto (fun x => (countingFunction A x * countingFunction B x : ℤ) - x)
      Filter.atTop Filter.atTop

/-
## Part IV: Danzer's Existence Result
-/

/--
**Danzer (1964): Exact Additive Complements Exist**
This was initially surprising - one might expect A(x)B(x) ~ x
to be impossible while covering all large integers.
-/
axiom danzer_1964_existence :
    ∃ A B : Set ℕ, IsExactAdditiveComplement A B

/-
## Part V: Sárközy-Szemerédi Solution
-/

/--
**Sárközy-Szemerédi (1994): Affirmative Answer**
If A, B are exact additive complements, then A(x)B(x) - x → ∞.
-/
axiom sarkozy_szemeredi_1994 :
    ∀ A B : Set ℕ, IsExactAdditiveComplement A B →
      Filter.Tendsto (fun x => (countingFunction A x * countingFunction B x : ℤ) - x)
        Filter.atTop Filter.atTop

/--
**The Main Theorem:**
The Erdős-Danzer question has an affirmative answer.
-/
theorem erdos_danzer_solved : ErdosDanzerQuestion :=
  sarkozy_szemeredi_1994

/-
## Part VI: Ruzsa's Refinement
-/

/--
**Ruzsa (2017): Tight Characterization**
For ANY function w : ℕ → ℝ with w(x) → ∞,
there exist exact additive complements A, B such that
A(x)B(x) - x < w(x) for infinitely many x.
-/
/-
## Part VII: Related Concepts
-/

/--
**Representation Function:**
r(n) = |{(a,b) : a ∈ A, b ∈ B, a+b = n}|.
-/
noncomputable def representationFunction (A B : Set ℕ) (n : ℕ) : ℕ :=
  {(a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ B ∧ a + b = n}.ncard

/--
**Average Representation:**
For exact complements, average r(n) for n ≤ x is close to 1.
-/
/-
## Part IX: Summary
-/

/--
**Erdős Problem #785: SOLVED**

**QUESTION:** For exact additive complements, does A(x)B(x) - x → ∞?

**ANSWER:** YES (Sárközy-Szemerédi 1994)

**REFINEMENT:** The growth to ∞ can be arbitrarily slow (Ruzsa 2017)

**KEY RESULTS:**
1. Danzer (1964): Exact additive complements exist
2. Sárközy-Szemerédi (1994): A(x)B(x) - x → ∞
3. Ruzsa (2017): Growth rate can be any w(x) → ∞

**SIGNIFICANCE:** Understanding the minimal density needed for
additive bases and complement pairs.
-/
theorem erdos_785_summary :
    -- Exact additive complements exist
    (∃ A B : Set ℕ, IsExactAdditiveComplement A B) ∧
    -- The main question is YES
    ErdosDanzerQuestion :=
  ⟨danzer_1964_existence, erdos_danzer_solved⟩

/--
**Erdős Problem #785: SOLVED**
The answer is YES by Sárközy-Szemerédi (1994).
-/
theorem erdos_785 : ErdosDanzerQuestion :=
  erdos_danzer_solved

end Erdos785
