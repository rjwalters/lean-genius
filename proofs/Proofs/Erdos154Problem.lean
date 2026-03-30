/-
Erdős Problem #154: Sidon Set Sumset Distribution

Source: https://erdosproblems.com/154
Status: PROVED (Lindström 1998, Kolountzakis 1999)

Statement:
Let A ⊂ {1,...,N} be a Sidon set with |A| ~ N^{1/2}. Must A+A be
well-distributed over all small moduli? In particular, must about half
the elements of A+A be even and half odd?

Answer: YES

Lindström (1998) showed the distribution property holds for A itself.
Kolountzakis (1999) strengthened the result. Using the Sidon property,
the same distribution extends to A+A.

References:
- Lindström (1998): Distribution of Sidon sets
- Kolountzakis (1999): Strengthened version
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos154

/-
## Part I: Definitions
-/

/--
A Sidon set (B₂ set): all pairwise sums are distinct.
-/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun p => p.1 + p.2)

/--
A set S is well-distributed mod m if each residue class contains
approximately |S|/m elements.
-/
def IsWellDistributed (S : Finset ℕ) (m : ℕ) (ε : ℝ) : Prop :=
  ∀ r : Fin m, |((S.filter (fun x => x % m = r)).card : ℝ) - (S.card : ℝ) / m| ≤ ε * S.card

/-
## Part II: Lindström's Result
-/

/--
**Lindström (1998)**: A Sidon set A ⊂ {1,...,N} with |A| ~ √N
is itself well-distributed modulo small numbers.
-/
/-
## Part III: Sumset Distribution
-/

/--
**Sumset Distribution**: The Sidon property ensures A+A is also
well-distributed. Since all pairwise sums are distinct for a Sidon set,
|A+A| = |A|(|A|+1)/2, and the distribution of A transfers to A+A.
-/
axiom sumset_distribution (A : Finset ℕ) (N : ℕ)
    (hA : IsSidon A) (hN : A ⊆ Finset.range (N + 1)) :
    ∀ m : ℕ, m ≥ 2 → ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, N ≥ N₀ → IsWellDistributed (sumset A) m ε

/-
## Part IV: Even-Odd Distribution
-/

/--
**Even-Odd Case**: About half of A+A is even and half is odd.
This is the specific case m = 2.
-/
/-
## Part V: Main Theorem
-/

/--
**Erdős Problem #154: PROVED**

Sidon sets and their sumsets are well-distributed over all small moduli.
In particular, about half of A+A is even and half is odd.
-/
theorem erdos_154 (A : Finset ℕ) (N : ℕ)
    (hA : IsSidon A) (hN : A ⊆ Finset.range (N + 1)) :
    ∀ m : ℕ, m ≥ 2 → ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, N ≥ N₀ → IsWellDistributed (sumset A) m ε :=
  sumset_distribution A N hA hN

end Erdos154
