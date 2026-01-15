/-
  Erdős Problem #198: Sidon Sets and Arithmetic Progressions

  Source: https://erdosproblems.com/198
  Status: SOLVED (Answer: NO)

  Question:
  If A ⊆ ℕ is a Sidon set, must the complement Aᶜ contain an infinite
  arithmetic progression?

  Answer: NO

  There exist Sidon sets that intersect every infinite arithmetic progression.
  Multiple constructions are known:

  1. **Lacunary construction** (Baumgartner 1975):
     Enumerate all infinite APs as P₁, P₂, ...
     Choose aₙ ∈ Pₙ with aₙ > 2aₙ₋₁
     The resulting set A = {a₁, a₂, ...} is Sidon (lacunary) and hits every AP.

  2. **Explicit construction** (AlphaProof):
     A = {n! + n : n ≥ 0} = {1, 2, 4, 9, 28, 125, 726, ...}
     This is Sidon and intersects every AP.

  Reference:
  - Baumgartner (1975), "Partitioning vector spaces"
  - Erdős-Graham (1980), "Old and new problems in combinatorial number theory"
-/

import Mathlib

open Set Function
open scoped ENNReal

namespace Erdos198

/-! ## Core Definitions -/

/-- A set A ⊆ ℕ is a **Sidon set** if all pairwise sums a + b (a ≤ b) are distinct. -/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
    a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂

/-- An **arithmetic progression** with first term a and common difference d. -/
def arithmeticProg (a d : ℕ) : Set ℕ := {n | ∃ k : ℕ, n = a + k * d}

/-- A set is an **infinite arithmetic progression** if it equals arithmeticProg a d
    for some a and positive d. -/
def IsInfiniteAP (Y : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ Y = arithmeticProg a d

/-- A set **intersects all infinite APs** if it has nonempty intersection with
    every infinite arithmetic progression. -/
def IntersectsAllAPs (A : Set ℕ) : Prop :=
  ∀ Y : Set ℕ, IsInfiniteAP Y → (A ∩ Y).Nonempty

/-! ## The Main Result -/

/--
**Erdős Problem #198 (SOLVED)**: Must every Sidon set have its complement
contain an infinite AP?

**Answer: NO**

There exist Sidon sets that intersect every infinite AP, leaving no room
for an infinite AP in the complement.
-/
def Erdos198_Question : Prop :=
  ∀ A : Set ℕ, IsSidonSet A → ∃ Y : Set ℕ, IsInfiniteAP Y ∧ Y ⊆ Aᶜ

/-- The answer to Erdős Problem #198 is FALSE. -/
axiom erdos_198_answer : ¬Erdos198_Question

/-! ## The Constructions -/

/-- The factorial construction: A = {n! + n : n ≥ 0}. -/
def factorialSidon : Set ℕ := {m | ∃ n : ℕ, m = n.factorial + n}

/--
**AlphaProof Construction**: The set {n! + n : n ≥ 0} is a Sidon set.

Proof idea: If (a! + a) + (b! + b) = (c! + c) + (d! + d) with a ≤ b, c ≤ d,
then WLOG b ≥ d. If b > d, then b! dominates and the equation fails.
So b = d, and then a! + a = c! + c implies a = c.
-/
axiom factorialSidon_is_sidon : IsSidonSet factorialSidon

/--
**AlphaProof Construction**: The set {n! + n : n ≥ 0} intersects every
infinite arithmetic progression.

Proof: For any AP with first term a and difference d, consider
(a + d + 1)! + (a + d). This is in factorialSidon, and
d divides (a + d + 1)! (since d ≤ a + d + 1), so
(a + d + 1)! + (a + d) ≡ a + d ≡ a (mod d).
Hence (a + d + 1)! + (a + d) is in the AP.
-/
axiom factorialSidon_intersects_all_APs : IntersectsAllAPs factorialSidon

/-- The factorial construction provides a counterexample to Erdős's question. -/
theorem factorial_counterexample :
    IsSidonSet factorialSidon ∧ IntersectsAllAPs factorialSidon :=
  ⟨factorialSidon_is_sidon, factorialSidon_intersects_all_APs⟩

/-! ## Lacunary Sets -/

/-- A set is **lacunary** if aₙ₊₁ > 2aₙ for consecutive elements. -/
def IsLacunary (A : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, StrictMono f ∧ A = range f ∧ ∀ n, f (n + 1) > 2 * f n

/-- Lacunary sets are Sidon sets.

Proof: If a + b = c + d with a < b and c < d from a lacunary sequence,
then b > 2a and d > 2c. WLOG b ≥ d. If b > d, then b > a + d > a + c,
so b > a + c + d - b, giving 2b > a + c + d = a + b, so b > a.
This leads to a contradiction. Hence b = d and a = c. -/
axiom lacunary_is_sidon {A : Set ℕ} (hA : IsLacunary A) : IsSidonSet A

/--
**Baumgartner's Construction**: There exists a lacunary Sidon set that
intersects every infinite AP.

Construction: Enumerate all infinite APs as P₁, P₂, ...
Choose a₁ = min(P₁ ∩ ℕ).
Choose aₙ = some element of Pₙ ∩ ℕ with aₙ > 2aₙ₋₁.
(This is always possible since Pₙ is infinite.)
-/
axiom baumgartner_construction :
    ∃ A : Set ℕ, IsLacunary A ∧ IntersectsAllAPs A

/-! ## First Few Elements -/

/-- The first elements of the factorial Sidon set: {1, 2, 4, 9, 28, 125, 726, ...}

    n! + n for n = 0, 1, 2, 3, 4, 5, 6, ...
    = 1, 2, 4, 9, 28, 125, 726, ...
-/
theorem first_elements_in_factorialSidon :
    1 ∈ factorialSidon ∧ 2 ∈ factorialSidon ∧ 4 ∈ factorialSidon ∧
    9 ∈ factorialSidon ∧ 28 ∈ factorialSidon :=
  ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩⟩

/-- Verification: 0! + 0 = 1. -/
example : (0 : ℕ).factorial + 0 = 1 := rfl

/-- Verification: 1! + 1 = 2. -/
example : (1 : ℕ).factorial + 1 = 2 := rfl

/-- Verification: 2! + 2 = 4. -/
example : (2 : ℕ).factorial + 2 = 4 := rfl

/-- Verification: 3! + 3 = 9. -/
example : (3 : ℕ).factorial + 3 = 9 := rfl

/-- Verification: 4! + 4 = 28. -/
example : (4 : ℕ).factorial + 4 = 28 := rfl

end Erdos198
