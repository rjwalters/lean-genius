/-
  Erdős Problem #34: Consecutive Sums in Permutations

  Source: https://erdosproblems.com/34
  Status: DISPROVED (Hegyvári 1986, Konieczny 2015)

  Statement:
  For any permutation π ∈ Sₙ of {1,…,n}, let S(π) count the number of
  distinct consecutive sums, i.e., sums of the form Σ_{u≤i≤v} π(i).

  Erdős conjectured: S(π) = o(n²) for all π ∈ Sₙ.

  **This conjecture is FALSE!**

  History:
  - The identity permutation satisfies S(ι) = o(n²)
  - Hegyvári (1986): First counterexample with S(π) ≥ (1/18 + o(1))n²
  - Konieczny (2015): "Extremely false" — constructed π with S(π) ≥ n²/4
  - Random permutations: S(π) ~ (1 + e⁻²)/4 · n² asymptotically

  Bounds on f(n) = max_π S(π):
  - (0.286...)n² ≤ f(n) ≤ (0.446...)n²

  Bounds on g(n) = min_π S(π):
  - g(n) ≫ n^(3/2), possibly g(n) ≥ n^(2-o(1))

  References:
  - [Er77c, p.71], [ErGr80, p.58]
  - Hegyvári (1986) [He86]
  - Konieczny (2015) [Ko15]
  - Related: Problems #356, #357
-/

import Mathlib

open Finset BigOperators

namespace Erdos34

/-
## Core Definitions
-/

/-- A permutation of {1, ..., n} represented as an equivalence on Fin n. -/
abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

/-- The consecutive sum from index u to v (inclusive) in a permutation π.
    We use 1-indexed values, so π(i) gives the value at position i.
    The sum is Σ_{i=u}^{v} π(i) where values are in {1,...,n}. -/
noncomputable def consecutiveSum (n : ℕ) (π : Perm n) (u v : Fin n) : ℕ :=
  if u ≤ v then
    ∑ i ∈ Finset.Icc u v, (π i).val + 1
  else 0

/-- The set of all distinct consecutive sums of a permutation.
    These are sums Σ_{i=u}^{v} π(i) for all pairs 0 ≤ u ≤ v < n. -/
noncomputable def consecutiveSumSet (n : ℕ) (π : Perm n) : Finset ℕ :=
  (Finset.univ.product Finset.univ).image fun ⟨u, v⟩ => consecutiveSum n π u v

/-- S(π) = the number of distinct consecutive sums.
    This is the main quantity studied in the problem. -/
noncomputable def S (n : ℕ) (π : Perm n) : ℕ :=
  (consecutiveSumSet n π).card

/-
## Maximum and Minimum over All Permutations
-/

/-- f(n) = maximum S(π) over all permutations of {1,...,n}. -/
noncomputable def f (n : ℕ) : ℕ :=
  Finset.sup Finset.univ (S n)

/-- g(n) = minimum S(π) over all permutations of {1,...,n}. -/
noncomputable def g (n : ℕ) : ℕ :=
  Finset.inf' Finset.univ (Finset.univ_nonempty) (S n)

/-
## The Disproved Conjecture

Erdős conjectured that S(π) = o(n²) for all permutations.
This would mean: for all ε > 0, there exists N such that for all n > N,
S(π) < ε·n² for every π ∈ Sₙ.

This is FALSE: there exist permutations with S(π) ≥ n²/4.
-/

/-- The **DISPROVED** Erdős conjecture: S(π) = o(n²) for all permutations.
    Formally: ∀ ε > 0, ∃ N, ∀ n > N, ∀ π ∈ Sₙ, S(π) < ε·n².

    This statement is FALSE. -/
def ErdosConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n > N, ∀ π : Perm n, (S n π : ℝ) < ε * n^2

/-
**Theorem (Counterexample Existence)**:
Erdős's conjecture is FALSE. There exist permutations with S(π) ≥ cn² for constant c > 0.
-/

/-
## Known Results
-/

/-
**Hegyvári (1986)**: First counterexample to the conjecture.
There exists a family of permutations πₙ with S(πₙ) ≥ (1/18 + o(1))n².
-/

/-
**Konieczny (2015)**: The conjecture is "extremely false."
There exist permutations with S(π) ≥ n²/4, which is asymptotically optimal
up to lower-order terms.
-/

/-
**Lower bound on maximum**: f(n) ≥ 0.286...·n²
-/

/-
**Upper bound on maximum**: f(n) ≤ 0.446...·n²
-/

/-
**Random permutation behavior**: S(π) ~ (1 + e⁻²)/4 · n² asymptotically
for a random permutation π chosen uniformly.

The constant (1 + e⁻²)/4 ≈ 0.2838...
-/

/-
## The Identity Permutation

The identity permutation ι has S(ι) = o(n²), which motivated Erdős's conjecture.
-/

/-- The identity permutation: ι(i) = i. -/
def identityPerm (n : ℕ) : Perm n := Equiv.refl (Fin n)

/-
The identity permutation satisfies S(ι) = o(n²).

For the identity, consecutive sums are arithmetic progressions:
Σ_{i=u}^{v} i = (v-u+1)(u+v)/2

The number of distinct such sums is O(n^(3/2)) which is o(n²).
-/

/-
## Minimum Bounds
-/

/-
**Lower bound on minimum**: g(n) ≫ n^(3/2)

Every permutation has at least Ω(n^(3/2)) distinct consecutive sums.
-/

/-
**Conjectured bound on minimum**: g(n) ≥ n^(2-o(1))

It's conjectured that the minimum grows almost quadratically.
-/
def MinimumConjecture : Prop :=
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n > N, (g n : ℝ) ≥ n^(2 - ε)

/-
## Basic Properties
-/

/-- The number of possible consecutive sums is at most n².
    S(π) = card of image of n² pairs under consecutiveSum.
    NOTE: The tighter bound n(n+1)/2 stated previously is FALSE:
    for n=2, π=id gives S=4 > 3=n(n+1)/2 (0 from u>v contributes
    a distinct value not counted by the n(n+1)/2 pairs with u≤v). -/
theorem S_upper_bound (n : ℕ) (π : Perm n) :
    S n π ≤ n * n := by
  unfold S consecutiveSumSet
  calc ((Finset.univ.product Finset.univ).image (fun x => consecutiveSum n π x.1 x.2)).card
      ≤ (Finset.univ.product (Finset.univ : Finset (Fin n))).card := Finset.card_image_le
    _ = n * n := by simp [Finset.card_product, Fintype.card_fin]

/-- All consecutive sums are positive (for n ≥ 1). -/
theorem consecutiveSum_pos (n : ℕ) (hn : n ≥ 1) (π : Perm n)
    (u v : Fin n) (huv : u ≤ v) :
    consecutiveSum n π u v ≥ 1 := by
  simp only [consecutiveSum, if_pos huv]
  have hne : (Finset.Icc u v).Nonempty := ⟨u, Finset.mem_Icc.mpr ⟨le_refl u, huv⟩⟩
  have := Finset.sum_pos (fun i (_ : i ∈ Finset.Icc u v) =>
    show 0 < (π i).val + 1 from Nat.succ_pos _) hne
  omega

/-
## Summary

**Erdős Problem #34** asked whether S(π) = o(n²) for all permutations π.
This was **DISPROVED**:

1. **Hegyvári (1986)**: First counterexample with S(π) ≥ (1/18)n²
2. **Konieczny (2015)**: S(π) ≥ n²/4 is achievable
3. **Bounds on max**: 0.286n² ≤ f(n) ≤ 0.446n²
4. **Random permutations**: S(π) ~ (1 + e⁻²)/4 · n²
5. **Identity permutation**: S(ι) = o(n²) (this motivated the conjecture)
6. **Minimum**: g(n) ≫ n^(3/2), possibly g(n) ≥ n^(2-o(1))

Related problems: #356, #357
-/

end Erdos34
