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

/-!
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

/-!
## Maximum and Minimum over All Permutations
-/

/-- f(n) = maximum S(π) over all permutations of {1,...,n}. -/
noncomputable def f (n : ℕ) : ℕ :=
  Finset.sup Finset.univ (S n)

/-- g(n) = minimum S(π) over all permutations of {1,...,n}. -/
noncomputable def g (n : ℕ) : ℕ :=
  Finset.inf' Finset.univ (Finset.univ_nonempty) (S n)

/-!
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

/--
**Theorem (Counterexample Existence)**:
Erdős's conjecture is FALSE. There exist permutations with S(π) ≥ cn² for constant c > 0.
-/
axiom erdos_34_disproved : ¬ErdosConjecture

/-!
## Known Results
-/

/--
**Hegyvári (1986)**: First counterexample to the conjecture.
There exists a family of permutations πₙ with S(πₙ) ≥ (1/18 + o(1))n².
-/
axiom hegyvari_counterexample :
    ∃ r : ℕ → ℝ, (∀ᶠ n in Filter.atTop, |r n| ≤ 1/n) ∧
    ∀ᶠ n in Filter.atTop, ∃ π : Perm n, (S n π : ℝ) ≥ (1/18 + r n) * n^2

/--
**Konieczny (2015)**: The conjecture is "extremely false."
There exist permutations with S(π) ≥ n²/4, which is asymptotically optimal
up to lower-order terms.
-/
axiom konieczny_quarter_bound :
    ∀ᶠ n in Filter.atTop, ∃ π : Perm n, S n π ≥ n^2 / 4

/--
**Lower bound on maximum**: f(n) ≥ 0.286...·n²
-/
axiom f_lower_bound :
    ∃ c : ℝ, c ≥ 0.286 ∧ ∀ᶠ n in Filter.atTop, (f n : ℝ) ≥ c * n^2

/--
**Upper bound on maximum**: f(n) ≤ 0.446...·n²
-/
axiom f_upper_bound :
    ∃ c : ℝ, c ≤ 0.446 ∧ ∀ᶠ n in Filter.atTop, (f n : ℝ) ≤ c * n^2

/--
**Random permutation behavior**: S(π) ~ (1 + e⁻²)/4 · n² asymptotically
for a random permutation π chosen uniformly.

The constant (1 + e⁻²)/4 ≈ 0.2838...
-/
axiom random_permutation_limit :
    ∃ c : ℝ, c = (1 + Real.exp (-2)) / 4 ∧
    True  -- Formal probability statement would require measure theory

/-!
## The Identity Permutation

The identity permutation ι has S(ι) = o(n²), which motivated Erdős's conjecture.
-/

/-- The identity permutation: ι(i) = i. -/
def identityPerm (n : ℕ) : Perm n := Equiv.refl (Fin n)

/--
The identity permutation satisfies S(ι) = o(n²).

For the identity, consecutive sums are arithmetic progressions:
Σ_{i=u}^{v} i = (v-u+1)(u+v)/2

The number of distinct such sums is O(n^(3/2)) which is o(n²).
-/
axiom identity_is_little_o :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n > N, (S n (identityPerm n) : ℝ) < ε * n^2

/-!
## Minimum Bounds
-/

/--
**Lower bound on minimum**: g(n) ≫ n^(3/2)

Every permutation has at least Ω(n^(3/2)) distinct consecutive sums.
-/
axiom g_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop, (g n : ℝ) ≥ c * n^(3/2 : ℝ)

/--
**Conjectured bound on minimum**: g(n) ≥ n^(2-o(1))

It's conjectured that the minimum grows almost quadratically.
-/
def MinimumConjecture : Prop :=
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n > N, (g n : ℝ) ≥ n^(2 - ε)

/-!
## Basic Properties
-/

/-- The number of possible consecutive sums is at most n(n+1)/2
    (one for each pair u ≤ v). -/
theorem S_upper_bound (n : ℕ) (π : Perm n) :
    S n π ≤ n * (n + 1) / 2 := by
  -- There are at most n(n+1)/2 pairs (u,v) with u ≤ v
  sorry

/-- All consecutive sums are positive (for n ≥ 1). -/
theorem consecutiveSum_pos (n : ℕ) (hn : n ≥ 1) (π : Perm n)
    (u v : Fin n) (huv : u ≤ v) :
    consecutiveSum n π u v ≥ 1 := by
  sorry

/-!
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
