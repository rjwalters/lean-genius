/-
# Erdős Problem #279 — Covering with Shifted Prime Progressions

For k ≥ 3, Erdős asked: Can one choose residue classes aₚ (mod p) for
every prime p such that every sufficiently large integer n can be written as
  n = aₚ + t · p
for some prime p and integer t ≥ k?

Even the case k = 3 seems difficult.

A generalization is proposed for sets A ⊆ ℕ with:
  |A ∩ [1,N]| ≫ N/log N and Σ_{n∈A, n≤N} 1/n − log log N → ∞.

For k = 1 or k = 2, the property holds whenever Σ 1/n (over A) diverges.

Reference: https://erdosproblems.com/279
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/- ## Covering by Shifted Progressions -/

/-- A choice of residue classes: for each prime p, a residue aₚ ∈ {0,...,p−1} -/
def ResidueChoice := (p : ℕ) → (hp : Nat.Prime p) → ℕ

/-- An integer n is covered by the choice a with parameter k:
    n = aₚ + t·p for some prime p and t ≥ k -/
def IsCoveredBy (a : ResidueChoice) (k : ℕ) (n : ℕ) : Prop :=
  ∃ (p : ℕ) (hp : Nat.Prime p) (t : ℕ),
    k ≤ t ∧ n = a p hp + t * p

/-- A choice covers all sufficiently large integers -/
def CoversEventually (a : ResidueChoice) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsCoveredBy a k n

/- ## Known Results for Small k -/

/- ## Density Conditions for Generalization -/

/-- A set A ⊆ ℕ has counting function ≫ N/log N: `|A ∩ [1,N]| ≥ c · N / log N`
    for some `c > 0` and all large `N`.

    Left `opaque` rather than given a `True` placeholder body on purpose: a
    trivially-provable body would make `ErdosProblem279_generalized` instantiable
    at junk sets (e.g. `A = ∅`), for which `GeneralizedCovering A k` is provably
    false — instantiating the axiom there would derive `False` (kernel
    inconsistency, issue #41236). Keeping the predicate opaque means it cannot be
    discharged for any set until a genuine density formalization replaces it, so
    the generalized axiom remains an honest, consistent Tier-C scaffold. -/
opaque HasPrimeLikeDensity (A : Set ℕ) : Prop

/-- The log-log condition: `Σ_{n∈A, n≤N} 1/n − log log N → ∞`.

    Also left `opaque` (not a `True` placeholder) for the same soundness reason
    as `HasPrimeLikeDensity` above — see issue #41236. -/
opaque HasLogLogDivergence (A : Set ℕ) : Prop

/- ## The Erdős Problem -/

/-- Erdős Problem 279 (prime case): for every k ≥ 3, there exists a
    choice of residue classes covering all sufficiently large integers -/
axiom ErdosProblem279 (k : ℕ) (hk : 3 ≤ k) :
  ∃ a : ResidueChoice, CoversEventually a k

/-- The case k = 3: follows from the general conjecture -/
theorem ErdosProblem279_k3 :
  ∃ a : ResidueChoice, CoversEventually a 3 :=
  ErdosProblem279 3 (le_refl 3)

/- ## Generalization to Dense Sets -/

/-- The generalized covering property for a set A -/
def GeneralizedCovering (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ (aChoice : (n : ℕ) → n ∈ A → ℕ),
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ (n : ℕ) (hn : n ∈ A) (t : ℕ),
        k ≤ t ∧ m = aChoice n hn + t * n

/-- Generalized conjecture: the covering holds for any set A with
    prime-like density and log-log divergence -/
axiom ErdosProblem279_generalized (A : Set ℕ) (k : ℕ) (hk : 3 ≤ k)
    (hdensity : HasPrimeLikeDensity A)
    (hloglog : HasLogLogDivergence A) :
  GeneralizedCovering A k
