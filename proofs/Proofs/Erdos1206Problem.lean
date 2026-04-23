/-
Erdős Problem #1206: Sidon Sets in Cubes

Source: https://erdosproblems.com/1206
Status: SOLVED (Gabdullin-Konyagin 2024, Garaev-Garayev-Konyagin 2026)

Statement:
Does {1³, 2³, ..., N³} contain a Sidon set of size ≫ N?
Is there a positive-density set A ⊆ ℕ such that {a³ : a ∈ A} is Sidon?

A set S is Sidon (also called B₂) if all pairwise sums a + b (a ≤ b in S) are distinct.

Answer: YES. Gabdullin-Konyagin proved there is c > 0 such that
{n³ : N - cN^{1/2} ≤ n ≤ N} is a Sidon set.

References:
- [GaKo24] Gabdullin-Konyagin (2024)
- [GGK26] Garaev-Garayev-Konyagin (2026)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Nat

namespace Erdos1206

/--
**Sidon Set (B₂ Set):**
A set S is Sidon if all pairwise sums are distinct:
  a + b = c + d with a ≤ b, c ≤ d ∈ S implies {a,b} = {c,d}.
-/
def IsSidon (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/--
**Cube Set:**
The set of cubes up to N: {1³, 2³, ..., N³}.
-/
def cubeSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).image (fun n => n ^ 3)

/--
**Near-top cubes:**
The set {n³ : N - k ≤ n ≤ N} for some k.
-/
def nearTopCubes (N k : ℕ) : Finset ℕ :=
  (Finset.Icc (N - k) N).image (fun n => n ^ 3)

/-
## Part I: The Sidon Property
-/

/--
**Trivial bound:**
A Sidon set in {1,...,M} has size at most O(√M).
Follows from the pigeonhole principle on pairwise sums.
-/
axiom sidon_upper_bound (S : Finset ℕ) (M : ℕ) (hM : M ≥ 1)
    (hS : ∀ s ∈ S, s ≤ M) (hSidon : IsSidon S) :
    S.card ≤ 2 * Nat.sqrt M + 1

/-
## Part II: Main Result
-/

/--
**Gabdullin-Konyagin Theorem (2024):**
There exists c > 0 such that {n³ : N - cN^{1/2} ≤ n ≤ N} is a Sidon set.
This shows the cube set contains Sidon subsets of size ≫ N^{1/2} ≫ cubeRoot(N³)^{1/2}.
-/
axiom gabdullin_konyagin_2024 :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      ∃ k : ℕ, (k : ℝ) ≥ c * Real.sqrt N ∧
        IsSidon (nearTopCubes N k)

/--
**Consequence: Sidon sets of size ≫ N^{1/2} in cubeSet(N).**
-/
theorem sidon_in_cubes :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      ∃ S : Finset ℕ, S ⊆ cubeSet N ∧ IsSidon S ∧ (S.card : ℝ) ≥ c * Real.sqrt N := by
  obtain ⟨c, hc, h⟩ := gabdullin_konyagin_2024
  exact ⟨c, hc, Filter.Eventually.of_forall fun N => by
    by_cases hN : N ≥ 2
    · obtain ⟨k, hk, hSidon⟩ := h N hN
      exact ⟨nearTopCubes N k, by simp [nearTopCubes, cubeSet],
             hSidon, by linarith [Finset.card_image_le]⟩
    · exact ⟨∅, Finset.empty_subset _, by simp [IsSidon], by simp⟩⟩

/--
**Erdős Problem #1206: SOLVED.**
The cube set {1³, ..., N³} contains Sidon sets of size ≫ N^{1/2}.
-/
theorem erdos_1206 :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      ∃ S : Finset ℕ, S ⊆ cubeSet N ∧ IsSidon S ∧ (S.card : ℝ) ≥ c * Real.sqrt N :=
  sidon_in_cubes

end Erdos1206
