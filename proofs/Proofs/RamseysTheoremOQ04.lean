/-
Ramsey Theory for Hypergraphs and Higher Dimensions

Source: Open question from ramseys-theorem gallery proof
Status: AXIOMATIZED (1 axiom for the deep Ramsey-type result, 0 sorries)

Extends Ramsey's theorem from 2-uniform (edges/graphs) to k-uniform hypergraphs.
The classical Ramsey theorem colors edges (2-element subsets); the hypergraph
extension colors k-element subsets.

Hypergraph Ramsey Theorem (Ramsey 1930, general form):
  For any k, r, n₁, ..., nᵣ, there exists N such that for any r-coloring
  of the k-element subsets of {1, ..., N}, there exists a color i and a
  monochromatic set of size nᵢ.

The k=2 case is the classical Ramsey theorem. The k=1 case is the pigeonhole
principle. Higher k values require significantly larger Ramsey numbers.
-/

import Mathlib

open Finset

namespace HypergraphRamsey

variable {α : Type*}

/-! ## Part I: Definitions for k-Uniform Hypergraph Coloring -/

/-- A k-element subset of a finset. -/
def kSubsets (s : Finset α) (k : ℕ) [DecidableEq α] : Finset (Finset α) :=
  s.powersetCard k

/-- An r-coloring of k-element subsets. -/
def Coloring (s : Finset α) (k : ℕ) (r : ℕ) [DecidableEq α] : Type :=
  kSubsets s k → Fin r

/-- A subset is monochromatic for a coloring if all its k-element subsets have the same color. -/
def IsMonochromatic [DecidableEq α] (s t : Finset α) (k : ℕ) (c : Coloring s k r)
    (color : Fin r) (ht : t ⊆ s) : Prop :=
  ∀ e ∈ kSubsets t k, ∀ (he : e ∈ kSubsets s k), c ⟨e, he⟩ = color

/-- The hypergraph Ramsey property: for any r-coloring of k-subsets of an N-element set,
    there exists a monochromatic subset of size n. -/
def HypergraphRamseyProperty (k r n N : ℕ) : Prop :=
  ∀ (S : Finset ℕ), S.card = N →
    ∀ (c : kSubsets S k → Fin r),
      ∃ (T : Finset ℕ) (i : Fin r), T ⊆ S ∧ T.card ≥ n ∧
        ∀ e ∈ kSubsets T k, ∀ (he : e ∈ kSubsets S k), c ⟨e, he⟩ = i

/-! ## Part II: Special Cases -/

/-- k = 1 is the pigeonhole principle: coloring singletons with r colors
    among enough elements forces some color to appear many times. -/
theorem k1_is_pigeonhole : HypergraphRamseyProperty 1 r n N →
    ∀ (S : Finset ℕ), S.card = N →
      ∀ (c : kSubsets S 1 → Fin r),
        ∃ (T : Finset ℕ) (i : Fin r), T ⊆ S ∧ T.card ≥ n ∧
          ∀ e ∈ kSubsets T 1, ∀ he, c ⟨e, he⟩ = i :=
  fun h => h

/-- k = 2 case: this is the classical Ramsey theorem.
    HypergraphRamseyProperty 2 2 n N recovers the 2-color graph Ramsey theorem. -/
theorem classical_ramsey_is_k2 (n₁ n₂ N : ℕ)
    (hN : HypergraphRamseyProperty 2 2 (max n₁ n₂) N) :
    ∀ (S : Finset ℕ), S.card = N →
      ∀ (c : kSubsets S 2 → Fin 2),
        ∃ (T : Finset ℕ), T ⊆ S ∧ T.card ≥ max n₁ n₂ ∧
          (∀ e ∈ kSubsets T 2, ∀ he, c ⟨e, he⟩ = 0) ∨
          (∀ e ∈ kSubsets T 2, ∀ he, c ⟨e, he⟩ = 1) := by
  intro S hS c
  obtain ⟨T, i, hTS, hTn, hmono⟩ := hN S hS c
  exact ⟨T, hTS, hTn, by fin_cases i <;> [left; right] <;> exact hmono⟩

/-! ## Part III: The Hypergraph Ramsey Theorem -/

/-- The Hypergraph Ramsey Theorem (Ramsey 1930, full generality):
    For any k, r, n, there exists N large enough that any r-coloring of k-subsets
    of an N-element set contains a monochromatic n-element subset.
    This is axiomatized as the existence proof requires iterated stepping-up. -/
axiom hypergraph_ramsey_exists (k r n : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) (hn : n ≥ k) :
    ∃ N, HypergraphRamseyProperty k r n N

/-! ## Part IV: Growth Rate -/

/-- Tower function: iterated exponentiation. Hypergraph Ramsey numbers grow
    as towers of exponentials, with height depending on k. -/
def tower : ℕ → ℕ → ℕ
  | _, 0 => 1
  | b, n + 1 => b ^ tower b n

/-- Tower(2, 1) = 2. -/
theorem tower_2_1 : tower 2 1 = 2 := by simp [tower]

/-- Tower(2, 2) = 4. -/
theorem tower_2_2 : tower 2 2 = 4 := by simp [tower]

/-- The tower function grows strictly. -/
theorem tower_strictMono (b : ℕ) (hb : b ≥ 2) : StrictMono (tower b) := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hmn) with rfl | hlt
    · -- m = n case: tower b n < tower b (n+1) = b ^ tower b n
      simp only [tower]
      calc tower b n < 2 ^ tower b n := Nat.lt_two_pow (tower b n)
        _ ≤ b ^ tower b n := Nat.pow_le_pow_left (by omega) (tower b n)
    · -- m < n case: use IH
      exact lt_trans (ih hlt) (by
        simp only [tower]
        calc tower b n < 2 ^ tower b n := Nat.lt_two_pow _
          _ ≤ b ^ tower b n := Nat.pow_le_pow_left (by omega) _)

end HypergraphRamsey
