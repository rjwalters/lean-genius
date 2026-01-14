/-
  Erdős Problem #70: Partition Calculus for the Continuum

  Source: https://erdosproblems.com/70
  Status: OPEN

  Statement:
  Let 𝔠 be the cardinality of the continuum, β be any countable ordinal, and 2 ≤ n < ω.
  Is it true that 𝔠 → (β, n)₂³?

  Notation:
  κ → (α, β)ₖⁿ means: for any k-coloring of the n-element subsets of a set S with |S| = κ,
  either there is a homogeneous set of order type α for color 0, or a homogeneous set
  of order type β for color 1.

  History:
  - Erdős-Rado proved: 𝔠 → (ω+n, 4)₂³ for any 2 ≤ n < ω
  - The general case for arbitrary countable β remains OPEN

  Background:
  This is a problem in partition calculus, a branch of combinatorial set theory.
  It asks whether the continuum satisfies certain Ramsey-type properties.

  This file formalizes the definitions and known results.
-/

import Mathlib

open Set Cardinal Ordinal

namespace Erdos70

/-! ## Basic Definitions -/

/-- A k-coloring of n-element subsets of a set S. -/
def Coloring (S : Type*) (n k : ℕ) :=
  { t : Finset S // t.card = n } → Fin k

/-- The set of n-element subsets of S. -/
def nSubsets (S : Type*) [DecidableEq S] (n : ℕ) : Set (Finset S) :=
  { t | t.card = n }

/-! ## Homogeneous Sets -/

/-- A set H is homogeneous for coloring c with color i if all n-subsets of H get color i. -/
def IsHomogeneous {S : Type*} [DecidableEq S] (H : Set S) (n : ℕ)
    (c : Coloring S n 2) (i : Fin 2) : Prop :=
  ∀ (t : Finset S) (ht : t.card = n), (↑t : Set S) ⊆ H → c ⟨t, ht⟩ = i

/-- A finset is homogeneous for a coloring. -/
def FinsetIsHomogeneous {S : Type*} [DecidableEq S] (H : Finset S) (n k : ℕ)
    (c : Coloring S n k) (i : Fin k) : Prop :=
  ∀ (t : Finset S) (ht : t.card = n), t ⊆ H → c ⟨t, ht⟩ = i

/-! ## Order Types -/

/-- A set has order type at least α under some well-ordering (simplified version).
    We use cardinal comparison: H has at least as many elements as α. -/
def HasOrderTypeAtLeast (S : Type*) (H : Set S) (α : Ordinal) : Prop :=
  α.card ≤ Cardinal.mk H

/-! ## Partition Arrow -/

/--
The partition arrow κ → (α, m)₂³ (for ordinals α and natural m).

This means: for any 2-coloring of 3-element subsets of a set S with |S| = κ,
either there is a homogeneous set of order type α for color 0,
or there is a homogeneous set of size m for color 1.
-/
def PartitionArrow (κ : Cardinal) (α : Ordinal) (m : ℕ) : Prop :=
  ∀ (S : Type) [DecidableEq S] (_ : #S = κ) (c : Coloring S 3 2),
    (∃ (H : Set S), HasOrderTypeAtLeast S H α ∧ IsHomogeneous H 3 c 0) ∨
    (∃ (H : Finset S), H.card ≥ m ∧ FinsetIsHomogeneous H 3 2 c 1)

/-! ## The Continuum -/

/-- The cardinality of the continuum. -/
noncomputable def continuum_card : Cardinal := Cardinal.continuum

/-- The continuum equals 2^ℵ₀. -/
theorem continuum_def : continuum_card = 2 ^ Cardinal.aleph0 :=
  Cardinal.two_power_aleph0.symm

/-! ## Countable Ordinals -/

/-- An ordinal is countable if its cardinality is at most ℵ₀. -/
def IsCountableOrdinal (α : Ordinal) : Prop := α.card ≤ Cardinal.aleph0

/-- ω (the first infinite ordinal) is countable. -/
theorem omega0_countable : IsCountableOrdinal Ordinal.omega0 := by
  unfold IsCountableOrdinal
  simp [Ordinal.card_omega0]

/-- Any natural number as an ordinal is countable. -/
theorem nat_countable (n : ℕ) : IsCountableOrdinal n := by
  unfold IsCountableOrdinal
  simp only [Ordinal.card_nat]
  exact Cardinal.nat_lt_aleph0 n |>.le

/-! ## Erdős-Rado Theorem -/

/--
**Erdős-Rado Theorem** (partial):
For any 2 ≤ n < ω, we have 𝔠 → (ω + n, 4)₂³.

This means: for any 2-coloring of 3-element subsets of a set of continuum size,
either there is a homogeneous set of order type ω + n for color 0,
or there is a homogeneous set of size 4 for color 1.
-/
axiom erdos_rado_omega_plus_n (n : ℕ) (hn : 2 ≤ n) :
    PartitionArrow continuum_card (Ordinal.omega0 + n) 4

/-! ## Main Conjecture (OPEN) -/

/--
**Erdős Problem 70** (OPEN):
For any countable ordinal β and 2 ≤ n < ω, is it true that 𝔠 → (β, n)₂³?

This asks whether the continuum satisfies this partition relation for ALL
countable ordinals, not just ω + n.
-/
def erdos_70_conjecture : Prop :=
  ∀ (β : Ordinal.{0}) (n : ℕ), IsCountableOrdinal β → 2 ≤ n →
    PartitionArrow continuum_card β n

/-! ## Special Cases -/

/-- The conjecture for β = ω. -/
def conjecture_omega (n : ℕ) : Prop :=
  PartitionArrow continuum_card Ordinal.omega0 n

/-- The conjecture for β = ω². -/
def conjecture_omega_squared (n : ℕ) : Prop :=
  PartitionArrow continuum_card (Ordinal.omega0 * Ordinal.omega0) n

/-- The conjecture for β = ω^ω. -/
def conjecture_omega_tower (n : ℕ) : Prop :=
  PartitionArrow continuum_card (Ordinal.omega0 ^ Ordinal.omega0) n

/-! ## Finite Ramsey Theory -/

/--
**Finite Ramsey Theorem** (axiomatized):
For any r, k, n there exists N such that N → (r)ₖⁿ.
(Any k-coloring of n-subsets of an N-set has a homogeneous r-set.)
-/
axiom finite_ramsey (r k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ∃ N : ℕ, ∀ (c : Coloring (Fin N) n k),
      ∃ (H : Finset (Fin N)) (i : Fin k), H.card ≥ r ∧
        FinsetIsHomogeneous H n k c i

/--
**Ramsey's Theorem** (specific case):
For 3-subsets with 2 colors, R(3,3) = 6.
Any 2-coloring of 3-subsets of a 6-set has a monochromatic 3-subset.
-/
axiom ramsey_3_3 : ∀ (c : Coloring (Fin 6) 3 2),
    ∃ (H : Finset (Fin 6)) (i : Fin 2), H.card ≥ 3 ∧
      FinsetIsHomogeneous H 3 2 c i

/-! ## Negative Results -/

/--
**Negative Direction** (if the conjecture is false):
There would exist a countable β and n ≥ 2 such that 𝔠 ↛ (β, n)₂³.
This would give a 2-coloring with no large homogeneous sets.
-/
def erdos_70_counterexample : Prop :=
  ∃ (β : Ordinal.{0}) (n : ℕ), IsCountableOrdinal β ∧ 2 ≤ n ∧
    ¬PartitionArrow continuum_card β n

/-- The conjecture and counterexample are mutually exclusive. -/
theorem conjecture_xor_counterexample :
    erdos_70_conjecture ↔ ¬erdos_70_counterexample := by
  unfold erdos_70_conjecture erdos_70_counterexample
  push_neg
  rfl

/-! ## Monotonicity -/

/-- Partition arrows are monotonic in the ordinal parameter. -/
axiom partition_arrow_mono_ordinal (κ : Cardinal) (α β : Ordinal) (m : ℕ)
    (hαβ : α ≤ β) (h : PartitionArrow κ β m) : PartitionArrow κ α m

/-- Partition arrows are monotonic in the size parameter. -/
axiom partition_arrow_mono_size (κ : Cardinal) (α : Ordinal) (m n : ℕ)
    (hmn : m ≤ n) (h : PartitionArrow κ α n) : PartitionArrow κ α m

/-! ## Related Ordinal Arithmetic -/

/-- ω + n is countable for any n. -/
theorem omega0_plus_n_countable (n : ℕ) : IsCountableOrdinal (Ordinal.omega0 + n) := by
  unfold IsCountableOrdinal
  rw [Ordinal.card_add, Ordinal.card_omega0, Ordinal.card_nat, Cardinal.aleph0_add_nat]

/-- ω * ω is countable. -/
theorem omega0_squared_countable : IsCountableOrdinal (Ordinal.omega0 * Ordinal.omega0) := by
  unfold IsCountableOrdinal
  rw [Ordinal.card_mul, Ordinal.card_omega0, Cardinal.aleph0_mul_aleph0]

/-! ## Summary

**Problem Status: OPEN**

Erdős Problem 70 asks whether 𝔠 → (β, n)₂³ holds for all countable ordinals β
and all 2 ≤ n < ω.

**Known Results**:
1. Erdős-Rado: 𝔠 → (ω + n, 4)₂³ for all 2 ≤ n < ω
2. Finite Ramsey theory provides the finite analogue
3. The full conjecture for arbitrary countable β remains open

**Open Questions**:
- Does 𝔠 → (ω², n)₂³ hold?
- Does 𝔠 → (ω^ω, n)₂³ hold?
- What is the relationship to CH (Continuum Hypothesis)?

References:
- Erdős, Rado: "A partition calculus in set theory"
- Erdős (1987): Original problem statement [Er87]
- Graham, Rothschild, Spencer: "Ramsey Theory"
-/

end Erdos70
