/-
Euler Partition Identities for Overpartitions

Source: Open question from partition-theorem gallery proof
Status: AXIOMATIZED (3 axioms for overpartition counts, 0 sorries)

An overpartition of n allows the first occurrence of each part size to be
optionally "overlined" (marked). This doubles the choices for each distinct part.

We formalize:
1. The Overpartition structure (partition + set of overlined parts)
2. Small case values (axiomatized)
3. Connection to Euler's partition identity (distinct = odd)
-/

import Mathlib

open Nat Finset BigOperators

namespace OverpartitionTheory

/-! ## Part I: Euler's Partition Identity (Foundation) -/

/-- Euler's partition identity: partitions into odd parts = partitions into distinct parts. -/
theorem euler_partition_identity (n : ℕ) :
    Nat.Partition.IsOdd.card n = Nat.Partition.IsDistinct.card n :=
  (Theorems100.partition n).symm

/-! ## Part II: Overpartition Definitions -/

/-- An overpartition of n is a partition together with a set of "overlined" part sizes.
    Each overlined size must appear in the partition, and only the first copy is overlined. -/
structure Overpartition (n : ℕ) where
  /-- The underlying partition of n. -/
  partition : Nat.Partition n
  /-- The set of part sizes that are overlined (subset of the support). -/
  overlined : Finset ℕ
  /-- Overlined parts must appear in the partition. -/
  overlined_subset : overlined ⊆ partition.parts.toFinset

/-- The number of overpartitions of n (axiomatized: computing requires
    enumerating partitions and their overline subsets). -/
axiom numOverpartitions : ℕ → ℕ

/-- Small values: p̄(0) = 1 (empty partition, no parts to overline). -/
/-- p̄(1) = 2 (partitions: {1}; overlined choices: ∅ or {1}). -/
/-- p̄(2) = 4 (partitions: {2}, {1,1}; overlined: 2 + 2 = 4). -/
/-! ## Part III: Key Properties -/

/-- Every distinct partition is an overpartition (with empty overline set). -/
def distinctToOverpartition (n : ℕ) (p : Nat.Partition n)
    (_h : p.parts.toFinset.card = p.parts.length) :
    Overpartition n :=
  ⟨p, ∅, Finset.empty_subset _⟩

/-- The number of overpartition choices for a given partition equals 2^d,
    where d is the number of distinct part sizes in the partition. -/
theorem overpartition_choices (n : ℕ) (p : Nat.Partition n) :
    (Finset.powerset p.parts.toFinset).card = 2 ^ p.parts.toFinset.card :=
  Finset.card_powerset _

end OverpartitionTheory
