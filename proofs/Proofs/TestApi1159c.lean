import Mathlib

open Configuration

universe u

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]

-- Try to prove line has a point using pointCount
example (l : L) : ∃ p : P, p ∈ l := by
  have hpc := ProjectivePlane.pointCount_eq P l
  have hord := ProjectivePlane.one_lt_order P L
  rw [Configuration.pointCount] at hpc
  have hpos : 0 < Nat.card {p : P // p ∈ l} := by omega
  rw [Nat.card_pos_iff] at hpos
  obtain ⟨⟨p, hp⟩⟩ := hpos
  exact ⟨p, hp⟩

-- Try univ_blocking_set using the above
example : ∀ l : L, ∃ p ∈ Set.univ, (p : P) ∈ l := by
  intro l
  have hpc := ProjectivePlane.pointCount_eq P l
  have hord := ProjectivePlane.one_lt_order P L
  rw [Configuration.pointCount] at hpc
  have hpos : 0 < Nat.card {p : P // p ∈ l} := by omega
  rw [Nat.card_pos_iff] at hpos
  obtain ⟨⟨p, hp⟩⟩ := hpos
  exact ⟨p, Set.mem_univ p, hp⟩

-- Try conjecture_equiv_bounded
-- First define the types
def IsBlockingSet' {P L : Type*} [Membership P L] (S : Set P) : Prop :=
  ∀ l : L, ∃ p ∈ S, p ∈ l

def IsBoundedBlockingSet' {P L : Type*} [Membership P L] (S : Set P) (C : ℕ) : Prop :=
  (@IsBlockingSet' P L _ S) ∧ ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤ C

example :
    (∃ C : ℕ, ∀ (P L : Type u) [Membership P L] [ProjectivePlane P L]
      [Fintype P] [Fintype L],
      ∃ S : Set P, (@IsBoundedBlockingSet' P L _ S C)) ↔
    (∃ C : ℕ, ∀ (P L : Type u) [Membership P L] [ProjectivePlane P L]
      [Fintype P] [Fintype L],
      ∃ S : Set P, (@IsBlockingSet' P L _ S) ∧
        ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤ C) := by
  constructor
  · intro ⟨C, hC⟩
    refine ⟨C, fun P L _ _ _ _ => ?_⟩
    obtain ⟨S, hb⟩ := hC P L
    exact ⟨S, hb.1, hb.2⟩
  · intro ⟨C, hC⟩
    refine ⟨C, fun P L _ _ _ _ => ?_⟩
    obtain ⟨S, hblock, hbound⟩ := hC P L
    exact ⟨S, hblock, hbound⟩
