import Mathlib

open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]

-- Try to prove line has a point using pointCount
example (l : L) : ∃ p : P, p ∈ l := by
  have hpc := ProjectivePlane.pointCount_eq P L l
  have hord := ProjectivePlane.one_lt_order P L
  have hpos : 0 < Nat.card {p : P // p ∈ l} := by omega
  rw [Nat.card_pos_iff] at hpos
  obtain ⟨⟨p, hp⟩⟩ := hpos
  exact ⟨p, hp⟩

-- Try univ_blocking_set using the above
example : ∀ l : L, ∃ p ∈ Set.univ, (p : P) ∈ l := by
  intro l
  have hpc := ProjectivePlane.pointCount_eq P L l
  have hord := ProjectivePlane.one_lt_order P L
  have hpos : 0 < Nat.card {p : P // p ∈ l} := by omega
  rw [Nat.card_pos_iff] at hpos
  obtain ⟨⟨p, hp⟩⟩ := hpos
  exact ⟨p, Set.mem_univ p, hp⟩

-- Try conjecture_equiv_bounded
-- First define the types
def IsBlockingSet' {P L : Type*} [Membership P L] (S : Set P) : Prop :=
  ∀ l : L, ∃ p ∈ S, p ∈ l

def IsBoundedBlockingSet' {P L : Type*} [Membership P L] (S : Set P) (C : ℕ) : Prop :=
  IsBlockingSet' S ∧ ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤ C

example :
    (∃ C : ℕ, ∀ (P L : Type*) [Membership P L] [ProjectivePlane P L]
      [Fintype P] [Fintype L],
      ∃ S : Set P, IsBoundedBlockingSet' S C) ↔
    (∃ C : ℕ, ∀ (P L : Type*) [Membership P L] [ProjectivePlane P L]
      [Fintype P] [Fintype L],
      ∃ S : Set P, IsBlockingSet' S ∧
        ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤ C) := by
  constructor
  · intro ⟨C, hC⟩
    exact ⟨C, fun P L _ _ _ _ => by
      obtain ⟨S, hblock, hbound⟩ := hC P L
      exact ⟨S, hblock, hbound⟩⟩
  · intro ⟨C, hC⟩
    exact ⟨C, fun P L _ _ _ _ => by
      obtain ⟨S, hblock, hbound⟩ := hC P L
      exact ⟨S, hblock, hbound⟩⟩
