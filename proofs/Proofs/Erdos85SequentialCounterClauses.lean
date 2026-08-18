import Proofs.Erdos85SequentialCounter

/-!
# Clause semantics for the PySAT sequential counter

The numeric generator allocates DIMACS identifiers to two kinds of atoms:
input literals and Knuth counter variables `(k,j)`.  This file proves the
four symbolic clause schemas independently of that allocation.  Consequently
the remaining DIMACS bridge only has to show that allocation and signed-literal
reification preserve these semantics.
-/

namespace Erdos85

/-- Symbolic atoms appearing in one sequential-counter block. -/
inductive SeqCounterAtom (n : Nat) where
  | input : Fin n → SeqCounterAtom n
  | aux : Nat → Nat → SeqCounterAtom n
deriving DecidableEq

/-- A symbolic literal; `positive = false` denotes negation. -/
structure SeqCounterLit (n : Nat) where
  positive : Bool
  atom : SeqCounterAtom n
deriving DecidableEq

abbrev SeqCounterClause (n : Nat) := List (SeqCounterLit n)

def seqCounterAtomValue {n : Nat} (x : Fin n → Bool) :
    SeqCounterAtom n → Bool
  | .input i => x i
  | .aux k j => seqCounterWitness x (j + k) k

def seqCounterLitValue {n : Nat} (x : Fin n → Bool)
    (lit : SeqCounterLit n) : Bool :=
  if lit.positive then seqCounterAtomValue x lit.atom
  else !(seqCounterAtomValue x lit.atom)

def seqCounterClauseSatisfied {n : Nat} (x : Fin n → Bool)
    (clause : SeqCounterClause n) : Prop :=
  ∃ lit ∈ clause, seqCounterLitValue x lit = true

def seqCounterPos {n : Nat} (a : SeqCounterAtom n) : SeqCounterLit n :=
  ⟨true, a⟩

def seqCounterNegLit {n : Nat} (a : SeqCounterAtom n) : SeqCounterLit n :=
  ⟨false, a⟩

/-- PySAT/Knuth base clause `¬x_j ∨ s(0,j)`. -/
theorem seqCounter_base_clause_satisfied {n : Nat} (x : Fin n → Bool)
    (j : Nat) (hj : j < n) :
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.input ⟨j, hj⟩), seqCounterPos (.aux 0 j)] := by
  by_cases hx : x ⟨j, hj⟩ = true
  · refine ⟨seqCounterPos (.aux 0 j), by simp, ?_⟩
    simp [seqCounterLitValue, seqCounterAtomValue, seqCounterPos,
      seqCounterKnuth_base x j hj hx]
  · refine ⟨seqCounterNegLit (.input ⟨j, hj⟩), by simp, ?_⟩
    cases hval : x ⟨j, hj⟩ <;> simp_all [seqCounterLitValue,
      seqCounterAtomValue, seqCounterNegLit]

/-- PySAT/Knuth horizontal clause `¬s(k,j) ∨ s(k,j+1)`. -/
theorem seqCounter_horizontal_clause_satisfied {n : Nat} (x : Fin n → Bool)
    (k j : Nat) (hnext : j + k + 1 < n) :
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.aux k j), seqCounterPos (.aux k (j + 1))] := by
  by_cases hs : seqCounterWitness x (j + k) k = true
  · refine ⟨seqCounterPos (.aux k (j + 1)), by simp, ?_⟩
    simp [seqCounterLitValue, seqCounterAtomValue, seqCounterPos,
      seqCounterKnuth_horizontal x k j hnext hs]
  · refine ⟨seqCounterNegLit (.aux k j), by simp, ?_⟩
    cases hval : seqCounterWitness x (j + k) k <;>
      simp_all [seqCounterLitValue, seqCounterAtomValue, seqCounterNegLit]

/-- PySAT/Knuth diagonal clause
`¬x_(j+k+1) ∨ ¬s(k,j) ∨ s(k+1,j)`. -/
theorem seqCounter_diagonal_clause_satisfied {n : Nat} (x : Fin n → Bool)
    (k j : Nat) (hidx : j + k + 1 < n) :
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.input ⟨j + k + 1, hidx⟩),
       seqCounterNegLit (.aux k j), seqCounterPos (.aux (k + 1) j)] := by
  by_cases hx : x ⟨j + k + 1, hidx⟩ = true
  · by_cases hs : seqCounterWitness x (j + k) k = true
    · refine ⟨seqCounterPos (.aux (k + 1) j), by simp, ?_⟩
      simp [seqCounterLitValue, seqCounterAtomValue, seqCounterPos,
        seqCounterKnuth_diagonal x k j hidx hx hs]
    · refine ⟨seqCounterNegLit (.aux k j), by simp, ?_⟩
      cases hval : seqCounterWitness x (j + k) k <;>
        simp_all [seqCounterLitValue, seqCounterAtomValue, seqCounterNegLit]
  · refine ⟨seqCounterNegLit (.input ⟨j + k + 1, hidx⟩), by simp, ?_⟩
    cases hval : x ⟨j + k + 1, hidx⟩ <;>
      simp_all [seqCounterLitValue, seqCounterAtomValue, seqCounterNegLit]

/-- PySAT/Knuth terminal clause `¬x_(j+t) ∨ ¬s(t-1,j)`. -/
theorem seqCounter_overflow_clause_satisfied {n : Nat} (x : Fin n → Bool)
    (t j : Nat) (ht : 0 < t) (hidx : j + t < n)
    (htotal : seqPrefixTrue x n ≤ t) :
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.input ⟨j + t, hidx⟩),
       seqCounterNegLit (.aux (t - 1) j)] := by
  by_cases hx : x ⟨j + t, hidx⟩ = true
  · refine ⟨seqCounterNegLit (.aux (t - 1) j), by simp, ?_⟩
    have hs := seqCounterKnuth_no_overflow x t j ht hidx htotal hx
    simp [seqCounterLitValue, seqCounterAtomValue, seqCounterNegLit, hs]
  · refine ⟨seqCounterNegLit (.input ⟨j + t, hidx⟩), by simp, ?_⟩
    cases hval : x ⟨j + t, hidx⟩ <;>
      simp_all [seqCounterLitValue, seqCounterAtomValue, seqCounterNegLit]

/-- All clause schemas traversed by PySAT's nontrivial at-most loop.  The
four fields use exactly its bounds: base and overflow for `j < n-t`,
horizontal propagation for `k<t, j<n-t-1`, and diagonal propagation for
`k<t-1, j<n-t`. -/
structure SeqCounterKnuthSchemasHold {n : Nat} (x : Fin n → Bool)
    (t : Nat) (ht : 0 < t) (hnontrivial : t + 1 < n) : Prop where
  base : ∀ j, ∀ hj : j < n - t,
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.input ⟨j, lt_of_lt_of_le hj (Nat.sub_le n t)⟩),
       seqCounterPos (.aux 0 j)]
  horizontal : ∀ k j, ∀ _hk : k < t, ∀ _hj : j < n - t - 1,
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.aux k j),
       seqCounterPos (.aux k (j + 1))]
  diagonal : ∀ k j, ∀ hk : k < t - 1, ∀ hj : j < n - t,
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.input ⟨j + k + 1, by omega⟩),
       seqCounterNegLit (.aux k j),
       seqCounterPos (.aux (k + 1) j)]
  overflow : ∀ j, ∀ hj : j < n - t,
    seqCounterClauseSatisfied x
      [seqCounterNegLit (.input ⟨j + t, by omega⟩),
       seqCounterNegLit (.aux (t - 1) j)]

/-- A row satisfying the at-most bound canonically satisfies every symbolic
clause visited by the exact PySAT loop. -/
theorem seqCounter_knuthSchemasHold {n : Nat} (x : Fin n → Bool)
    (t : Nat) (ht : 0 < t) (hnontrivial : t + 1 < n)
    (htotal : seqPrefixTrue x n ≤ t) :
    SeqCounterKnuthSchemasHold x t ht hnontrivial := by
  constructor
  · intro j hj
    exact seqCounter_base_clause_satisfied x j (by omega)
  · intro k j hk hj
    exact seqCounter_horizontal_clause_satisfied x k j (by omega)
  · intro k j hk hj
    exact seqCounter_diagonal_clause_satisfied x k j (by omega)
  · intro j hj
    exact seqCounter_overflow_clause_satisfied x t j ht (by omega) htotal

end Erdos85
