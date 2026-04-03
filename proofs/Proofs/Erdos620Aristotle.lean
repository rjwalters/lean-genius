/-
  Aristotle targets for Erdős Problem #620
  Routine supporting lemmas for automated proof search.
  See Erdos620Problem.lean for the main formalization.

  Criteria for inclusion:
  - turan_is_K4Free: pigeonhole on 3 residue classes mod 3 (omega)
  - four_values_mod3_has_duplicate: 4 values, 3 classes → duplicate (omega)
  - mod3_lt_three: trivial bound (norm_num)
  - turanGraph3_adj_iff: definitional equality
  - NOT sparse_case (complex independent set construction)
  - NOT erdos_rogers_ramsey_connection (complex Ramsey theory)
  - NOT original_is_f43 (K4Free vs CliqueFree 4 mismatch)
  - NOT erdos_620_unsolved (open problem, not a routine lemma)
-/
import Mathlib

namespace Erdos620Aristotle

open SimpleGraph Finset

/-- A K₄ (complete graph on 4 vertices) in a graph. -/
def HasK4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- A graph is K₄-free if it contains no complete graph on 4 vertices. -/
def K4Free {V : Type*} (G : SimpleGraph V) : Prop := ¬HasK4 G

/-- The Turán graph T(n,3): connect vertices with different residues mod 3. -/
def turanGraph3 (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val % 3 ≠ j.val % 3
  symm := by intro i j h; exact Ne.symm h
  loopless := by intro i h; exact h rfl

-- Routine: n % 3 < 3 for any natural number n.
theorem mod3_lt_three (n : ℕ) : n % 3 < 3 := by
  sorry

-- Routine: Any 4 natural numbers must have two with equal residue mod 3.
-- By pigeonhole: 4 pigeons into 3 holes (residues 0, 1, 2).
theorem four_values_mod3_has_duplicate (a b c d : ℕ) :
    a % 3 = b % 3 ∨ a % 3 = c % 3 ∨ a % 3 = d % 3 ∨
    b % 3 = c % 3 ∨ b % 3 = d % 3 ∨ c % 3 = d % 3 := by
  sorry

-- Routine: The adjacency condition of turanGraph3 unfolds definitionally.
theorem turanGraph3_adj_iff (n : ℕ) (i j : Fin n) :
    (turanGraph3 n).Adj i j ↔ i.val % 3 ≠ j.val % 3 := by
  sorry

-- Routine: The Turán graph T(n,3) is K₄-free.
-- If 4 vertices were mutually adjacent, their mod-3 residues would be pairwise
-- distinct. But there are only 3 residue classes, so by pigeonhole two share
-- a residue and hence are not adjacent — contradiction.
theorem turan_is_K4Free (n : ℕ) : K4Free (turanGraph3 n) := by
  sorry

end Erdos620Aristotle
