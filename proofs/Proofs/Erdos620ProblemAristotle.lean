/-
  Aristotle targets for Erdos620Problem (Erdős-Rogers Problem)
  Routine supporting lemmas for automated proof search.
  See Erdos620Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (exact value of f(n) = erdosRogers)
  - NOT open conjectures (Shearer's lower bound, Mubayi-Verstraete upper bound)
  - Structural results about the Turán graph T(n,3) provable by finite reasoning
  - No definition sorries, no axioms

  Targets:
  1. turan_is_K4Free: The Turán graph T(n,3) is K₄-free
     Proof strategy: T(n,3) is 3-colorable via i ↦ i.val % 3.
     A K₄ requires 4 mutually adjacent vertices.  In T(n,3), adjacency means
     having different residues mod 3.  Four pairwise-distinct values in {0,1,2}
     is impossible (only 3 distinct values exist).
     Tactic: omega closes the goal once all 4 residues are bounded below 3
     and shown pairwise distinct.

  Excluded (deep results, not Aristotle targets):
  - sparse_case: requires independent set extraction from sparse graphs
  - erdos_rogers_ramsey_connection: requires Ramsey number infrastructure
  - original_is_f43: definitional mismatch between K4Free and CliqueFree 4
  - erdos_620_unsolved: open problem (placeholder sorry)
-/
import Mathlib
import Proofs.Erdos620Problem

namespace Erdos620.Aristotle

/-
## Aristotle Target: Turán graph K₄-freeness

The Turán graph T(n,3) has adjacency i adj j ↔ i.val % 3 ≠ j.val % 3.
Any K₄ would require 4 vertices with pairwise-distinct residues mod 3,
but only 3 residues (0, 1, 2) exist — contradiction by omega.
-/

/-- **Turán graph T(n,3) is K₄-free** (primary Aristotle target).

    Proof strategy:
    1. Unfold K4Free and HasK4; assume ∃ a b c d with all 6 pairs adjacent.
    2. Adjacency in turanGraph3 means i.val % 3 ≠ j.val % 3.
    3. So a.val%3, b.val%3, c.val%3, d.val%3 are four pairwise-distinct naturals.
    4. All four are < 3 (by Nat.mod_lt with divisor 3).
    5. Four pairwise-distinct naturals all < 3 is impossible: omega. -/
theorem turan_is_K4Free (n : ℕ) : Erdos620.K4Free (Erdos620.turanGraph3 n) := by
  rintro ⟨a, b, c, d, -, -, -, -, -, -, hab, hac, had, hbc, hbd, hcd⟩
  simp only [Erdos620.turanGraph3] at hab hac had hbc hbd hcd
  omega

end Erdos620.Aristotle
