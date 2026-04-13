/-
  Aristotle targets for Erdős Problem #476 (Erdős-Heilbronn Conjecture)
  Routine supporting lemmas for automated proof search.
  See Erdos476Problem.lean for the main formalization.

  Criteria for inclusion:
  - card_two_case: |A| = 2 → |A +̂ A| = 1 (Finset case analysis + commutativity)
  - ap_card_eq_n: arithmetic progression has n elements when d ≠ 0, n ≤ p
  - NOT restrictedSumsetR definition (definition sorry)
  - NOT combinatorial_nullstellensatz (deep exterior algebra)
  - NOT erdos_476 (main result, axiomatized)
-/
import Mathlib

namespace Erdos476Aristotle

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- The restricted sumset A +̂ A = {a + b : a ≠ b, a b ∈ A}. -/
def restrictedSumset (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A.product A).filter (fun ab => ab.1 ≠ ab.2) |>.image (fun ab => ab.1 + ab.2)

/-- Arithmetic progression {a, a+d, ..., a+(n-1)d} in ZMod p. -/
def arithmeticProgression (a d : ZMod p) (n : ℕ) : Finset (ZMod p) :=
  (Finset.range n).image (fun i => a + i • d)

-- Routine: When |A| = 2, write A = {a, b} and observe that
-- the only pairs with distinct elements are (a,b) and (b,a),
-- both giving sum a+b = b+a (commutativity in ZMod p).
-- So A +̂ A = {a + b}, which has cardinality 1.
theorem card_two_case (A : Finset (ZMod p)) (h : A.card = 2) :
    (restrictedSumset p A).card = 1 := by
  sorry

-- Routine: The map i ↦ a + i • d is injective on {0,...,n-1}
-- when d ≠ 0 in ZMod p (a field) and n ≤ p.
-- Hence (Finset.range n).image (fun i => a + i • d) has card = n.
theorem ap_card_eq_n (a d : ZMod p) (n : ℕ) (hd : d ≠ 0) (hn : n ≤ p) :
    (arithmeticProgression p a d n).card = n := by
  sorry

end Erdos476Aristotle
