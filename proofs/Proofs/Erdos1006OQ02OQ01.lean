/-
  Erdős Problem #1006 - Open Question 02 - Open Question 01:
  Can the FFLLW sufficient condition (χ < girth) be sharpened?

  Source: https://erdosproblems.com/1006
  Related: Erdos1006OQ02.lean

  Question:
  FFLLW (1997) proved: if χ(G) < girth(G) then G admits a robustly acyclic orientation.
  Can this be sharpened to χ(G) ≤ girth(G)?

  Answer: NO.
  The complete graph K₃ has girth 3 and χ = 3, so χ = girth.
  Thus χ ≤ girth holds. But K₃ has no classically robust
  acyclic orientation (proved in Erdos1006OQ02.lean).
  Therefore χ ≤ girth is NOT sufficient for robust orientability.
  The FFLLW bound χ < girth is tight.

  This resolves the question negatively using the smallest possible counterexample.
-/

import Proofs.Erdos1006OQ02

open SimpleGraph

namespace Erdos1006OQ02OQ01

/-- **FFLLW cannot be sharpened to χ ≤ girth.**

    The FFLLW sufficient condition χ(G) < girth(G) for robust orientability
    is tight: relaxing to χ(G) ≤ girth(G) fails.

    Counterexample: K₃ has χ = girth = 3 and no classically robust orientation. -/
theorem ffllw_not_sharpenable_to_le :
    ¬(∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (G.chromaticNumber : ℕ∞) ≤ G.egirth →
      admitsClassicalRobustOrientation G) := by
  intro h
  apply girth3_classical_witness.2.2
  exact h (Fin 3) (⊤ : SimpleGraph (Fin 3))
    (by rw [k3_chromaticNumber_eq_3, k3_egirth_eq_3])

end Erdos1006OQ02OQ01
