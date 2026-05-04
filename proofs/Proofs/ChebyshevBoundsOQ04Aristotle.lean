/-
  Aristotle targets for ChebyshevBoundsOQ04
  Routine supporting lemma for automated proof search.
  See ChebyshevBoundsOQ04.lean for the main formalization.

  The key sorry: psi_doubling_le_log_centralBinom
  This encodes the classical von Mangoldt / Fubini argument:
    log(C(2n,n)) = sum_d Lambda(d) * (floor(2n/d) - 2*floor(n/d)) >= psi(2n) - psi(n)
  where Lambda is the von Mangoldt function.
  See: Chebyshev (1852), Hardy-Wright Section 22.7
-/
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ChebyshevBoundsOQ04

open Nat Finset ArithmeticFunction

noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), vonMangoldt k

theorem psi_doubling_le_log_centralBinom (n : ℕ) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ Real.log (Nat.centralBinom n : ℝ) := by
  sorry

end ChebyshevBoundsOQ04
