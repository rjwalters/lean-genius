/-
  Aristotle targets for Erdős Problem #1100
  Routine supporting lemmas for automated proof search.
  See Erdos1100ProblemProvable.lean for the main formalization.

  Target: tau_perp_lower_bound
  The file header notes: "τ⊥(n) ≥ ω(n) trivially (with equality for infinitely many n)"

  Strategy: for each prime factor p | n, the divisor list contains some d with gcd(d, d') = 1
  where d' is the next divisor. The ω(n) prime factors supply at least ω(n) such transitions.

  Excluded from this companion:
  - erdos_hall_max_lower_bound: requires Erdős-Hall (1978) — deep analytic NT
  - erdos_simonovits_bounds: requires Erdős-Simonovits result — deep combinatorics
-/
import Mathlib
import Proofs.Erdos1100ProblemProvable

namespace Erdos1100

open Real Nat Finset

/-- τ⊥(n) ≥ ω(n): At least ω(n) consecutive coprime divisor pairs exist.
    The problem statement notes this is trivial; primes achieve equality. -/
theorem tau_perp_lower_bound (n : ℕ) (hn : n > 0) : tauPerp n ≥ omega n := by
  sorry

end Erdos1100
