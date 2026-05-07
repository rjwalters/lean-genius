/-
  Aristotle targets for Erdos933Problem
  Routine supporting lemmas for automated proof search.
  See Erdos933Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT steinerberger_gives_large_smooth (deep analytic argument)
  - NOT steinerberger_proof (axiom — Aristotle skips)
  - Factorization additivity lemmas: power of prime p in n*(n+1)
    equals sum of powers in n and n+1 (from Nat.factorization_mul)
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (2):
  - power2_consecutive_ari: v_2(n*(n+1)) = v_2(n) + v_2(n+1)
  - power3_consecutive_ari: v_3(n*(n+1)) = v_3(n) + v_3(n+1)

  NOT included:
  - steinerberger_proof: axiom (Aristotle skips)
  - steinerberger_gives_large_smooth: requires analytic estimates
-/
import Mathlib
import Proofs.Erdos933Problem

namespace Erdos933ProblemAristotle

open Erdos933 Nat

/-
## Factorization Additivity for Consecutive Products

The key tool is Nat.factorization_mul: for m, n > 0,
  (m * n).factorization = m.factorization + n.factorization

as Finsupps of prime exponents, so evaluating at any prime p gives
  v_p(m * n) = v_p(m) + v_p(n).

For n = 0, factorization 0 = 0 and n*(n+1) = 0, so both sides are 0.
For n > 0, n+1 > 0 always, so Nat.factorization_mul applies.
-/

/-- The 2-adic valuation of n*(n+1) equals the sum of 2-adic valuations of n and n+1. -/
theorem power2_consecutive_ari (n : ℕ) :
    (n * (n + 1)).factorization 2 =
      n.factorization 2 + (n + 1).factorization 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.factorization_mul hn.ne' (Nat.succ_ne_zero n), Finsupp.add_apply]

/-- The 3-adic valuation of n*(n+1) equals the sum of 3-adic valuations of n and n+1. -/
theorem power3_consecutive_ari (n : ℕ) :
    (n * (n + 1)).factorization 3 =
      n.factorization 3 + (n + 1).factorization 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.factorization_mul hn.ne' (Nat.succ_ne_zero n), Finsupp.add_apply]

end Erdos933ProblemAristotle
