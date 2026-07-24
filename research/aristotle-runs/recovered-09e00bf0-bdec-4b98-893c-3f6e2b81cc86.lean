/-
Sum of the first n odd natural numbers.

Statement: For every natural number n,
    1 + 3 + 5 + ... + (2n - 1) = n²

Formally: ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2.

This is the classic arithmetic identity due to Pythagoras (the "gnomon"
argument: each successive odd number completes a larger square).  It is
used here as a small, well-known sanity check for the Harmonic
`StatementOnly_*.lean` Aristotle submission format.

Answer: n²
-/

import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option pp.fullNames true
set_option pp.structureInstances true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option linter.all false

noncomputable section

namespace SumOfOddsStatement

/-
The sum of the first `n` odd natural numbers equals `n ^ 2`.

This is a classic identity (Pythagoras' gnomon argument):
`1 + 3 + 5 + ... + (2 n - 1) = n²`.

Included here as a documented example of the Harmonic
`StatementOnly_*.lean` file format used for Aristotle submissions:
- single informal comment block at the top of the file,
- standard `set_option` block (verbatim from Harmonic),
- `noncomputable section` wrapper,
- exactly one theorem statement (proof body left as a hole),
- optional `-- Proof attempt:` scaffolding (Rivin pattern).
-/
theorem sum_of_first_n_odds (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n <;> simpa [Finset.sum_range_succ] using by linarith

-- Proof attempt: a sketch of the expected argument. Aristotle is free to
-- ignore this; it exists only to seed the MCTS prior.
-- 1. Induct on n. The base case n = 0 is `Finset.sum_range_zero` and `0 ^ 2 = 0`.
-- 2. For the step, use `Finset.sum_range_succ` to peel off the (n+1)-th term:
--      ∑ k ∈ range (n+1), (2 k + 1) = (∑ k ∈ range n, (2 k + 1)) + (2 n + 1).
--    Apply the IH and `ring` to conclude `n ^ 2 + (2 n + 1) = (n + 1) ^ 2`.

end SumOfOddsStatement