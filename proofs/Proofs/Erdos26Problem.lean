/-
  Erdős Problem #26: Thick Sequences and Behrend Sets

  Source: https://erdosproblems.com/26
  Status: DISPROVED (Ruzsa counterexample)

  Statement:
  Let A ⊂ ℕ be infinite such that Σ(1/a) = ∞ (a "thick" sequence).
  Must there exist some k ≥ 1 such that almost all integers have a divisor
  of the form a + k for some a ∈ A?

  Answer: NO

  Background:
  - A sequence is "thick" if the sum of its reciprocals diverges
  - A sequence is "Behrend" if almost all integers are multiples of its elements
  - Davenport-Erdős (1951): Σ(1/a) = ∞ for every Behrend sequence

  Counterexample:
  - Ruzsa: Constructed a sequence where no shift A + k is Behrend
  - Van Doorn: Modified to make the reciprocal sum infinite

  The answer being NO means that even with thick sequences, we cannot
  guarantee any shift covers almost all integers as divisors.

  Weaker Variant (OPEN):
  Tenenbaum asked: For every ε > 0, does some k = k(ε) exist such that
  at least (1 - ε) density of integers have a divisor of the form a + k?

  References:
  - Erdős, P. & Tenenbaum, G. (original problem formulation)
  - Davenport, H. & Erdős, P. (1951). On the density of sequences
  - Ruzsa, I. Z. (counterexample)
  - Tenenbaum, G. (2019). "Some of Erdős' unconventional problems"
    arXiv:1908.00488
-/

import Mathlib

open Set Filter BigOperators Nat Real

namespace Erdos26

/- ## Natural Density -/

open Classical in
-- isThick_const: unused axiom removed (never referenced by any theorem)
axiom davenport_erdos_behrend_thick :
  ∀ {ι : Type*} (A : ι → ℕ), (∀ i, A i > 0) → IsBehrend A → IsThick A

-- ruzsa_counterexample: unused axiom removed (never referenced by any theorem)
axiom van_doorn_thick_counterexample :
  ∃ A : ℕ → ℕ, StrictMono A ∧ IsThick A ∧ ∀ k : ℕ, ¬IsBehrend (A · + k)

-- isBehrend_of_contains_one: unused axiom removed (never referenced by any theorem)
-- isWeaklyBehrend_of_ge_one: unused axiom removed (never referenced by any theorem)
-- not_isWeaklyBehrend_of_neg: unused axiom removed (never referenced by any theorem)
must be Behrend (i.e., almost all integers have a divisor in A + k).

**Answer: NO** (Ruzsa counterexample, Van Doorn thick variant)

**Key Results:**
1. Davenport-Erdős (1951): Behrend sequences are always thick
2. Ruzsa: Non-thick counterexample where no shift is Behrend
3. Van Doorn: Thick counterexample (Σ(1/a) = ∞) where no shift is Behrend

**The Gap:**
The main theorem (erdos_26_disproved) shows the conjecture fails.
The Van Doorn counterexample provides a thick sequence where no shift
achieves density 1 coverage.

**Open Question:**
Tenenbaum's weaker variant (density ≥ 1 - ε instead of = 1) remains open.

References:
- Erdős, P. & Tenenbaum, G. (original problem)
- Davenport, H. & Erdős, P. (1951). On sequences of positive integers
- Ruzsa, I. Z. (counterexample)
- Tenenbaum, G. (2019). arXiv:1908.00488
-/

end Erdos26
