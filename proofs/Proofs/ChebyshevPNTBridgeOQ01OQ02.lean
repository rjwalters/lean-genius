/-
# Chebyshev Prime Bound: Alternative Proof via prod_pow_factorization_centralBinom

This file answers the research question from chebyshev-pnt-bridge-oq-01-oq-02:

> Can `centralBinom_le_pow_primeCounting` be proved by reconstructing the central binomial
> coefficient from its prime factorization using `Nat.factorization_prod_pow_eq_self`?

**Finding**: Yes — and Mathlib provides an even more direct lemma:
`Nat.prod_pow_factorization_centralBinom` in `Mathlib.Data.Nat.Choose.Factorization`.
This lemma gives the factorization identity for centralBinom directly, without requiring
the hypothesis `centralBinom n ≠ 0` that the original proof needs.

## Proof Comparison

**Original proof** (ChebyshevPNTBridge.lean, lines 203–212):
- Uses `Nat.factorization_prod_pow_eq_self hcb_ne` (requires `hcb_ne : centralBinom n ≠ 0`)
- Reconstructs via `Finsupp.prod` over the factorization support
- Needs separate `hprime_of_mem` and `hsub` lemmas

**This proof** (4 calc steps):
- Uses `Nat.prod_pow_factorization_centralBinom n` (no nonzero hypothesis)
- Works over `Finset.range (2 * n + 1)`; non-prime terms vanish since `(centralBinom n).factorization p = 0`
  for non-prime `p`, giving `p^0 = 1`
- Filters to primes via `Finset.prod_filter_of_ne`
- Bounds via `Nat.pow_factorization_choose_le` and counts via `Nat.primeCounting`

Both proofs encode the same mathematics: C(2n,n) is a product of at most π(2n)
prime powers, each bounded by 2n.

**Status**: COMPLETE (0 sorries, 0 axioms)
-/

import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace ChebyshevPNTBridgeOQ01OQ02

open Nat Finset

/-- **Alternative proof of the Chebyshev prime bound** via `prod_pow_factorization_centralBinom`.

    Proves C(2n,n) ≤ (2n)^{π(2n)} in four calc steps, using Mathlib's specialized
    factorization identity for centralBinom. Key difference from ChebyshevPNTBridge.lean:
    no `hcb_ne : centralBinom n ≠ 0` hypothesis needed.

    This answers chebyshev-pnt-bridge-oq-01-oq-02: the factorization approach works,
    and `Nat.prod_pow_factorization_centralBinom` is the right Mathlib lemma for it. -/
theorem centralBinom_le_pow_primeCounting_via_factorization (n : ℕ) (hn : 1 ≤ n) :
    centralBinom n ≤ (2 * n) ^ primeCounting (2 * n) := by
  calc centralBinom n
      -- Step 1: centralBinom n = ∏ p ∈ range(2n+1), p^(factorization p)
      -- Using Mathlib's specialized lemma (no hcb_ne needed, unlike factorization_prod_pow_eq_self)
      = ∏ p ∈ range (2 * n + 1), p ^ (centralBinom n).factorization p :=
        (prod_pow_factorization_centralBinom n).symm
      -- Step 2: Non-prime p have (centralBinom n).factorization p = 0, so p^0 = 1
      -- Collapse to product over prime filter only
    _ = ∏ p ∈ (range (2 * n + 1)).filter Nat.Prime,
          p ^ (centralBinom n).factorization p := by
        apply (prod_filter_of_ne _).symm
        intro p _ hp
        by_contra h_nonprome
        simp [Nat.factorization_eq_zero_of_not_prime _ h_nonprome] at hp
      -- Step 3: Each p^{v_p(C(2n,n))} ≤ 2n by Legendre's formula (Mathlib: pow_factorization_choose_le)
    _ ≤ ∏ _p ∈ (range (2 * n + 1)).filter Nat.Prime, (2 * n) := by
        apply prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        have hmem := (mem_filter.mp hp).1
        rw [centralBinom_eq_two_mul_choose]
        exact pow_factorization_choose_le (by omega)
      -- Step 4: π(2n) copies of (2n) give (2n)^{π(2n)}
    _ = (2 * n) ^ ((range (2 * n + 1)).filter Nat.Prime).card := prod_const _
    _ = (2 * n) ^ primeCounting (2 * n) := by
        congr 1
        unfold primeCounting primeCounting'
        exact (count_eq_card_filter_range Nat.Prime (2 * n + 1)).symm

end ChebyshevPNTBridgeOQ01OQ02
