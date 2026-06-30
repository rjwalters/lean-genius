/-
  Element-Order Counts in a Group of Order p² — the Exact Order Distribution

  Follow-up open question OQ-01-OQ-03
  (parent: group-order-prime-squared-abelian-oq-01).

  The parent entry proves that a group `G` of order `p²` (`p` prime) is abelian and
  splits into two isomorphism types: cyclic (`≅ ℤ/p²`) or elementary abelian
  (`≅ (ℤ/p)²`). The sibling OQ-01-OQ-01 distinguishes the two through the single
  invariant `Monoid.exponent G` (value `p²` vs `p`).

  This follow-up computes the **exact number of elements of each order**, i.e. the
  full order distribution of the group — a strictly finer invariant than the exponent
  (which only records the *largest* order). For `|G| = p²` every element order lies in
  `{1, p, p²}` (parent trichotomy), and the counts are:

  | order | cyclic `ℤ/p²`        | elementary abelian `(ℤ/p)²` |
  |-------|----------------------|-----------------------------|
  | `1`   | `1`                  | `1`                         |
  | `p`   | `p − 1`  ( = φ(p) )   | `p² − 1`                    |
  | `p²`  | `p² − p` ( = φ(p²) )  | `0`                         |

  Both columns sum to `p²`, as they must. The order-`p` count alone (`p − 1` vs
  `p² − 1`) is therefore a **sharp discriminator** of the isomorphism type, parallel to
  the exponent invariant but counting fixed-order elements rather than reading off the
  exponent.

  ## Contents

  * `card_orderOf_eq_prime_of_isCyclic` — cyclic case: exactly `p − 1` elements of
    order `p` (Mathlib's `IsCyclic.card_orderOf_eq_totient` with `φ(p) = p − 1`).
  * `card_orderOf_eq_sq_of_isCyclic` — cyclic case: exactly `p² − p` elements of
    order `p²` (the generators, `φ(p²) = p(p−1)`).
  * `card_orderOf_eq_prime_of_not_isCyclic` — non-cyclic case: exactly `p² − 1`
    elements of order `p` (every non-identity element).
  * `card_orderOf_eq_sq_of_not_isCyclic` — non-cyclic case: `0` elements of order `p²`.
  * `card_orderOf_eq_prime_eq_iff_isCyclic` — the order-`p` count is a sharp invariant:
    it equals `p − 1` iff `G` is cyclic (else `p² − 1`).

  Everything is elementary finite group theory; no axioms, no sorries. The structural
  dichotomy is imported from the parent file, and the cyclic counts reduce to Mathlib's
  totient count for cyclic groups.
-/
import Mathlib
import Proofs.GroupOrderPrimeSquaredAbelian
import Proofs.GroupOrderPrimeSquaredAbelianExponentOQ01

namespace GroupOrderPrimeSqCounts

open GroupOrderPrimeSq GroupOrderPrimeSqExponent
open scoped Finset

variable {G : Type*} [Group G] [Fintype G]

/-- The ambient `Fintype.card` equals `p²` whenever `Nat.card G = p²`. -/
private theorem fintypeCard {p : ℕ} (hG : Nat.card G = p ^ 2) : Fintype.card G = p ^ 2 := by
  rw [← Nat.card_eq_fintype_card]; exact hG

/-! ## Cyclic case: the totient counts -/

/-- **Cyclic case, order `p`.** A cyclic group of order `p²` has exactly `p − 1`
elements of order `p`. By Mathlib's totient count for cyclic groups the number of
elements of order `p ∣ p²` is `φ(p)`, and `φ(p) = p − 1` for `p` prime. -/
theorem card_orderOf_eq_prime_of_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hc : IsCyclic G) : #{g : G | orderOf g = p} = p - 1 := by
  haveI : IsCyclic G := hc
  have hcard := fintypeCard hG
  have hdvd : p ∣ Fintype.card G := by rw [hcard]; exact dvd_pow_self p two_ne_zero
  rw [IsCyclic.card_orderOf_eq_totient hdvd, Nat.totient_prime hp]

/-- **Cyclic case, order `p²`.** A cyclic group of order `p²` has exactly `p² − p`
elements of order `p²` — these are the generators. The totient count gives
`φ(p²) = p^(2−1)·(p−1) = p·(p−1) = p² − p`. -/
theorem card_orderOf_eq_sq_of_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hc : IsCyclic G) : #{g : G | orderOf g = p ^ 2} = p ^ 2 - p := by
  haveI : IsCyclic G := hc
  have hcard := fintypeCard hG
  have hdvd : p ^ 2 ∣ Fintype.card G := by rw [hcard]
  rw [IsCyclic.card_orderOf_eq_totient hdvd, Nat.totient_prime_pow hp (by norm_num)]
  -- φ(p²) = p^(2-1)·(p-1) = p·(p-1) = p² − p
  have e1 : p ^ (2 - 1) = p := by norm_num
  rw [e1, mul_tsub, mul_one, ← pow_two]

/-! ## Non-cyclic (elementary abelian) case -/

/-- **Non-cyclic case, order `p`.** A non-cyclic group of order `p²` has exactly
`p² − 1` elements of order `p`: every non-identity element has order `p` (sibling
result `orderOf_eq_prime_of_not_isCyclic`), and the identity has order `1 ≠ p`. Thus the
order-`p` elements are precisely the `p² − 1` non-identity elements. -/
theorem card_orderOf_eq_prime_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) : #{g : G | orderOf g = p} = p ^ 2 - 1 := by
  classical
  have hcard := fintypeCard hG
  -- the order-p elements are exactly the non-identity elements
  have hset : ({g : G | orderOf g = p} : Finset G) = Finset.univ.erase (1 : G) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro h hg1
      subst hg1
      rw [orderOf_one] at h
      have := hp.one_lt
      omega
    · intro hg
      exact orderOf_eq_prime_of_not_isCyclic hp hG hnc hg
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, hcard]

/-- **Non-cyclic case, order `p²`.** A non-cyclic group of order `p²` has **no**
element of order `p²`: every order is `1` or `p`, never `p²` (otherwise the group would
be cyclic). -/
theorem card_orderOf_eq_sq_of_not_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) : #{g : G | orderOf g = p ^ 2} = 0 := by
  have hempty : ({g : G | orderOf g = p ^ 2} : Finset G) = (∅ : Finset G) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    rcases eq_or_ne g 1 with rfl | hg
    · rw [orderOf_one] at h
      have := hp.one_lt
      nlinarith [hp.two_le]
    · rw [orderOf_eq_prime_of_not_isCyclic hp hG hnc hg] at h
      nlinarith [hp.two_le]
  rw [hempty, Finset.card_empty]

/-! ## The order-`p` count is a sharp invariant -/

/-- **The number of order-`p` elements pins down the isomorphism type.** For a group of
order `p²`, the count of elements of order `p` equals `p − 1` *iff* `G` is cyclic
(`≅ ℤ/p²`); otherwise it equals `p² − 1` (`≅ (ℤ/p)²`). This mirrors the exponent
invariant of OQ-01-OQ-01 but uses a fixed-order *element count* as the discriminant. -/
theorem card_orderOf_eq_prime_eq_iff_isCyclic {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    #{g : G | orderOf g = p} = p - 1 ↔ IsCyclic G := by
  refine ⟨fun h => ?_, card_orderOf_eq_prime_of_isCyclic hp hG⟩
  by_contra hnc
  rw [card_orderOf_eq_prime_of_not_isCyclic hp hG hnc] at h
  -- p² − 1 = p − 1 forces p² = p, impossible for p ≥ 2 (omega handles the Nat subtraction
  -- once it knows 2 ≤ p and p < p²)
  have h2 : 2 ≤ p := hp.two_le
  have hlt : p < p ^ 2 := by nlinarith
  omega

end GroupOrderPrimeSqCounts
