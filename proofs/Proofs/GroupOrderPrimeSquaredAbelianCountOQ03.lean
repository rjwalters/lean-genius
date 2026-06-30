/-
  Element-Order Counts in a Group of Order p² — the Exact Census

  Follow-up open question OQ-01-OQ-03
  (parent: group-order-prime-squared-abelian-oq-01).

  The parent entry proves that a group `G` of order `p²` (`p` prime) is abelian and
  splits into exactly two isomorphism types via the structural dichotomy
  (`isCyclic_or_exponent_p`): `G` is cyclic (`≅ ℤ/p²`) **or** every element satisfies
  `gᵖ = 1` (elementary abelian, `≅ (ℤ/p)²`). The follow-up `…ExponentOQ01` distinguishes
  the two types by their exponent.

  This entry computes the *full element-order census*: for each possible order
  `1`, `p`, `p²` (the only orders that occur, by the parent's trichotomy), exactly how
  many elements of `G` have that order. The counts depend only on the isomorphism type:

  | order | cyclic `ℤ/p²`        | elementary abelian `(ℤ/p)²` |
  |-------|----------------------|------------------------------|
  | `1`   | `1`                  | `1`                          |
  | `p`   | `p − 1`              | `p² − 1`                     |
  | `p²`  | `p·(p − 1)` (`=φ(p²)`) | `0`                         |

  The cyclic column is read off Mathlib's `IsCyclic.card_orderOf_eq_totient`
  (number of elements of order `d` in a cyclic group is `φ(d)` for `d ∣ |G|`), via the
  totient values `φ(p) = p − 1` and `φ(p²) = p·(p − 1)`. The elementary-abelian column
  uses the parent's sharpening `orderOf_eq_prime_of_not_isCyclic`: every non-identity
  element has order *exactly* `p`, so the order-`p` elements are precisely the
  `p² − 1` non-identity elements and there are no elements of order `p²`.

  ## Contents

  * `card_orderOf_eq_one` — every finite group has exactly one element of order `1`.
  * `card_orderOf_eq_prime_of_isCyclic` — cyclic case: `p − 1` elements of order `p`.
  * `card_orderOf_eq_sq_of_isCyclic` — cyclic case: `p·(p − 1)` elements of order `p²`.
  * `card_orderOf_eq_prime_of_not_isCyclic` — elementary-abelian case: `p² − 1`
    elements of order `p`.
  * `card_orderOf_eq_sq_of_not_isCyclic` — elementary-abelian case: no elements of
    order `p²`.
  * `isCyclic_iff_card_orderOf_eq_prime` — the census is sharp: the number of order-`p`
    elements *alone* decides the isomorphism type (`p − 1` ⟺ cyclic).

  Everything is elementary finite group theory; no axioms, no sorries. The structural
  results are imported from the parent files.
-/
import Mathlib
import Proofs.GroupOrderPrimeSquaredAbelian
import Proofs.GroupOrderPrimeSquaredAbelianExponentOQ01

namespace GroupOrderPrimeSqCount

open GroupOrderPrimeSq GroupOrderPrimeSqExponent Finset

variable {G : Type*} [Group G] [Fintype G]

/-! ## The identity is the unique element of order 1 -/

/-- **Exactly one element of order `1`.** In any finite group the only element of
order `1` is the identity (`orderOf g = 1 ↔ g = 1`), so the count is `1`. This is the
trivial column of the census and holds with no cardinality hypothesis. -/
theorem card_orderOf_eq_one : #{g : G | orderOf g = 1} = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext g
  simp only [mem_filter, mem_univ, true_and, mem_singleton, orderOf_eq_one_iff]

/-! ## Cyclic case: G ≅ ℤ/p² -/

/-- **Cyclic case — `p − 1` elements of order `p`.** In a cyclic group of order `p²`
the number of elements of order `p` is `φ(p) = p − 1`, by
`IsCyclic.card_orderOf_eq_totient` (`p ∣ p² = |G|`) and `Nat.totient_prime`. -/
theorem card_orderOf_eq_prime_of_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hc : IsCyclic G) :
    #{g : G | orderOf g = p} = p - 1 := by
  haveI := hc
  have hd : p ∣ Fintype.card G := by rw [hG]; exact dvd_pow_self p (by norm_num)
  rw [IsCyclic.card_orderOf_eq_totient hd, Nat.totient_prime hp]

/-- **Cyclic case — `p·(p − 1)` elements of order `p²`.** These are exactly the
generators of `G ≅ ℤ/p²`; their number is `φ(p²) = p·(p − 1)`, by
`IsCyclic.card_orderOf_eq_totient` (`p² ∣ |G|`) and `Nat.totient_prime_pow`. -/
theorem card_orderOf_eq_sq_of_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hc : IsCyclic G) :
    #{g : G | orderOf g = p ^ 2} = p * (p - 1) := by
  haveI := hc
  have hd : p ^ 2 ∣ Fintype.card G := by rw [hG]
  rw [IsCyclic.card_orderOf_eq_totient hd, Nat.totient_prime_pow hp (by norm_num : 0 < 2),
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]

/-! ## Elementary-abelian case: G ≅ (ℤ/p)² -/

/-- **Elementary-abelian case — `p² − 1` elements of order `p`.** When `G` is not
cyclic, every non-identity element has order exactly `p`
(`orderOf_eq_prime_of_not_isCyclic`), so the order-`p` elements are precisely the
`|G| − 1 = p² − 1` elements other than the identity. -/
theorem card_orderOf_eq_prime_of_not_isCyclic [DecidableEq G] {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    #{g : G | orderOf g = p} = p ^ 2 - 1 := by
  have hNat : Nat.card G = p ^ 2 := by rw [Nat.card_eq_fintype_card, hG]
  have hcard : #{g : G | orderOf g = p} = (univ.erase (1 : G)).card := by
    apply congrArg Finset.card
    ext g
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    constructor
    · intro h hg1
      subst hg1
      rw [orderOf_one] at h
      exact hp.ne_one h.symm
    · intro hg
      exact orderOf_eq_prime_of_not_isCyclic hp hNat hnc hg
  rw [hcard, card_erase_of_mem (mem_univ (1 : G)), card_univ, hG]

/-- **Elementary-abelian case — no elements of order `p²`.** When `G` is not cyclic,
`gᵖ = 1` for every `g` (`pow_prime_eq_one_of_not_isCyclic`), so `orderOf g ∣ p ≤ p`,
which is `< p²`; hence no element has order `p²`. -/
theorem card_orderOf_eq_sq_of_not_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    #{g : G | orderOf g = p ^ 2} = 0 := by
  have hNat : Nat.card G = p ^ 2 := by rw [Nat.card_eq_fintype_card, hG]
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro g hg
  rw [mem_filter] at hg
  have h : orderOf g = p ^ 2 := hg.2
  have hp1 : g ^ p = 1 := pow_prime_eq_one_of_not_isCyclic hp hNat hnc g
  have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_iff_pow_eq_one.mpr hp1)
  rw [h] at hle
  nlinarith [hp.two_le, hle]

/-! ## The census is a sharp invariant -/

/-- **The order-`p` count decides the isomorphism type.** For a group of order `p²`,
`G` is cyclic *iff* it has exactly `p − 1` elements of order `p`. The forward direction
is the cyclic count; conversely, a non-cyclic group has `p² − 1 ≠ p − 1` elements of
order `p` (since `p² ≠ p` for a prime `p`), so the count `p − 1` forces cyclicity. -/
theorem isCyclic_iff_card_orderOf_eq_prime [DecidableEq G] {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) :
    IsCyclic G ↔ #{g : G | orderOf g = p} = p - 1 := by
  refine ⟨card_orderOf_eq_prime_of_isCyclic hp hG, fun h => ?_⟩
  by_contra hnc
  rw [card_orderOf_eq_prime_of_not_isCyclic hp hG hnc] at h
  have h2 : 2 ≤ p := hp.two_le
  have hpp : p ^ 2 = p := by omega
  nlinarith [h2, hpp]

end GroupOrderPrimeSqCount
