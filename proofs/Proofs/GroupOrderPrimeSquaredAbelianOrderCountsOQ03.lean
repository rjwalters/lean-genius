/-
  Element-Order Counts in a Group of Order p² — a Sharp Combinatorial Invariant

  Follow-up open question OQ-01-OQ-03
  (parent: group-order-prime-squared-abelian-oq-01).

  The parent entry proves that a group `G` of order `p²` (`p` prime) is abelian and
  splits into two isomorphism types: `G` is cyclic (`≅ ℤ/p²`) **or** elementary abelian
  (`≅ (ℤ/p)²`, every element satisfies `gᵖ = 1`). The sibling OQ-01-OQ-01 shows the
  *exponent* discriminates the two types.

  This follow-up records the full **element-order spectrum** — for each possible order
  `1`, `p`, `p²` the exact number of elements of that order — and shows the spectrum is a
  *sharp* invariant separating the two types:

  | order | cyclic `ℤ/p²` | elementary abelian `(ℤ/p)²` |
  |-------|---------------|------------------------------|
  | `1`   | `1`           | `1`                          |
  | `p`   | `p − 1`       | `p² − 1`                     |
  | `p²`  | `p² − p`      | `0`                          |

  The order-`1` count is `1` in every group (only the identity). The cyclic counts are
  the Euler-totient values `φ(1), φ(p), φ(p²)` via Mathlib's
  `IsCyclic.card_orderOf_eq_totient`. The elementary-abelian counts are elementary: every
  non-identity element has order exactly `p`, and no element has order `p²`.

  The two spectra differ in the order-`p²` slot (`p² − p > 0` vs `0`), giving a clean
  combinatorial discriminator:

      0 < #{ g | orderOf g = p² }  ⟺  G is cyclic.

  Everything is elementary finite group theory; no axioms, no sorries. The structural
  dichotomy is imported from the parent file.
-/
import Mathlib
import Proofs.GroupOrderPrimeSquaredAbelian
import Proofs.GroupOrderPrimeSquaredAbelianExponentOQ01

namespace GroupOrderPrimeSqCounts

open GroupOrderPrimeSq GroupOrderPrimeSqExponent Finset

variable {G : Type*} [Group G] [Fintype G]

/-! ## A helper: `Nat.card` from `Fintype.card` -/

private theorem natCard_eq {p : ℕ} (hG : Fintype.card G = p ^ 2) : Nat.card G = p ^ 2 := by
  rw [Nat.card_eq_fintype_card]; exact hG

/-! ## The order-1 count (holds in every finite group) -/

/-- **Exactly one element of order `1`.** The only element of order `1` is the identity,
so the count is `1` regardless of the group. -/
theorem card_orderOf_eq_one_eq_one :
    #{g : G | orderOf g = 1} = 1 := by
  have hset : ({g : G | orderOf g = 1} : Finset G) = {1} := by
    ext g; simp [orderOf_eq_one_iff]
  rw [hset, Finset.card_singleton]

/-! ## Element-order counts in the elementary-abelian (non-cyclic) case -/

/-- **`p² − 1` elements of order `p` in the non-cyclic case.** Every non-identity element
of a non-cyclic group of order `p²` has order exactly `p` (`orderOf_eq_prime_of_not_isCyclic`),
and the identity has order `1 ≠ p`. So the elements of order `p` are exactly the `p² − 1`
non-identity elements. -/
theorem card_orderOf_eq_prime_of_not_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    #{g : G | orderOf g = p} = p ^ 2 - 1 := by
  classical
  have hN : Nat.card G = p ^ 2 := natCard_eq hG
  have hset : ({g : G | orderOf g = p} : Finset G) = Finset.univ.erase 1 := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro h hg1
      rw [hg1, orderOf_one] at h
      exact absurd h hp.one_lt.ne
    · intro hg1
      exact orderOf_eq_prime_of_not_isCyclic hp hN hnc hg1
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, hG]

/-- **No element of order `p²` in the non-cyclic case.** An element of order `p²` would
generate `G` (its order equals `Nat.card G = p²`), making `G` cyclic — contradiction. -/
theorem card_orderOf_eq_sq_of_not_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    #{g : G | orderOf g = p ^ 2} = 0 := by
  have hN : Nat.card G = p ^ 2 := natCard_eq hG
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hgsq
  exact hnc (isCyclic_of_orderOf_eq_card g (by rw [hgsq, hN]))

/-! ## Element-order counts in the cyclic case (Euler totient) -/

/-- **`p − 1` elements of order `p` in the cyclic case.** In a cyclic group the number of
elements of order `d ∣ |G|` is `φ(d)`; here `φ(p) = p − 1`. -/
theorem card_orderOf_eq_prime_of_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hc : IsCyclic G) :
    #{g : G | orderOf g = p} = p - 1 := by
  haveI : IsCyclic G := hc
  have hdvd : p ∣ Fintype.card G := by rw [hG]; exact dvd_pow_self p (by norm_num)
  rw [IsCyclic.card_orderOf_eq_totient hdvd, Nat.totient_prime hp]

/-- **`p² − p` elements of order `p²` in the cyclic case.** Here `φ(p²) = p·(p−1) = p² − p`. -/
theorem card_orderOf_eq_sq_of_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hc : IsCyclic G) :
    #{g : G | orderOf g = p ^ 2} = p ^ 2 - p := by
  haveI : IsCyclic G := hc
  have hdvd : p ^ 2 ∣ Fintype.card G := ⟨1, by rw [hG, mul_one]⟩
  rw [IsCyclic.card_orderOf_eq_totient hdvd, Nat.totient_prime_pow hp (by norm_num)]
  -- φ(p²) = p^(2-1) * (p-1) = p * (p-1) = p² - p
  have e1 : p ^ (2 - 1) = p := by norm_num
  rw [e1, Nat.mul_sub_left_distrib, mul_one, ← pow_two]

/-! ## The order spectrum is a sharp invariant for the dichotomy -/

/-- **The order-`p²` count detects cyclicity.** A group of order `p²` is cyclic *iff* it
has at least one element of order `p²`. This is the clean combinatorial discriminator
separating `ℤ/p²` (`p² − p > 0` elements of order `p²`) from `(ℤ/p)²` (none). -/
theorem card_orderOf_eq_sq_pos_iff_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) :
    0 < #{g : G | orderOf g = p ^ 2} ↔ IsCyclic G := by
  constructor
  · intro h
    by_contra hnc
    rw [card_orderOf_eq_sq_of_not_isCyclic hp hG hnc] at h
    exact (lt_irrefl 0) h
  · intro hc
    rw [card_orderOf_eq_sq_of_isCyclic hp hG hc]
    -- p² - p = p(p-1) > 0 since p ≥ 2
    have h2 : 2 ≤ p := hp.two_le
    have : p < p ^ 2 := by nlinarith
    omega

/-- **The full order spectrum in the cyclic case**: the counts of elements of order
`1`, `p`, `p²` are `1`, `p − 1`, `p² − p` respectively, and these sum to `p²`. -/
theorem orderSpectrum_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hc : IsCyclic G) :
    #{g : G | orderOf g = 1} = 1 ∧
    #{g : G | orderOf g = p} = p - 1 ∧
    #{g : G | orderOf g = p ^ 2} = p ^ 2 - p :=
  ⟨card_orderOf_eq_one_eq_one,
   card_orderOf_eq_prime_of_isCyclic hp hG hc,
   card_orderOf_eq_sq_of_isCyclic hp hG hc⟩

/-- **The full order spectrum in the elementary-abelian case**: the counts of elements of
order `1`, `p`, `p²` are `1`, `p² − 1`, `0` respectively. -/
theorem orderSpectrum_not_isCyclic {p : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ 2) (hnc : ¬ IsCyclic G) :
    #{g : G | orderOf g = 1} = 1 ∧
    #{g : G | orderOf g = p} = p ^ 2 - 1 ∧
    #{g : G | orderOf g = p ^ 2} = 0 :=
  ⟨card_orderOf_eq_one_eq_one,
   card_orderOf_eq_prime_of_not_isCyclic hp hG hnc,
   card_orderOf_eq_sq_of_not_isCyclic hp hG hnc⟩

end GroupOrderPrimeSqCounts
