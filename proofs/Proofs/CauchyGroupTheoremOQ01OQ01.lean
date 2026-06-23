import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The odd-order boundary of Cauchy's theorem: squaring is a bijection

## What This Proves

The parent file `CauchyGroupTheoremOQ01` records Cauchy's theorem and its
*even-order* corollary: a finite group of even order contains an involution
(`exists_involution_of_even_card`, the `p = 2` case of Cauchy). This file proves
the complementary *odd-order* structure theory, the sharp boundary on the other
side of that dividing line. None of these statements are packaged in Mathlib.

* **Explicit square root** (`exists_sq_eq_of_odd_card`). In a finite group of
  odd order, every element `x` is a square: concretely `x = (x ^ (m+1)) ^ 2`
  where `|G| = 2m + 1`. The proof is the one-line identity
  `(x ^ (m+1)) ^ 2 = x ^ (|G| + 1) = x ^ |G| · x = x`, using
  `pow_card_eq_one`.

* **Squaring is a bijection** (`sq_surjective_of_odd_card`,
  `sq_bijective_of_odd_card`). The squaring map `x ↦ x²` is surjective, hence
  (the group being finite) bijective. This is the structural reason every
  element has a unique square root in an odd-order group, and the engine behind
  many parity-free arguments.

* **No involutions** (`no_involution_of_odd_card`). If `|G|` is odd then the
  only solution of `x² = 1` is `x = 1`: an order-`2` element would force
  `2 ∣ |G|`. This is the exact contrapositive of the parent's even-order
  involution corollary.

* **Sharp boundary** (`involution_iff_even_card`). Combining the new odd-order
  result with the Cauchy `p = 2` case gives the clean equivalence: a finite
  group contains a nontrivial element `x` with `x² = 1` **iff** its order is
  even. This pins down *exactly* when involutions exist, sharpening the parent's
  one-directional corollary into an iff.

* **Additive form** (`exists_two_nsmul_eq_of_odd_card`). The additive
  translation: in a finite additive group of odd order the doubling map
  `y ↦ 2 • y` is surjective — every element is a double.

* **Concrete instances** (`zmod3_double_surjective`, `zmod3_no_involution`,
  `zmod5_double_surjective`). In `ZMod 3` and `ZMod 5` (odd orders) doubling is
  surjective and the only self-inverse element is `0`, witnessed by kernel
  `decide` (no `native_decide`), keeping the file genuinely `0`-axiom.

## Context

Cauchy's theorem says `p ∣ |G|` produces an element of order `p`. The even
prime `p = 2` is the source of involutions; the odd-order world is precisely
where that source is switched off. The fact that squaring is then a bijection
(equivalently, that odd-order groups have unique square roots) is a standard
ingredient in the structure theory of finite groups — for instance in the
opening moves of the Feit–Thompson programme, where odd order is the standing
hypothesis.
-/

namespace CauchyGroupTheoremOQ01OQ01

variable {G : Type*}

/-! ### Squaring in odd-order groups -/

/-- **Explicit square root in an odd-order group.** If `|G|` is odd, every
element `x` is the square of `x ^ (m+1)` where `|G| = 2m + 1`. -/
theorem exists_sq_eq_of_odd_card [Group G] [Fintype G]
    (hodd : Odd (Fintype.card G)) (x : G) : ∃ y : G, y ^ 2 = x := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨x ^ (m + 1), ?_⟩
  rw [← pow_mul]
  have hk : (m + 1) * 2 = Fintype.card G + 1 := by omega
  rw [hk, pow_succ, pow_card_eq_one, one_mul]

/-- **Squaring is surjective** in a finite group of odd order. -/
theorem sq_surjective_of_odd_card [Group G] [Fintype G]
    (hodd : Odd (Fintype.card G)) : Function.Surjective (fun x : G => x ^ 2) :=
  fun x => exists_sq_eq_of_odd_card hodd x

/-- **Squaring is bijective** in a finite group of odd order: every element has a
unique square root. -/
theorem sq_bijective_of_odd_card [Group G] [Fintype G]
    (hodd : Odd (Fintype.card G)) : Function.Bijective (fun x : G => x ^ 2) :=
  ⟨(Finite.injective_iff_surjective).mpr (sq_surjective_of_odd_card hodd),
   sq_surjective_of_odd_card hodd⟩

/-! ### Absence of involutions -/

/-- **No involutions in an odd-order group.** If `|G|` is odd, the only solution
of `x ^ 2 = 1` is `x = 1`. This is the contrapositive of the parent's
even-order involution corollary. -/
theorem no_involution_of_odd_card [Group G] [Fintype G]
    (hodd : Odd (Fintype.card G)) {x : G} (hx : x ^ 2 = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcard : orderOf x ∣ Fintype.card G := orderOf_dvd_card
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h2] at hcard
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := hcard
    omega

/-- **Sharp boundary: involutions exist iff the order is even.** A finite group
contains a nontrivial self-inverse element iff its order is even. The forward
direction is the new odd-order result; the backward direction is the Cauchy
`p = 2` case. This upgrades the parent's one-directional even-order corollary to
an equivalence. -/
theorem involution_iff_even_card [Group G] [Fintype G] :
    (∃ x : G, x ≠ 1 ∧ x ^ 2 = 1) ↔ Even (Fintype.card G) := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    by_contra h
    exact hx1 (no_involution_of_odd_card (Nat.not_even_iff_odd.mp h) hx2)
  · intro heven
    obtain ⟨k, hk⟩ := heven
    have h2 : 2 ∣ Fintype.card G := ⟨k, by omega⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h2
    refine ⟨g, ?_, ?_⟩
    · intro hg1
      rw [hg1, orderOf_one] at hg
      exact absurd hg (by decide)
    · have h := pow_orderOf_eq_one g
      rwa [hg] at h

/-! ### Additive form -/

/-- **Doubling is surjective** in a finite additive group of odd order: every
element is a double, namely `x = 2 • ((m+1) • x)` where `|G| = 2m + 1`. -/
theorem exists_two_nsmul_eq_of_odd_card [AddGroup G] [Fintype G]
    (hodd : Odd (Fintype.card G)) (x : G) : ∃ y : G, 2 • y = x := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨(m + 1) • x, ?_⟩
  rw [two_nsmul, ← add_nsmul]
  have hk : (m + 1) + (m + 1) = Fintype.card G + 1 := by omega
  rw [hk, succ_nsmul, card_nsmul_eq_zero, zero_add]

/-! ### Concrete instances (kernel `decide`, no `native_decide`) -/

/-- In `ZMod 3` (odd order), doubling is surjective. -/
theorem zmod3_double_surjective : ∀ x : ZMod 3, ∃ y : ZMod 3, 2 • y = x := by decide

/-- In `ZMod 3` (odd order), the only self-inverse element is `0`. -/
theorem zmod3_no_involution : ∀ x : ZMod 3, x + x = 0 → x = 0 := by decide

/-- In `ZMod 5` (odd order), doubling is surjective. -/
theorem zmod5_double_surjective : ∀ x : ZMod 5, ∃ y : ZMod 5, 2 • y = x := by decide

end CauchyGroupTheoremOQ01OQ01
