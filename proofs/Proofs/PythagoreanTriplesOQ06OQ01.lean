/-
  # Parity dichotomy and the mod-4 refinements for primitive Pythagorean triples
  # (pythagorean-triples-oq-06-oq-01)

  ## The Open Question

  Off the verified classification entry `pythagorean-triples-oq-06`, the seeker asked
  to "use the classification to prove exactly one leg is even." Mathlib already records
  the bare leg-parity dichotomy as `PythagoreanTriple.even_odd_of_coprime`
  (one leg is even and the other odd). This file restates that fact in the idiomatic
  `Even`/`Odd` form and then proves the three classical *refinements* that go strictly
  beyond it and are **not** in Mathlib:

  * **The hypotenuse is odd.** Pure parity: `z² = x² + y²` with one leg even and one
    odd forces `z²` — hence `z` — odd.
  * **The even leg is divisible by 4.** From the Euclid parametrization `y = 2mn` with
    `m, n` of opposite parity, one of `m, n` is even, so `2mn ≡ 0 (mod 4)`.
  * **The hypotenuse is `≡ 1 (mod 4)`.** From `z = m² + n²` with `m, n` of opposite
    parity, `m² + n² ≡ 0 + 1 (mod 4)`.

  The last two are the standard "next facts" after the parity dichotomy and are the
  genuine mathematical content here; the first is a short parity supplement. Everything
  is built on top of Mathlib's `even_odd_of_coprime` and `coprime_classification'`.

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

open PythagoreanTriple

namespace PythTriplesParity

/-- **Parity dichotomy (idiomatic form).** In a primitive Pythagorean triple exactly
    one leg is even and the other is odd. This is `even_odd_of_coprime` restated with
    the `Even`/`Odd` predicates instead of the raw `% 2` residues. -/
theorem one_leg_even {x y z : ℤ} (h : PythagoreanTriple x y z) (hco : Int.gcd x y = 1) :
    (Even x ∧ Odd y) ∨ (Odd x ∧ Even y) := by
  rcases h.even_odd_of_coprime hco with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨Int.even_iff.mpr hx, Int.odd_iff.mpr hy⟩
  · exact Or.inr ⟨Int.odd_iff.mpr hx, Int.even_iff.mpr hy⟩

/-- **The hypotenuse is odd.** Since one leg is even and the other odd, `x² + y²` is
    odd, so `z²` and therefore `z` are odd. Needs only the parity dichotomy, no
    parametrization. -/
theorem hyp_odd {x y z : ℤ} (h : PythagoreanTriple x y z) (hco : Int.gcd x y = 1) :
    z % 2 = 1 := by
  have heq : x * x + y * y = z * z := h
  have key : (z * z) % 2 = 1 := by
    rw [← heq]
    rcases h.even_odd_of_coprime hco with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      simp [Int.add_emod, Int.mul_emod, hx, hy]
  rcases Int.emod_two_eq_zero_or_one z with hz | hz
  · exfalso
    rw [Int.mul_emod, hz] at key
    simp at key
  · exact hz

/-- **The even leg is divisible by 4.** Taking the canonically oriented triple
    (`x` the odd leg, `z > 0`), the Euclid parametrization gives `y = 2mn` with `m, n`
    of opposite parity. One of `m, n` is even, so `y = 2mn` is a multiple of `4`. -/
theorem even_leg_div_four {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hz : 0 < z) :
    (4 : ℤ) ∣ y := by
  obtain ⟨m, n, _hx, hy, _hzeq, _hmn, hpar, _hm⟩ := h.coprime_classification' hco hodd hz
  subst hy
  rcases hpar with ⟨hme, _hno⟩ | ⟨_hmo, hne⟩
  · obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero hme
    exact ⟨k * n, by ring⟩
  · obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero hne
    exact ⟨m * k, by ring⟩

/-- **The hypotenuse is `≡ 1 (mod 4)`.** From `z = m² + n²` with `m, n` of opposite
    parity: the even square contributes `0` and the odd square contributes `1` modulo
    `4`, so `z ≡ 1 (mod 4)`. -/
theorem hyp_one_mod_four {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hz : 0 < z) :
    z % 4 = 1 := by
  obtain ⟨m, n, _hx, _hy, hzeq, _hmn, hpar, _hm⟩ := h.coprime_classification' hco hodd hz
  subst hzeq
  rcases hpar with ⟨hme, hno⟩ | ⟨hmo, hne⟩
  · -- m even, n odd
    obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero hme
    obtain ⟨b, rfl⟩ : ∃ b, n = 2 * b + 1 := ⟨n / 2, by omega⟩
    have : (2 * a) ^ 2 + (2 * b + 1) ^ 2 = 4 * (a ^ 2 + b ^ 2 + b) + 1 := by ring
    rw [this]; omega
  · -- m odd, n even
    obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero hne
    obtain ⟨b, rfl⟩ : ∃ b, m = 2 * b + 1 := ⟨m / 2, by omega⟩
    have : (2 * b + 1) ^ 2 + (2 * a) ^ 2 = 4 * (a ^ 2 + b ^ 2 + b) + 1 := by ring
    rw [this]; omega

/-- Concrete instance `(3, 4, 5)`: the even leg `4` is divisible by `4` and the
    hypotenuse `5 ≡ 1 (mod 4)`. -/
theorem example_3_4_5 :
    (4 : ℤ) ∣ 4 ∧ (5 : ℤ) % 4 = 1 := by
  refine ⟨⟨1, by norm_num⟩, by decide⟩

/-- Concrete instance `(8, 15, 17)` (odd leg `15`): even leg `8` divisible by `4`,
    hypotenuse `17 ≡ 1 (mod 4)`, obtained from the general theorems. -/
theorem example_8_15_17 :
    (4 : ℤ) ∣ 8 ∧ (17 : ℤ) % 4 = 1 := by
  have h : PythagoreanTriple 15 8 17 := by unfold PythagoreanTriple; norm_num
  have hco : Int.gcd 15 8 = 1 := by decide
  exact ⟨even_leg_div_four h hco (by decide) (by norm_num),
         hyp_one_mod_four h hco (by decide) (by norm_num)⟩

end PythTriplesParity

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `one_leg_even`       | Exactly one leg even (Even/Odd form of `even_odd_of_coprime`) |
  | `hyp_odd`            | The hypotenuse `z` is odd |
  | `even_leg_div_four`  | The even leg is divisible by 4 |
  | `hyp_one_mod_four`   | The hypotenuse `z ≡ 1 (mod 4)` |
  | `example_8_15_17`    | The two refinements instantiated at (15, 8, 17) |

  The leg dichotomy is Mathlib's `even_odd_of_coprime`; the three refinements
  (`hyp_odd`, `even_leg_div_four`, `hyp_one_mod_four`) are the new content and are not
  available in Mathlib. They rest on `coprime_classification'` (Euclid parametrization).

  **Sorries**: 0
  **Axioms**: 0
-/
