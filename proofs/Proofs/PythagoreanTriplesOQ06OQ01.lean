/-
  # Parity dichotomy of primitive Pythagorean triples
  # (pythagorean-triples-oq-06-oq-01)

  ## The Open Question

  The parent entry `pythagorean-triples-oq-06` packages Euclid's classification of
  primitive Pythagorean triples. Its open question asks us to *use* the classification
  (or an elementary argument) to prove the **parity dichotomy**:

  > In a primitive Pythagorean triple `x² + y² = z²` with `gcd(x, y) = 1`, **exactly one
  > of the two legs `x, y` is even**, and the hypotenuse `z` is always odd.

  ## The argument (fully elementary — no classification needed)

  The dichotomy follows from two independent parity facts, each provable directly from
  the defining equation `x*x + y*y = z*z`:

  * **Not both even.** If `2 ∣ x` and `2 ∣ y` then `2 ∣ gcd(x, y) = 1`, impossible.
    (This is the only place coprimality is used.)
  * **Not both odd.** If `x, y` are both odd then `x² + y² ≡ 2 (mod 4)`. But a perfect
    square is `≡ 0` or `1 (mod 4)`, so `z²` can never be `≡ 2 (mod 4)`. Contradiction.
    (No coprimality needed — this holds for *every* Pythagorean triple.)

  Together: the two legs have opposite parity, so exactly one is even. The sum of an
  even square and an odd square is odd, hence `z²` is odd and `z` is odd.

  The mod-4 step is carried out by abstracting each square as an opaque integer and
  letting `omega` discharge the resulting linear contradiction (`4a + 1 = 4b + 2` etc.).

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace PythTriplesParity

/-- **Not both even.** In a primitive triple the two legs cannot both be even: that
    would force `2 ∣ gcd(x, y) = 1`. This is the only step that uses coprimality. -/
theorem not_both_even {x y z : ℤ} (_h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) : ¬ (Even x ∧ Even y) := by
  rintro ⟨hx, hy⟩
  have hg : (2 : ℕ) ∣ Int.gcd x y :=
    Nat.dvd_gcd (Int.natAbs_even.mpr hx).two_dvd (Int.natAbs_even.mpr hy).two_dvd
  omega

/-- **Not both odd.** No Pythagorean triple has two odd legs: `odd² + odd² ≡ 2 (mod 4)`,
    while every square is `≡ 0` or `1 (mod 4)`. Holds for *all* triples, primitive or
    not — coprimality is irrelevant here. -/
theorem not_both_odd {x y z : ℤ} (h : PythagoreanTriple x y z) :
    ¬ (Odd x ∧ Odd y) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have heq : x * x + y * y = z * z := h
  -- x² + y² = 4·(a²+a+b²+b) + 2 once x = 2a+1, y = 2b+1.
  have hsum : x * x + y * y = 4 * (a * a + a + b * b + b) + 2 := by subst ha hb; ring
  have hz2 : z * z = 4 * (a * a + a + b * b + b) + 2 := heq.symm.trans hsum
  rcases Int.even_or_odd z with ⟨c, hc⟩ | ⟨c, hc⟩
  · -- z = c + c : z² = 4·c², so 4c² = 4(…)+2, impossible mod 4.
    have hzc : z * z = 4 * (c * c) := by subst hc; ring
    omega
  · -- z = 2c + 1 : z² = 4·(c²+c)+1, so 4(c²+c)+1 = 4(…)+2, impossible mod 4.
    have hzc : z * z = 4 * (c * c + c) + 1 := by subst hc; ring
    omega

/-- **Parity dichotomy.** In a primitive Pythagorean triple, exactly one leg is even:
    either `x` is even and `y` is odd, or `x` is odd and `y` is even. -/
theorem parity_dichotomy {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) :
    (Even x ∧ Odd y) ∨ (Odd x ∧ Even y) := by
  rcases Int.even_or_odd x with hx | hx
  · rcases Int.even_or_odd y with hy | hy
    · exact absurd ⟨hx, hy⟩ (not_both_even h hco)
    · exact Or.inl ⟨hx, hy⟩
  · rcases Int.even_or_odd y with hy | hy
    · exact Or.inr ⟨hx, hy⟩
    · exact absurd ⟨hx, hy⟩ (not_both_odd h)

/-- **"Exactly one" as a biconditional.** A leg `x` is even iff the other leg `y` is
    odd. This is the sharpest packaging of the dichotomy. -/
theorem even_left_iff_odd_right {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) : Even x ↔ Odd y := by
  constructor
  · intro hx
    rcases parity_dichotomy h hco with ⟨_, hy⟩ | ⟨hx', _⟩
    · exact hy
    · exact absurd hx (by simpa [Int.not_even_iff_odd] using hx')
  · intro hy
    rcases parity_dichotomy h hco with ⟨hx, _⟩ | ⟨_, hy'⟩
    · exact hx
    · exact absurd hy (by simpa [Int.not_odd_iff_even] using hy')

/-- **The hypotenuse is odd.** Since the legs have opposite parity, `x² + y²` is
    `even + odd = odd`, hence `z²` and therefore `z` is odd. -/
theorem hypotenuse_odd {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) : Odd z := by
  have heq : x * x + y * y = z * z := h
  have hsq : Odd (x * x + y * y) := by
    rcases parity_dichotomy h hco with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact (hx.mul_right x).add_odd (hy.mul hy)
    · exact (hx.mul hx).add_even (hy.mul_right y)
  rw [heq] at hsq
  exact (Int.odd_mul.mp hsq).1

/-- The smallest primitive triple `(3, 4, 5)` realises the dichotomy: `3` is odd and
    `4` is even, and the hypotenuse `5` is odd. -/
theorem triple_3_4_5_parity :
    ((Even (3 : ℤ) ∧ Odd (4 : ℤ)) ∨ (Odd (3 : ℤ) ∧ Even (4 : ℤ))) ∧ Odd (5 : ℤ) :=
  ⟨parity_dichotomy (x := 3) (y := 4) (z := 5)
      (show (3 : ℤ) * 3 + 4 * 4 = 5 * 5 by norm_num) (by decide), by decide⟩

end PythTriplesParity

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `not_both_even`          | primitive ⟹ ¬(Even x ∧ Even y)  (uses gcd = 1) |
  | `not_both_odd`           | any triple ⟹ ¬(Odd x ∧ Odd y)   (mod-4 argument) |
  | `parity_dichotomy`       | primitive ⟹ exactly one leg even |
  | `even_left_iff_odd_right`| primitive ⟹ (Even x ↔ Odd y) |
  | `hypotenuse_odd`         | primitive ⟹ Odd z |
  | `triple_3_4_5_parity`    | (3, 4, 5): leg parity split + odd hypotenuse |

  The dichotomy is fully elementary: `not_both_odd` is a pure mod-4 fact about the
  Pythagorean equation, and `not_both_even` is the lone place coprimality enters. No
  appeal to the Euclid parametrization is required.
-/
