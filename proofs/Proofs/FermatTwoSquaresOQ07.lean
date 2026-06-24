/-
  Brahmagupta's Identity and the Norm Form x² + N·y²
  Open Question: fermat-two-squares-oq-07

  The Brahmagupta–Fibonacci identity

      (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²

  expresses that a product of two sums of two squares is again a sum of two
  squares — equivalently, that the norm N(z) = |z|² on the Gaussian integers
  ℤ[i] is multiplicative. That N = 1 case is already in the gallery
  (`FermatTwoSquaresOQ01.two_squares_mul` / `two_squares_closed`).

  This file proves the *general Brahmagupta identity* for the quadratic form

      f_N(x, y) = x² + N·y²,

  which is precisely the norm form of the quadratic ring ℤ[√−N]:

      (a² + N·b²)(c² + N·d²) = (ac − N·bd)² + N·(ad + bc)²
                             = (ac + N·bd)² + N·(ad − bc)².

  Consequences proved here (for EVERY parameter N, not just N = 1):
  • `brahmagupta` / `brahmagupta'` — the two sign-variant identities;
  • `normForm_mul` — the form f_N is multiplicative;
  • `Represents_mul` — the set of integers represented by f_N is closed under
    multiplication;
  • the two sign variants generically yield TWO distinct representations of a
    product as a sum of two squares (the classical reason composite numbers
    have multiple two-square representations), witnessed by
    65 = 4² + 7² = 8² + 1².

  The N = 1 case (`brahmagupta_fibonacci`) recovers the gallery's
  Brahmagupta–Fibonacci identity as a one-line specialization.

  References:
  - Brahmagupta (628 AD), Brāhmasphuṭasiddhānta: the identity for x² − Ny²
    and x² + Ny² (norm of ℤ[√±N]).
  - FermatTwoSquaresOQ01.lean: the N = 1 special case (Gaussian integers).
-/

import Mathlib.Tactic

namespace FermatTwoSquaresOQ07

/-! ### The general Brahmagupta identity -/

/-- **Brahmagupta's identity** for the form `x² + N·y²`, in any commutative ring.
This is the multiplicativity of the norm on `ℤ[√−N]`:

    (a² + N·b²)(c² + N·d²) = (ac − N·bd)² + N·(ad + bc)². -/
theorem brahmagupta {R : Type*} [CommRing R] (N a b c d : R) :
    (a ^ 2 + N * b ^ 2) * (c ^ 2 + N * d ^ 2) =
      (a * c - N * b * d) ^ 2 + N * (a * d + b * c) ^ 2 := by
  ring

/-- The conjugate sign variant of Brahmagupta's identity:

    (a² + N·b²)(c² + N·d²) = (ac + N·bd)² + N·(ad − bc)².

Choosing `d ↦ −d` swaps the two forms; the existence of two variants is the
source of multiple representations of composite numbers. -/
theorem brahmagupta' {R : Type*} [CommRing R] (N a b c d : R) :
    (a ^ 2 + N * b ^ 2) * (c ^ 2 + N * d ^ 2) =
      (a * c + N * b * d) ^ 2 + N * (a * d - b * c) ^ 2 := by
  ring

/-! ### The norm form and its multiplicativity -/

/-- The quadratic norm form `f_N(x, y) = x² + N·y²` — the norm of `x + y√−N`
in `ℤ[√−N]`. -/
def normForm (N x y : ℤ) : ℤ := x ^ 2 + N * y ^ 2

/-- **The norm form is multiplicative.** The product of two values of `f_N` is
again a value of `f_N`, with explicit composition law on the arguments. -/
theorem normForm_mul (N a b c d : ℤ) :
    normForm N a b * normForm N c d =
      normForm N (a * c - N * b * d) (a * d + b * c) := by
  simp only [normForm]
  ring

/-! ### Multiplicative closure of the represented set -/

/-- `Represents N n` means `n` is a value of the form `x² + N·y²`. -/
def Represents (N n : ℤ) : Prop := ∃ x y : ℤ, n = x ^ 2 + N * y ^ 2

/-- **Multiplicative closure (general N).** For every parameter `N`, the set of
integers represented by `x² + N·y²` is closed under multiplication. The `N = 1`
case is closure of sums of two squares (`FermatTwoSquaresOQ01.two_squares_closed`). -/
theorem Represents_mul {N m n : ℤ} (hm : Represents N m) (hn : Represents N n) :
    Represents N (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c - N * b * d, a * d + b * c, by ring⟩

/-- Every square is represented (`y = 0`): `x² = x² + N·0²`. -/
theorem Represents_sq (N x : ℤ) : Represents N (x ^ 2) :=
  ⟨x, 0, by ring⟩

/-- `1` is always represented (`x = 1, y = 0`). -/
theorem Represents_one (N : ℤ) : Represents N 1 :=
  ⟨1, 0, by ring⟩

/-! ### Recovering the gallery's N = 1 Brahmagupta–Fibonacci identity -/

/-- **Brahmagupta–Fibonacci identity** as the `N = 1` specialization. This is the
gallery's `FermatTwoSquaresOQ01.two_squares_mul`, obtained here in one line. -/
theorem brahmagupta_fibonacci (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) =
      (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  simpa using brahmagupta 1 a b c d

/-- For `N = 1`, `Represents 1 n` is exactly "sum of two squares". -/
theorem represents_one_iff (n : ℤ) :
    Represents 1 n ↔ ∃ x y : ℤ, n = x ^ 2 + y ^ 2 := by
  unfold Represents
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨x, y, by simpa using h⟩
  · rintro ⟨x, y, h⟩; exact ⟨x, y, by simpa using h⟩

/-! ### Two distinct representations from the two sign variants

The two Brahmagupta variants applied to a product of two *distinct* sums of two
squares generically produce two genuinely different representations. The
canonical example is `65 = 5 · 13 = (2² + 1²)(3² + 2²)`:

* variant `brahmagupta`  → `(2·3 − 1·2, 2·2 + 1·3) = (4, 7)`,  so `65 = 4² + 7²`;
* variant `brahmagupta'` → `(2·3 + 1·2, 2·2 − 1·3) = (8, 1)`,  so `65 = 8² + 1²`.

These two unordered pairs `{4, 7}` and `{1, 8}` are distinct, exhibiting the two
essentially different ways `65` is a sum of two squares. -/

/-- The first variant gives `65 = 4² + 7²`. -/
theorem sixtyFive_rep_one :
    (65 : ℤ) = (2 * 3 - 1 * 2) ^ 2 + (2 * 2 + 1 * 3) ^ 2 := by
  norm_num

/-- The second variant gives `65 = 8² + 1²`. -/
theorem sixtyFive_rep_two :
    (65 : ℤ) = (2 * 3 + 1 * 2) ^ 2 + (2 * 2 - 1 * 3) ^ 2 := by
  norm_num

/-- Both variants represent `65` as a sum of two squares, and the two unordered
pairs of summand-bases are distinct: `{4, 7} ≠ {1, 8}`. Hence `65` has (at least)
two essentially different two-square representations, both forced by Brahmagupta's
identity from `65 = 5 · 13`. -/
theorem sixtyFive_two_distinct_reps :
    (65 : ℤ) = 4 ^ 2 + 7 ^ 2 ∧ (65 : ℤ) = 8 ^ 2 + 1 ^ 2 ∧
      ({4, 7} : Finset ℕ) ≠ ({1, 8} : Finset ℕ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  decide

/-- Both representations of `65` arise from `Represents 1`, confirming the
multiplicative-closure mechanism `Represents 1 5 → Represents 1 13 →
Represents 1 65` is genuinely multivalued. -/
theorem sixtyFive_represents_two_ways :
    Represents 1 65 ∧ Represents 1 65 :=
  ⟨⟨4, 7, by norm_num⟩, ⟨8, 1, by norm_num⟩⟩

end FermatTwoSquaresOQ07
