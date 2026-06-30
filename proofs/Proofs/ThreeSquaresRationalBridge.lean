/-
Rational-solvability bridge for Legendre's three-square theorem.

`Proofs/ThreeSquares.lean` proves the **necessity** half of Legendre's theorem
(`excluded_form_not_sum_three_sq`: a number of the form `4^a(8b+7)` is never a
sum of three integer squares) with no axioms, and reduces **sufficiency** to a
single axiom `not_excluded_form_is_sum_three_sq`
(`¬IsExcludedForm n → ∃ a b c : ℤ, a²+b²+c² = n`).

`Proofs/ThreeSquaresDavenportCassels.lean` proves, axiom-free, the
**Davenport–Cassels descent** `exists_int_sq_of_rat_sq`:

  `(∃ x y z : ℚ, x²+y²+z² = n) → (∃ a b c : ℤ, a²+b²+c² = n)`,

i.e. for the form `x²+y²+z²`, rational representability *implies* integral
representability — the genuinely elementary half of the classical short proof.

This file connects the two. It isolates the entire remaining content of the
sufficiency direction into a single, sharply-stated analytic input — **three-
squares rational solvability** —

  `ThreeSquaresRationalSolvability :
     ∀ n, ¬IsExcludedForm n → ∃ x y z : ℚ, x²+y²+z² = n`,

and shows, with **no axioms** (taking that statement as an explicit hypothesis,
not an `axiom`), that it discharges the whole theorem:

  * `not_excluded_form_is_sum_three_sq_of_rat`  — sufficiency from rational
    solvability, via the proved Davenport–Cassels descent;
  * `legendre_three_squares_of_rat`            — the full Legendre `↔`,
    conditional only on rational solvability.

Why this is the right factoring.  By Davenport–Cassels, rational and integral
representability of `x²+y²+z²` are *equivalent* (the `←` direction is trivial:
integers are rationals). So the residual hypothesis
`ThreeSquaresRationalSolvability` is exactly as strong as the integral axiom it
replaces — but it is the form in which the real mathematics lives: rational
solvability of `x²+y²+z² = n` is the local–global (Hasse–Minkowski) statement,
provable from congruence conditions plus one existence-of-a-prime
(Dirichlet-in-AP) input, with **no lattice/Minkowski geometry required**. The
fiddly integral descent that the rest of the `ThreeSquares*` development spends
its effort on (the congruence-sublattice Minkowski step) is, by this route,
subsumed by the short Davenport–Cassels lemma already machine-checked here.

Net effect: the sufficiency direction is reduced to the single clean target
`ThreeSquaresRationalSolvability`, and everything downstream of it is verified
(0 sorries, 0 axioms in this file).
-/
import Proofs.ThreeSquares
import Proofs.ThreeSquaresDavenportCassels

namespace ThreeSquaresRationalBridge

open ThreeSquares

/-- **Three-squares rational solvability.**

Every `n` not of the excluded form `4^a(8b+7)` is a sum of three *rational*
squares. This is the sole remaining input for the sufficiency direction of
Legendre's three-square theorem; it is the local–global (Hasse–Minkowski)
statement for the ternary form `x²+y²+z²`. -/
def ThreeSquaresRationalSolvability : Prop :=
  ∀ n : ℕ, ¬ IsExcludedForm n → ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ)

/-- **Sufficiency from rational solvability.**

If every non-excluded `n` is a sum of three rational squares, then every
non-excluded `n` is a sum of three *integer* squares. The integral step is the
proved, axiom-free Davenport–Cassels descent
`ThreeSquaresDC.exists_int_sq_of_rat_sq`; this lemma adds no axioms of its own. -/
theorem not_excluded_form_is_sum_three_sq_of_rat
    (hRat : ThreeSquaresRationalSolvability) {n : ℕ} (h : ¬ IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ) := by
  -- Rational representability of `n` (target rephrased over `ℤ → ℚ` to match DC).
  have hq : ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = ((n : ℤ) : ℚ) := by
    obtain ⟨x, y, z, hxyz⟩ := hRat n h
    exact ⟨x, y, z, by push_cast at hxyz ⊢; exact hxyz⟩
  exact ThreeSquaresDC.exists_int_sq_of_rat_sq (n : ℤ) hq

/-- **Legendre's three-square theorem, conditional on rational solvability.**

`n` is a sum of three integer squares iff it is not of the form `4^a(8b+7)` —
assuming only `ThreeSquaresRationalSolvability`. The necessity (`→`) direction
is the unconditional, axiom-free `excluded_form_not_sum_three_sq`; the
sufficiency (`←`) direction is `not_excluded_form_is_sum_three_sq_of_rat`. No
axioms are used. -/
theorem legendre_three_squares_of_rat
    (hRat : ThreeSquaresRationalSolvability) (n : ℕ) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ)) ↔ ¬ IsExcludedForm n :=
  ⟨fun hsum hf => excluded_form_not_sum_three_sq hf hsum,
   not_excluded_form_is_sum_three_sq_of_rat hRat⟩

/-- The reverse Davenport–Cassels direction is immediate: integers are rationals.
Together with `not_excluded_form_is_sum_three_sq_of_rat` this records that
`ThreeSquaresRationalSolvability` is *equivalent* to integral sufficiency, i.e.
the factoring through rationals loses nothing. -/
theorem rat_sq_of_int_sq {n : ℤ} (h : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n) :
    ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ) := by
  obtain ⟨a, b, c, habc⟩ := h
  refine ⟨(a : ℚ), (b : ℚ), (c : ℚ), ?_⟩
  rw [← habc]; push_cast; ring

end ThreeSquaresRationalBridge
