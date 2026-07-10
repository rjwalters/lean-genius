import Mathlib
import Proofs.ETranscendentalOQ02

/-!
# Is e a Normal Number? (OQ-02-OQ-06) — the negative class: which numbers are *not* absolutely normal

The parent file `ETranscendentalOQ02.lean` develops normality and the absolute-level
consequences of normality (`absolutely_normal_imp_irrational`,
`absolutely_normal_imp_disjunctive`), and — on the *sharpness* side — exhibits explicit
**irrational** numbers that are not normal (the Liouville constant,
`exists_irrational_not_normal_of_two_le`).

This companion records the complementary **negative class** that the parent never names:
the numbers that fail to be absolutely normal for the *cheap* reason of being rational.
Since absolute normality forces irrationality (`absolutely_normal_imp_irrational`), its
contrapositive rules out every non-irrational real at once:

* `not_absolutely_normal_of_not_irrational` — a real that is *not* irrational is not
  absolutely normal (abstract contrapositive of `absolutely_normal_imp_irrational`).
* `rat_not_absolutely_normal` — **no rational number is absolutely normal**.
* `int_not_absolutely_normal` — in particular no integer is absolutely normal.

Together with the parent's Liouville examples this completes the picture behind
"irrationality is *necessary but not sufficient* for normality": the non-normal reals
include the *whole* class of rationals (this file) *and* some irrationals (the parent's
Liouville constant).  All results are unconditional — they do **not** invoke the open
`e_absolutely_normal` axiom.

0 axioms, 0 sorries on top of Mathlib and the parent file.
-/

open Real Filter

namespace ETranscendentalOQ02

/-- **Contrapositive of `absolutely_normal_imp_irrational`.**  A real number that is not
irrational cannot be absolutely normal: absolute normality would force irrationality. -/
theorem not_absolutely_normal_of_not_irrational (x : ℝ) (hx : ¬ Irrational x) :
    ¬ IsAbsolutelyNormal x :=
  fun h => hx (absolutely_normal_imp_irrational x h)

/-- **No rational number is absolutely normal.**  A rational's base-`b` expansion is
eventually periodic in every base, so it is normal in none; equivalently, it is not
irrational and hence not absolutely normal.  This is a whole class of non-normal reals,
complementing the parent file's explicit *irrational* non-normal examples. -/
theorem rat_not_absolutely_normal (q : ℚ) : ¬ IsAbsolutelyNormal (q : ℝ) :=
  not_absolutely_normal_of_not_irrational _ (Rat.not_irrational q)

/-- **No integer is absolutely normal.**  The integer instance of
`rat_not_absolutely_normal`. -/
theorem int_not_absolutely_normal (m : ℤ) : ¬ IsAbsolutelyNormal (m : ℝ) :=
  not_absolutely_normal_of_not_irrational _ (Int.not_irrational m)

end ETranscendentalOQ02
