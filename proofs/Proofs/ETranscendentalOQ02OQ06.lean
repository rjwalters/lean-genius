import Mathlib.Tactic
import Proofs.ETranscendentalOQ02

/-
# The contrapositive of `normal_imp_irrational`: rationals are never normal

## Context

The parent entry `ETranscendentalOQ02` ("Is e a Normal Number?") proves the
positive implication

  `normal_imp_irrational : IsNormalInBase b x → Irrational x`   (base `b ≥ 2`),

using that a rational's base-`b` expansion is eventually periodic and hence has a
missing digit block, so some block frequency tends to `0` rather than to the
positive normal value `b^(-k)`.

The open-question child `e-transcendental-oq-02-oq-06` asks to package the
*contrapositive* as a reusable standalone lemma:

  `x ∈ ℚ  ⇒  ¬ IsNormalInBase b x`.

That is exactly what a downstream user needs to rule out normality of a concrete
number once it is known to be rational. This file records the contrapositive and
its immediate specializations (rational / integer / natural casts, and the
absolute-normality level), each obtained from `normal_imp_irrational` and the
Mathlib facts `Rat.not_irrational` / `Int.not_irrational` / `Nat.not_irrational`.

None of these introduce assumptions: they are corollaries of a theorem already
machine-checked in the parent file. The only `axiom` in the parent
(`e_absolutely_normal`, the genuinely open conjecture that `e` is normal) is not
used here.

## Results

- `rational_not_normal`      : `¬ IsNormalInBase b (q : ℝ)` for `q : ℚ`.
- `intCast_not_normal`       : `¬ IsNormalInBase b (n : ℝ)` for `n : ℤ`.
- `natCast_not_normal`       : `¬ IsNormalInBase b (n : ℝ)` for `n : ℕ`.
- `normal_ne_ratCast`        : a normal number differs from every rational.
- `rational_not_absolutely_normal` : `¬ IsAbsolutelyNormal (q : ℝ)`.
-/

open ETranscendentalOQ02

namespace ETranscendentalOQ02OQ06

/-- **Rationals are never normal (the contrapositive of `normal_imp_irrational`).**
    If `q : ℚ`, then `(q : ℝ)` is not normal in any base `b ≥ 2`: normality would
    force irrationality by `normal_imp_irrational`, contradicting
    `Rat.not_irrational`. This is the standalone contrapositive requested by the
    `e-transcendental-oq-02-oq-06` open question. -/
theorem rational_not_normal (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ¬ IsNormalInBase b (q : ℝ) :=
  fun hn => q.not_irrational (normal_imp_irrational b hb (q : ℝ) hn)

/-- **Integers are never normal.**  Specialization of `rational_not_normal` to
    integer casts, via `Int.not_irrational`. -/
theorem intCast_not_normal (b : ℕ) (hb : 2 ≤ b) (n : ℤ) :
    ¬ IsNormalInBase b (n : ℝ) :=
  fun hn => (Int.not_irrational n) (normal_imp_irrational b hb (n : ℝ) hn)

/-- **Naturals are never normal.**  Specialization of `rational_not_normal` to
    natural-number casts, via `Nat.not_irrational`. -/
theorem natCast_not_normal (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ¬ IsNormalInBase b (n : ℝ) :=
  fun hn => (Nat.not_irrational n) (normal_imp_irrational b hb (n : ℝ) hn)

/-- **A normal number is distinct from every rational.**  The pointwise form of
    the contrapositive: if `x` is normal in base `b ≥ 2`, then `x ≠ (q : ℝ)` for
    every `q : ℚ`. Immediate from `rational_not_normal` (substituting a purported
    equality would make a rational normal). -/
theorem normal_ne_ratCast (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormalInBase b x)
    (q : ℚ) : x ≠ (q : ℝ) := by
  rintro rfl
  exact rational_not_normal b hb q hx

/-- **Rationals are not absolutely normal.**  A rational cannot be normal in even
    a single base, so in particular it is not normal in *every* base. Uses
    `IsAbsolutelyNormal` at the concrete base `2`. -/
theorem rational_not_absolutely_normal (q : ℚ) :
    ¬ IsAbsolutelyNormal (q : ℝ) :=
  fun hn => rational_not_normal 2 (le_refl 2) q (hn 2 (le_refl 2))

end ETranscendentalOQ02OQ06
