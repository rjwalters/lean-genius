import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Factors
import Mathlib.Tactic
import Proofs.FactorRemainderTheoremOQ01OQ02

/-
# Factor–remainder theorem OQ-01-OQ-02-OQ-01: separability is "no repeated linear factor"

The parent entry (`factor-remainder-theorem-oq-01-oq-02`,
`FactorRemainderTheoremOQ01OQ02`) proves the **Hasse multiplicity factor theorem** in every
characteristic:

  `(X − a)ᵏ ∣ p ↔ ∀ m < k, (hasseDeriv m p)(a) = 0`,

together with its `k = 2` instance `double_root_iff`

  `(X − a)² ∣ p ↔ p(a) = 0 ∧ p′(a) = 0`,

stated with the *ordinary* derivative `p′ = hasseDeriv 1 p` and valid over **any commutative
ring with no `p ≠ 0` hypothesis**.

This leaf connects that divisibility criterion to **separability**.  Recall Mathlib defines

  `Polynomial.Separable p  :↔  IsCoprime p (derivative p)`,

so separability is phrased through the *ordinary* derivative.  A natural worry raised by the
parent's `hasseDeriv_detects_char_p` (where the ordinary derivative of `X²` is identically `0`
in characteristic `2`) is whether the ordinary-derivative criterion still detects repeated
roots in positive characteristic.  It does: squarefreeness is a *multiplicity-≤-1* condition,
and the parent shows that **double roots are detected by the ordinary derivative in every
characteristic** (the divided-power correction is only needed at multiplicities `≥ p`).  So
the separability criterion is characteristic-robust for "no repeated root", and we make the
link explicit and computable.

## Main results

* `sq_dvd_iff_eval_derivative` : the parent's `double_root_iff`, re-exported as the
  characteristic-free repeated-root criterion `(X − a)² ∣ p ↔ p(a) = 0 ∧ p′(a) = 0`.
* `Separable.not_sq_dvd` : a separable polynomial over any nontrivial commutative ring has
  **no repeated linear factor** — `¬ (X − a)² ∣ p` for every `a`.  Coprimality forces any
  common divisor of `p` and `p′` to be a unit, but `X − a` is never a unit.
* `sq_dvd_iff_one_lt_rootMultiplicity` / `roots_nodup_iff_forall_not_sq_dvd` : over a field,
  `(X − a)²` divides `p` iff `a` is a multiple root, and `p` has distinct roots iff no
  `(X − a)²` divides `p`.
* `separable_iff_forall_not_sq_dvd` : the **headline** elementary criterion — for a nonzero
  polynomial that *splits* over a field `F`,

    `p.Separable ↔ ∀ a, ¬ (X − a)² ∣ p`,

  i.e. separability is exactly the absence of a repeated linear factor.
* `separable_X_sq_add_X_zmod_two` / `not_separable_X_sq_zmod_two` : explicit characteristic-`2`
  witnesses — `X² + X` is separable (derivative `= 1`) while `X²` is not (derivative `= 0`),
  showing the ordinary-derivative criterion behaves correctly even where the parent's
  `hasseDeriv_detects_char_p` flags the ordinary derivative as "blind" at higher multiplicity.

Mathlib already proves `rootMultiplicity_le_one_of_separable`, `nodup_roots`, and
`nodup_roots_iff_of_splits`; the new content here is the **explicit `(X − a)²`-divisibility
characterization** of separability — derived through the parent's characteristic-free
`double_root_iff` rather than through `rootMultiplicity` — and the positive-characteristic
witnesses that close the loop with the parent's char-`p` analysis.
-/

namespace FactorRemainderTheoremOQ01OQ02OQ01

open Polynomial

variable {R : Type*}

/-- **Repeated linear factor via the ordinary derivative (all characteristics).**
`(X − a)²` divides `p` iff `p` and its ordinary derivative both vanish at `a`.  This is the
`k = 2` case of the parent's Hasse multiplicity factor theorem; the *ordinary* derivative
suffices here because `hasseDeriv 1 = derivative`, so — unlike higher multiplicities — double
roots need no divided-power correction even in positive characteristic, and there is no
`p ≠ 0` hypothesis. -/
theorem sq_dvd_iff_eval_derivative [CommRing R] {a : R} (p : R[X]) :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ (derivative p).eval a = 0 :=
  FactorRemainderTheoremOQ01OQ02.double_root_iff p

/-- **Separable polynomials have no repeated linear factor — in every characteristic.**
If `p` is separable (coprime to its ordinary derivative) then no square `(X − a)²` divides
`p`.  Any common divisor of `p` and `p′` is forced to be a unit by coprimality, but `X − a`
is never a unit. -/
theorem Separable.not_sq_dvd [CommRing R] [Nontrivial R] {p : R[X]}
    (hsep : p.Separable) (a : R) : ¬ (X - C a) ^ 2 ∣ p := by
  rw [sq_dvd_iff_eval_derivative]
  rintro ⟨h0, h1⟩
  have hp : (X - C a) ∣ p := (FactorRemainderTheoremOQ01OQ02.factor_theorem p).mpr h0
  have hp' : (X - C a) ∣ derivative p :=
    (FactorRemainderTheoremOQ01OQ02.factor_theorem (derivative p)).mpr h1
  exact not_isUnit_X_sub_C a (IsCoprime.isUnit_of_dvd' hsep hp hp')

section Field

variable {F : Type*} [Field F]

/-- Over a field, `(X − a)²` divides a nonzero `p` iff `a` is a multiple root of `p`. -/
theorem sq_dvd_iff_one_lt_rootMultiplicity {p : F[X]} (hp : p ≠ 0) (a : F) :
    (X - C a) ^ 2 ∣ p ↔ 1 < rootMultiplicity a p := by
  rw [sq_dvd_iff_eval_derivative, one_lt_rootMultiplicity_iff_isRoot hp]
  simp only [IsRoot.def]

/-- Over a field, a nonzero `p` has all distinct roots iff no `(X − a)²` divides it. -/
theorem roots_nodup_iff_forall_not_sq_dvd {p : F[X]} (hp : p ≠ 0) :
    p.roots.Nodup ↔ ∀ a, ¬ (X - C a) ^ 2 ∣ p := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  refine forall_congr' (fun a => ?_)
  rw [count_roots, sq_dvd_iff_one_lt_rootMultiplicity hp, not_lt]

/-- **Separability is the absence of a repeated linear factor.**  For a nonzero polynomial
that splits over a field `F`,

  `p.Separable ↔ ∀ a, ¬ (X − a)² ∣ p`,

the elementary classical criterion.  The forward direction (`Separable.not_sq_dvd`) holds in
every characteristic and any extension; the converse uses that `p` splits, so every repeated
root is realised by a linear factor `(X − a)²` over `F` itself. -/
theorem separable_iff_forall_not_sq_dvd {p : F[X]} (hp : p ≠ 0) (hsplit : p.Splits) :
    p.Separable ↔ ∀ a, ¬ (X - C a) ^ 2 ∣ p := by
  rw [← nodup_roots_iff_of_splits hp hsplit, roots_nodup_iff_forall_not_sq_dvd hp]

end Field

section CharacteristicTwo

/-- In characteristic `2`, `X² + X = X(X + 1)` is **separable**: its ordinary derivative is the
constant `1` (the `2·X` term vanishes), which is coprime to everything.  Built from the
*ordinary* derivative, the separability criterion correctly certifies the two distinct roots
`0, 1` even though `char = 2`. -/
theorem separable_X_sq_add_X_zmod_two :
    (X ^ 2 + X : (ZMod 2)[X]).Separable := by
  have hd : derivative (X ^ 2 + X : (ZMod 2)[X]) = 1 := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [derivative_add, derivative_X_pow, derivative_X, h2, map_zero, zero_mul, zero_add]
  rw [Separable, hd]
  exact isCoprime_one_right

/-- In characteristic `2`, `X²` is **not separable**: it has the double root `0`, and its
ordinary derivative `2·X = 0` is not coprime to `X²`.  This is the separability shadow of the
parent's `hasseDeriv_detects_char_p`: the ordinary derivative detects double roots in every
characteristic, so the separability criterion correctly rejects `X²`. -/
theorem not_separable_X_sq_zmod_two :
    ¬ (X ^ 2 : (ZMod 2)[X]).Separable := by
  have hd : derivative (X ^ 2 : (ZMod 2)[X]) = 0 := by
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [derivative_X_pow, h2, map_zero, zero_mul]
  rw [Separable, hd, isCoprime_zero_right]
  intro h
  have hdeg := natDegree_eq_zero_of_isUnit h
  simp at hdeg

end CharacteristicTwo

end FactorRemainderTheoremOQ01OQ02OQ01
