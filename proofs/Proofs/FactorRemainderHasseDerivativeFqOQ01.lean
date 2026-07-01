import Mathlib.Tactic
import Proofs.FactorRemainderHasseDerivativeFq
import Proofs.FactorRemainderTheoremOQ01OQ02

/-
# The overcounting dichotomy of the ordinary-derivative multiplicity test

Problem id: `factor-remainder-hasse-derivative-fq-oq-01`
(child of `factor-remainder-hasse-derivative-fq`).

## Question

The parent entry (`FactorRemainderHasseDerivativeFq`) shows that over a field of
characteristic `p` the *ordinary* iterated-derivative multiplicity test is reliable
exactly in the range `m ≤ p` and blind from order `p` on.  The open question asks to
**quantify the overcounting for a general polynomial**: given `f` with a root `a` of true
(Hasse) multiplicity `m := rootMultiplicity a f`, how large is the gap between `m` and the
multiplicity the ordinary derivatives certify?

## Answer — a sharp dichotomy

Let the *ordinary-certified multiplicity* be the largest `n` with
`(derivative^[j] f).eval a = 0` for all `j < n` (the ordinary test declares `(X−a)ⁿ ∣ f`).
Using the parent's evaluation form of the scaling identity
`(derivative^[k] f).eval a = (k! : F) · (hasseDeriv k f).eval a`, the certified value is the
least `j` with **both** `j < p` (so `k!` is a unit) **and** `(hasseDeriv j f).eval a ≠ 0`.
Comparing to the true multiplicity `m` (the least `j` with `(hasseDeriv j f).eval a ≠ 0`),
the outcome splits cleanly on whether `m` reaches the characteristic:

| true multiplicity `m` | ordinary-certified multiplicity | overcounting gap |
|-----------------------|--------------------------------|------------------|
| `m < p`               | exactly `m`                    | `0` (exact)      |
| `m ≥ p`               | unbounded (every order passes) | `∞`              |

There is no intermediate regime: the ordinary test is either **perfectly exact** or
**infinitely wrong**, and the switch happens precisely at `m = p`.

## Main results

* `unbounded_overcount` — **`m ≥ p` case.** If `(X − a)ᵖ ∣ f` (i.e. the true multiplicity is
  at least `p`) then `(derivative^[j] f).eval a = 0` for **every** `j`.  The ordinary test
  certifies `(X − a)ⁿ ∣ f` for all `n`, an unbounded overcount.
* `ordinary_certifies_all_of_char_pow_dvd` — packaged form: the ordinary test certifies
  multiplicity `≥ n` for every `n`.
* `ordinary_exact_below_threshold` — **`m < p` case (divisibility form).** If the true
  multiplicity is exactly `m < p` (`(X−a)ᵐ ∣ f`, `(X−a)ᵐ⁺¹ ∤ f`), then the ordinary
  derivatives vanish at `a` for all `j < m` and `(derivative^[m] f).eval a ≠ 0`: the ordinary
  test first fails at order `m`, so it certifies exactly `m`.  Gap `= 0`.
* `overcounting_dichotomy` — **the capstone.** For any `f ≠ 0`, phrased through the true
  `rootMultiplicity a f`, exactly one of the two regimes above holds.
* `overcount_X_pow`, `exact_X_sub_C` — the two regimes realized: `Xᵖ` (unbounded overcount)
  and a linear factor `X − a` (exact, `m = 1 < p`).

All results are `0`-axiom, `0`-sorry, over any characteristic-`p` field (hence every `𝔽_q`).
-/

namespace FactorRemainderHasseDerivativeFqOQ01

open Polynomial Nat FactorRemainderHasseDerivativeFq FactorRemainderTheoremOQ01OQ02

variable {F : Type*} {p : ℕ}

/-- **Evaluation form of the scaling identity.** Evaluating
`derivative^[k] f = (k! : F) • hasseDeriv k f` (parent
`iterate_derivative_eq_smul_hasseDeriv`) at a point `a` turns the scalar action into
multiplication: `(derivative^[k] f).eval a = (k! : F) * (hasseDeriv k f).eval a`. This is the
bridge that lets the factorial threshold `(k! : F) = 0 ↔ p ≤ k` control the *values* of the
ordinary derivatives, not just the whole polynomials. -/
theorem iterate_derivative_eval_eq [CommRing F] (k : ℕ) (f : F[X]) (a : F) :
    (derivative^[k] f).eval a = (k ! : F) * (hasseDeriv k f).eval a := by
  rw [iterate_derivative_eq_smul_hasseDeriv, smul_eq_C_mul, eval_mul, eval_C]

/-- The ordinary-derivative test **certifies** multiplicity `≥ n` for `f` at `a` when every
ordinary derivative of order below `n` vanishes at `a` — the largest such `n` is the
multiplicity the ordinary test reports. -/
def OrdinaryCertifies [CommRing F] (f : F[X]) (a : F) (n : ℕ) : Prop :=
  ∀ j < n, (derivative^[j] f).eval a = 0

/-- **Above the threshold every ordinary derivative already vanishes at a point.** For
`p ≤ j` the whole polynomial `derivative^[j] f` is `0` (parent
`iterate_derivative_eq_zero_of_char_le`), so a fortiori its value at `a` is `0`. -/
theorem ordinary_eval_eq_zero_of_char_le [Field F] [CharP F p] (hp : p.Prime)
    {j : ℕ} (hj : p ≤ j) (f : F[X]) (a : F) :
    (derivative^[j] f).eval a = 0 := by
  rw [iterate_derivative_eq_zero_of_char_le hp hj, eval_zero]

/-- **Unbounded overcount (`m ≥ p`).** If `(X − a)ᵖ ∣ f`, then `(derivative^[j] f).eval a = 0`
for **every** order `j`.

Split on the factorial threshold: for `j ≥ p` the ordinary derivative vanishes identically
(`ordinary_eval_eq_zero_of_char_le`); for `j < p` the Hasse derivative vanishes at `a` because
`(X − a)ᵖ ∣ f` (parent Hasse criterion), and the ordinary value is `j!` times it.  So the
ordinary test never sees a nonzero value and certifies arbitrarily large multiplicity. -/
theorem unbounded_overcount [Field F] [CharP F p] (hp : p.Prime)
    (f : F[X]) (a : F) (hdvd : (X - C a) ^ p ∣ f) :
    ∀ j, (derivative^[j] f).eval a = 0 := by
  intro j
  rcases le_or_gt p j with hj | hj
  · exact ordinary_eval_eq_zero_of_char_le hp hj f a
  · have hhasse : (hasseDeriv j f).eval a = 0 :=
      (pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero a p f).mp hdvd j hj
    rw [iterate_derivative_eval_eq, hhasse, mul_zero]

/-- Packaged form of `unbounded_overcount`: when `(X − a)ᵖ ∣ f` the ordinary test certifies
multiplicity `≥ n` for *every* `n`. -/
theorem ordinary_certifies_all_of_char_pow_dvd [Field F] [CharP F p] (hp : p.Prime)
    (f : F[X]) (a : F) (hdvd : (X - C a) ^ p ∣ f) (n : ℕ) :
    OrdinaryCertifies f a n :=
  fun j _ => unbounded_overcount hp f a hdvd j

/-- **Exactness below the threshold (`m < p`).** If the true multiplicity of `f` at `a` is
exactly `m < p` — encoded as `(X − a)ᵐ ∣ f` and `(X − a)ᵐ⁺¹ ∤ f` — then:

* the ordinary derivatives of order `j < m` vanish at `a` (so the test certifies `≥ m`), and
* `(derivative^[m] f).eval a ≠ 0` (so the test fails at order `m` and certifies no more).

Hence the ordinary-certified multiplicity is exactly `m`: the overcounting gap is `0`.

Below `p` every `(j! : F)` is a unit, so ordinary and Hasse values vanish together; the true
multiplicity `m` is the first nonvanishing Hasse order, and `m! ≠ 0` promotes that to a
nonzero ordinary value. -/
theorem ordinary_exact_below_threshold [Field F] [CharP F p] (hp : p.Prime)
    {m : ℕ} (hm : m < p) (f : F[X]) (a : F)
    (hdvd : (X - C a) ^ m ∣ f) (hndvd : ¬ (X - C a) ^ (m + 1) ∣ f) :
    (∀ j < m, (derivative^[j] f).eval a = 0) ∧ (derivative^[m] f).eval a ≠ 0 := by
  have hbelow : ∀ j < m, (hasseDeriv j f).eval a = 0 :=
    (pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero a m f).mp hdvd
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [iterate_derivative_eval_eq, hbelow j hj, mul_zero]
  · -- The `m+1`-th Hasse test must fail somewhere `< m+1`; below `m` it holds, so at `m`.
    have hnot : ¬ ∀ j < m + 1, (hasseDeriv j f).eval a = 0 := by
      rw [← pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero]; exact hndvd
    have hm_ne : (hasseDeriv m f).eval a ≠ 0 := by
      intro h0
      refine hnot (fun j hj => ?_)
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · exact hbelow j hlt
      · rw [heq]; exact h0
    rw [iterate_derivative_eval_eq]
    have hfac : (m ! : F) ≠ 0 := by
      rw [Ne, factorial_cast_eq_zero_iff hp]; omega
    exact mul_ne_zero hfac hm_ne

/-- **The overcounting dichotomy (capstone).** Over a field of characteristic `p`, for any
`f ≠ 0` with true multiplicity `m := rootMultiplicity a f` at `a`, exactly one regime holds:

* `m < p`: the ordinary-derivative test is **exact** — it certifies precisely `m`
  (vanishing below `m`, nonzero at `m`); the overcounting gap is `0`; or
* `m ≥ p`: the ordinary-derivative test **overcounts without bound** — every ordinary
  derivative vanishes at `a`, so it certifies every multiplicity.

The transition is sharp at `m = p`. -/
theorem overcounting_dichotomy [Field F] [CharP F p] (hp : p.Prime)
    (f : F[X]) (hf : f ≠ 0) (a : F) :
    (rootMultiplicity a f < p ∧
        (∀ j < rootMultiplicity a f, (derivative^[j] f).eval a = 0) ∧
        (derivative^[rootMultiplicity a f] f).eval a ≠ 0)
    ∨ (p ≤ rootMultiplicity a f ∧ ∀ j, (derivative^[j] f).eval a = 0) := by
  set m := rootMultiplicity a f with hm
  rcases lt_or_ge m p with hlt | hge
  · left
    refine ⟨hlt, ?_⟩
    have hdvd : (X - C a) ^ m ∣ f := (le_rootMultiplicity_iff hf).mp (le_refl m)
    have hndvd : ¬ (X - C a) ^ (m + 1) ∣ f := by
      rw [← le_rootMultiplicity_iff hf]; omega
    exact ordinary_exact_below_threshold hp hlt f a hdvd hndvd
  · right
    refine ⟨hge, ?_⟩
    have hdvd : (X - C a) ^ p ∣ f := (le_rootMultiplicity_iff hf).mp hge
    exact unbounded_overcount hp f a hdvd

/-- **Unbounded-overcount regime realized: `Xᵖ`.** Over a characteristic-`p` field every
ordinary derivative of `Xᵖ` vanishes at `0`, while its true multiplicity there is `p`. -/
theorem overcount_X_pow [Field F] [CharP F p] (hp : p.Prime) :
    ∀ j, (derivative^[j] (X ^ p : F[X])).eval 0 = 0 := by
  refine unbounded_overcount hp (X ^ p) 0 ?_
  simp

/-- **Exact regime realized: a linear factor `X − a`.** Its true multiplicity at `a` is
`1 < p`, and the ordinary test certifies exactly `1`: `(derivative^[0] (X − C a)).eval a = 0`
but `(derivative^[1] (X − C a)).eval a = 1 ≠ 0`. -/
theorem exact_X_sub_C [Field F] [CharP F p] (_hp : p.Prime) (a : F) :
    (derivative^[0] (X - C a : F[X])).eval a = 0 ∧
      (derivative^[1] (X - C a : F[X])).eval a ≠ 0 := by
  refine ⟨by simp, ?_⟩
  simp only [Function.iterate_one, derivative_sub, derivative_X, derivative_C, sub_zero,
    eval_one]
  exact one_ne_zero

end FactorRemainderHasseDerivativeFqOQ01
