import Mathlib.Tactic
import Proofs.FactorRemainderHasseDerivativeFq
import Proofs.FactorRemainderHasseDerivativeFqOQ01

/-
# The Hasse-derivative multiplicity oracle: characteristic-free exactness

Problem id: `factor-remainder-hasse-derivative-fq-oq-02`
(child of `factor-remainder-hasse-derivative-fq`, sibling of `-oq-01`).

## Question

The parent entry (`FactorRemainderHasseDerivativeFq`) and its first child
(`FactorRemainderHasseDerivativeFqOQ01`) analyse the *ordinary* iterated-derivative
multiplicity test and find it defective in positive characteristic: over a field of
characteristic `p` it is exact only for true multiplicities `m < p` and overcounts
**without bound** the moment `m ≥ p` (`overcounting_dichotomy`).  The obvious next
question is the *positive* one the negative results leave open:

> Is there a derivative-style test that reports the exact multiplicity in **every**
> characteristic, and if so what is its precise form?

## Answer — the Hasse test is a universal exact oracle

Yes.  Replacing the ordinary derivative `derivative^[j]` by the **Hasse derivative**
`hasseDeriv j` — the divided-power operator whose value does not carry the `j!` factor
that collapses to `0` past the characteristic — yields a test that is *exact in every
characteristic, with no hypothesis on `p` at all*.  Concretely, defining the
Hasse test to *certify* multiplicity `≥ n` when every Hasse derivative of order `< n`
vanishes at `a` (`HasseCertifies`, the divided-power analogue of OQ-01's
`OrdinaryCertifies`), we prove:

* `hasseCertifies_iff_le_rootMultiplicity` — **exactness.** For `f ≠ 0`,
  `HasseCertifies f a n ↔ n ≤ rootMultiplicity a f`.  The Hasse test certifies exactly
  the true multiplicity and never a hair more — *in any characteristic*.  Contrast
  OQ-01's `ordinary_certifies_all_of_char_pow_dvd`, where the ordinary test certifies
  **every** `n` once `m ≥ p`.
* `hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity` /
  `hasseDeriv_rootMultiplicity_eval_ne_zero` — the two halves of "first nonvanishing
  order": below the true multiplicity every Hasse derivative vanishes at `a`, and at the
  multiplicity itself the Hasse derivative is nonzero.
* `rootMultiplicity_isLeast_hasseDeriv_ne_zero` — **the capstone.** For `f ≠ 0`,
  `rootMultiplicity a f` is the **least** order at which a Hasse derivative fails to
  vanish at `a`.  This is the characteristic-free oracle in its sharpest form, and it
  carries *no* `CharP` hypothesis.

Finally `hasse_exact_where_ordinary_diverges` places the two tests side by side on the
same polynomial in characteristic `p`: exactly where OQ-01's ordinary test runs away to
`∞` (any `f` with `(X − a)ᵖ ∣ f`), the Hasse test stops precisely at the true
multiplicity.  `hasse_oracle_X_pow` realises the contrast on the witness `f = Xᵖ`.

## Why this is not merely a restatement of the parent

The parent's `sub_pow_dvd_iff_hasseDeriv_eval_eq_zero` (Mathlib's
`Polynomial.pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero`) is a *divisibility* criterion phrased with
an order bound `n`.  The contribution here is to turn it into a **pointwise multiplicity
oracle**: the identification of `rootMultiplicity a f` as the least nonvanishing Hasse
order (`IsLeast`), the exact certified-value equivalence, and the explicit head-to-head
against OQ-01's unbounded-overcount regime.  None of these appear in the parent or in
`-oq-01`, and the capstone's *absence* of any characteristic hypothesis is the whole
point of the positive resolution.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open Polynomial Nat FactorRemainderHasseDerivativeFq FactorRemainderHasseDerivativeFqOQ01

namespace FactorRemainderHasseDerivativeFqOQ02

variable {F : Type*} {p : ℕ}

/-- The Hasse-derivative test **certifies** multiplicity `≥ n` for `f` at `a` when every
Hasse derivative of order below `n` vanishes at `a`.  This is the divided-power analogue of
OQ-01's `OrdinaryCertifies`; the difference is that the Hasse value does not carry the `(j! : F)`
factor that annihilates the ordinary test past the characteristic. -/
def HasseCertifies [CommRing F] (f : F[X]) (a : F) (n : ℕ) : Prop :=
  ∀ j < n, (hasseDeriv j f).eval a = 0

/-- **The Hasse test measures divisibility exactly.** Certifying multiplicity `≥ n` is
*equivalent* to `(X − a)ⁿ ∣ f`, in every characteristic and over any commutative ring.  This is
the parent's Hasse criterion `sub_pow_dvd_iff_hasseDeriv_eval_eq_zero` read as a
statement about the test. -/
theorem hasseCertifies_iff_pow_dvd [CommRing F] (a : F) (n : ℕ) (f : F[X]) :
    HasseCertifies f a n ↔ (X - C a) ^ n ∣ f :=
  (sub_pow_dvd_iff_hasseDeriv_eval_eq_zero a n f).symm

/-- **Exactness of the Hasse test (characteristic-free).** For `f ≠ 0` the Hasse test certifies
multiplicity `≥ n` **iff** `n ≤ rootMultiplicity a f`: it reports the true multiplicity and never
overcounts, with *no* hypothesis on the characteristic.

This is the sharp positive counterpart to OQ-01's `ordinary_certifies_all_of_char_pow_dvd`, where
in characteristic `p` the ordinary test certifies *every* `n` as soon as `p ≤ m`. -/
theorem hasseCertifies_iff_le_rootMultiplicity [Field F] {f : F[X]} (hf : f ≠ 0) (a : F) (n : ℕ) :
    HasseCertifies f a n ↔ n ≤ rootMultiplicity a f :=
  (hasseCertifies_iff_pow_dvd a n f).trans (le_rootMultiplicity_iff hf).symm

/-- **Below the true multiplicity, every Hasse derivative vanishes at the root.** If
`j < rootMultiplicity a f` then `(hasseDeriv j f).eval a = 0`.  No `f ≠ 0` hypothesis is needed
(for `f = 0` the multiplicity is `0` and the statement is vacuous). -/
theorem hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity [Field F] {f : F[X]} {a : F} {j : ℕ}
    (hj : j < rootMultiplicity a f) : (hasseDeriv j f).eval a = 0 :=
  (sub_pow_dvd_iff_hasseDeriv_eval_eq_zero a _ f).mp (pow_rootMultiplicity_dvd f a) j hj

/-- **At the true multiplicity the Hasse derivative is nonzero.** For `f ≠ 0`,
`(hasseDeriv (rootMultiplicity a f) f).eval a ≠ 0`: order `m := rootMultiplicity a f` is the first
place the Hasse test detects a nonzero value.

Proof: `(X − a)ᵐ⁺¹ ∤ f` because `m + 1 > m = rootMultiplicity a f`, so by the Hasse criterion some
Hasse derivative of order `< m + 1` is nonzero at `a`; every order `< m` vanishes
(`hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity`), so the offender is order `m` itself. -/
theorem hasseDeriv_rootMultiplicity_eval_ne_zero [Field F] {f : F[X]} (hf : f ≠ 0) (a : F) :
    (hasseDeriv (rootMultiplicity a f) f).eval a ≠ 0 := by
  intro h0
  have hndvd : ¬ (X - C a) ^ (rootMultiplicity a f + 1) ∣ f := by
    rw [← le_rootMultiplicity_iff hf]; omega
  refine hndvd ?_
  rw [sub_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  intro j hj
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
  · exact hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity hlt
  · rw [heq]; exact h0

/-- **The Hasse-derivative multiplicity oracle (capstone).** For `f ≠ 0`,
`rootMultiplicity a f` is the **least** order at which a Hasse derivative fails to vanish at `a`:

  `IsLeast {n | (hasseDeriv n f).eval a ≠ 0} (rootMultiplicity a f)`.

Equivalently, the true multiplicity of `f` at `a` can be *read off* as the first nonvanishing
Hasse-derivative order — a correct multiplicity test that holds over **every** field, with no
characteristic hypothesis whatsoever.  This is the positive resolution of the defect OQ-01
quantified for the ordinary derivative. -/
theorem rootMultiplicity_isLeast_hasseDeriv_ne_zero [Field F] {f : F[X]} (hf : f ≠ 0) (a : F) :
    IsLeast {n | (hasseDeriv n f).eval a ≠ 0} (rootMultiplicity a f) := by
  refine ⟨hasseDeriv_rootMultiplicity_eval_ne_zero hf a, ?_⟩
  intro y hy
  by_contra h
  push_neg at h
  exact hy (hasseDeriv_eval_eq_zero_of_lt_rootMultiplicity h)

/-- **Head-to-head with OQ-01: the Hasse test stays exact exactly where the ordinary test
diverges.** In characteristic `p`, take any `f ≠ 0` with `(X − a)ᵖ ∣ f` — the unbounded-overcount
regime of OQ-01.  Then:

* the **ordinary** test certifies multiplicity `≥ n` for *every* `n`
  (OQ-01 `ordinary_certifies_all_of_char_pow_dvd`), while
* the **Hasse** test stops one step past the truth: it does *not* certify
  `rootMultiplicity a f + 1`.

So on the very polynomials where the ordinary derivative test runs away to `∞`, the Hasse test
still pins the multiplicity exactly. -/
theorem hasse_exact_where_ordinary_diverges [Field F] [CharP F p] (hp : p.Prime)
    {f : F[X]} (hf : f ≠ 0) (a : F) (hdvd : (X - C a) ^ p ∣ f) :
    (∀ n, OrdinaryCertifies f a n) ∧ ¬ HasseCertifies f a (rootMultiplicity a f + 1) := by
  refine ⟨ordinary_certifies_all_of_char_pow_dvd hp f a hdvd, ?_⟩
  rw [hasseCertifies_iff_le_rootMultiplicity hf]
  omega

/-- **The contrast realised on `f = Xᵖ`.** Over a characteristic-`p` field the ordinary test
certifies *every* multiplicity at `0`, yet the Hasse oracle reads off the exact value: the least
nonvanishing Hasse-derivative order of `Xᵖ` at `0` is its true multiplicity `p`. -/
theorem hasse_oracle_X_pow [Field F] [CharP F p] (hp : p.Prime) :
    (∀ n, OrdinaryCertifies (X ^ p : F[X]) 0 n) ∧
      IsLeast {n | (hasseDeriv n (X ^ p : F[X])).eval 0 ≠ 0} p := by
  have hdvd : (X - C (0 : F)) ^ p ∣ (X ^ p : F[X]) := by simp
  have hf : (X ^ p : F[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  refine ⟨ordinary_certifies_all_of_char_pow_dvd hp (X ^ p) 0 hdvd, ?_⟩
  have hrm : rootMultiplicity (0 : F) (X ^ p : F[X]) = p := rootMultiplicity_X_pow p
  simpa [hrm] using rootMultiplicity_isLeast_hasseDeriv_ne_zero hf (0 : F)

end FactorRemainderHasseDerivativeFqOQ02
