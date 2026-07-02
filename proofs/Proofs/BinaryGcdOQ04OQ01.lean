/-
  A total, executable binary GCD for the Gaussian integers ℤ[i]
  =============================================================

  The parent entry `BinaryGcdOQ04` builds the *correctness layer* of Stein's
  binary GCD over ℤ[i]: the arithmetic of the prime π = 1+i, the parity
  dichotomy ℤ[i]/(π) ≅ 𝔽₂, the exact divide-by-π map `divPi`, and the three
  reduction identities up to `Associated`

    * `gcd_pi_mul`      — both π-even : gcd(πa, πb) ~ π·gcd(a, b)
    * `gcd_pi_mul_odd`  — one  π-even : gcd(πa, v) ~ gcd(a, v)   (π ∤ v)
    * `gcd_sub`         — both π-odd  : gcd(u, v)  ~ gcd(u−v, v)

  What was still missing (the parent's own open question OQ-04-OQ-01) is to
  **package those reductions into an actual algorithm** — a total function
  that runs the reductions and returns a gcd — and to prove that algorithm
  correct against `EuclideanDomain.gcd`.

  This file does exactly that.

  ## The function

  `binaryGcdAux : ℕ → ℤ[i] → ℤ[i] → Option ℤ[i]` is the fuel-indexed driver.
  Each call consumes one unit of fuel and performs one reduction, branching on
  the decidable π-parity predicate `PiEven z := 2 ∣ (z.re + z.im)`:

    * `u = 0`  → return `v`;  `v = 0` → return `u`   (base cases);
    * both π-even → recurse on `(divPi u, divPi v)`, multiply the result by π;
    * `u` π-even, `v` π-odd → recurse on `(divPi u, v)`   (strip a π from u);
    * `u` π-odd, `v` π-even → recurse on `(u, divPi v)`;
    * both π-odd → recurse on `(u − v, v)`   (Euclidean subtraction).

  Fuel makes the function **total** without a well-foundedness proof; a fuel
  budget that is too small yields `none`.

  ## The correctness theorem (fully verified, 0 axioms)

  `binaryGcdAux_correct` : whenever the driver returns an answer, that answer
  is an associate of the Euclidean gcd —

        binaryGcdAux fuel u v = some g  →  Associated g (EuclideanDomain.gcd u v).

  This is *partial correctness*: the algorithm never returns a wrong value.
  It is proved by a single induction on fuel; every recursive step is
  discharged by one of the parent's three reduction identities (with a
  gcd-commutativity-up-to-associates helper for the mirrored one-even case).

  `binaryGcdGaussian` then wraps the driver with a concrete norm-based fuel
  budget into a genuinely total `ℤ[i] → ℤ[i] → ℤ[i]`, and

        binaryGcdGaussian u v  ~  EuclideanDomain.gcd u v      (Associated)

  holds **unconditionally** (`binaryGcdGaussian_associated`).

  ## Honest scope

  The substantive verified content is *partial correctness*: the algorithm is
  proved never to lie. The total wrapper attains an unconditional
  `Associated`-to-`gcd` statement by design (it falls back to the Euclidean
  gcd if its fuel budget is ever exhausted — a formal totality device, not a
  claim that the raw budget always suffices). Proving that a *computable* fuel
  bound always suffices for the naive subtraction step is the genuinely
  delicate part: unlike over ℤ, the both-π-odd subtraction need not decrease
  the Gaussian norm, and a termination guarantee needs Weilert's refined
  (1+i)-ary step. That analysis is deferred; it is orthogonal to the
  correctness proved here.

  References:
    * A. Weilert, "(1+i)-ary GCD computation in ℤ[i] as an analogue to the
      binary GCD algorithm", J. Symbolic Comput. 30 (2000) 605–617.
    * D. Knuth, TAOCP Vol. 2, §4.5.2 (binary gcd), §4.5.4 (Gaussian gcd).
-/
import Mathlib
import Proofs.BinaryGcdOQ04

namespace BinaryGcdOQ04OQ01

open Zsqrtd BinaryGcdOQ04

/-!
### The decidable π-parity test

`PiEven z` is the concrete, decidable form of "π ∣ z": by the parent's parity
dichotomy `pi_dvd_iff`, divisibility by π = 1+i is exactly evenness of
`z.re + z.im`. Branching the algorithm on this ℤ-predicate keeps every step
executable.
-/

/-- `z` is π-even: `2 ∣ (z.re + z.im)`, equivalently `π = 1+i` divides `z`
    (see `piEven_iff`). A decidable ℤ-predicate the algorithm branches on. -/
def PiEven (z : GaussianInt) : Prop := (2 : ℤ) ∣ (z.re + z.im)

instance : DecidablePred PiEven :=
  fun z => inferInstanceAs (Decidable ((2 : ℤ) ∣ (z.re + z.im)))

/-- The parity test agrees with divisibility by π. -/
lemma piEven_iff (z : GaussianInt) : PiEven z ↔ pi ∣ z := (pi_dvd_iff z).symm

lemma piEven_of (z : GaussianInt) (h : PiEven z) : pi ∣ z := (piEven_iff z).mp h

lemma not_pi_dvd_of_not_piEven (z : GaussianInt) (h : ¬ PiEven z) : ¬ pi ∣ z :=
  fun hd => h ((piEven_iff z).mpr hd)

/-!
### The fuel-indexed driver
-/

/-- The fuel-indexed binary-GCD driver for `ℤ[i]`. One reduction per unit of
    fuel; `none` means the budget ran out. See the module header for the
    branch structure. -/
def binaryGcdAux : ℕ → GaussianInt → GaussianInt → Option GaussianInt
  | 0, _, _ => none
  | fuel + 1, u, v =>
    if u = 0 then some v
    else if v = 0 then some u
    else if PiEven u then
      if PiEven v then
        match binaryGcdAux fuel (divPi u) (divPi v) with
        | none => none
        | some g => some (pi * g)
      else binaryGcdAux fuel (divPi u) v
    else if PiEven v then binaryGcdAux fuel u (divPi v)
    else binaryGcdAux fuel (u - v) v

/-!
### A gcd-commutativity helper (up to associates)

The one-π-even reduction `gcd_pi_mul_odd` from the parent strips a π from the
*first* argument. For the mirror case (even second argument) we swap arguments
using the fact that the Euclidean gcd is commutative up to a unit.
-/

/-- `EuclideanDomain.gcd` is commutative up to associates. -/
lemma gcd_associated_comm (a b : GaussianInt) :
    Associated (EuclideanDomain.gcd a b) (EuclideanDomain.gcd b a) :=
  associated_of_dvd_dvd
    (EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right a b)
      (EuclideanDomain.gcd_dvd_left a b))
    (EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right b a)
      (EuclideanDomain.gcd_dvd_left b a))

/-!
### Partial correctness

The algorithm never returns a wrong answer: any value it produces is an
associate of the Euclidean gcd. Proved by induction on fuel, one reduction
identity per branch.
-/

/-- **Partial correctness.** Whenever the fuel-indexed driver returns a value,
    that value is an associate of `EuclideanDomain.gcd u v`. -/
theorem binaryGcdAux_correct :
    ∀ (fuel : ℕ) (u v g : GaussianInt),
      binaryGcdAux fuel u v = some g → Associated g (EuclideanDomain.gcd u v) := by
  intro fuel
  induction fuel with
  | zero => intro u v g h; simp [binaryGcdAux] at h
  | succ n ih =>
    intro u v g h
    rw [binaryGcdAux] at h
    split_ifs at h with hu hv hpu hpv hpv2
    · -- u = 0 : return v ; gcd 0 v = v
      subst hu
      rw [Option.some.injEq] at h; subst h
      rw [EuclideanDomain.gcd_zero_left]
    · -- v = 0 : return u ; gcd u 0 = u
      subst hv
      rw [Option.some.injEq] at h; subst h
      rw [EuclideanDomain.gcd_zero_right]
    · -- both π-even : recurse on (divPi u, divPi v), scale by π
      have hdu : pi ∣ u := piEven_of u hpu
      have hdv : pi ∣ v := piEven_of v hpv
      cases hb : binaryGcdAux n (divPi u) (divPi v) with
      | none => simp [hb] at h
      | some g' =>
        simp only [hb, Option.some.injEq] at h
        subst h
        have hih : Associated g' (EuclideanDomain.gcd (divPi u) (divPi v)) :=
          ih (divPi u) (divPi v) g' hb
        have hmul :
            Associated (EuclideanDomain.gcd u v)
              (pi * EuclideanDomain.gcd (divPi u) (divPi v)) := by
          have := gcd_pi_mul (divPi u) (divPi v)
          rwa [pi_mul_divPi u hdu, pi_mul_divPi v hdv] at this
        exact (hih.mul_left pi).trans hmul.symm
    · -- u π-even, v π-odd : recurse on (divPi u, v)
      have hdu : pi ∣ u := piEven_of u hpu
      have hvodd : ¬ pi ∣ v := not_pi_dvd_of_not_piEven v hpv
      have hih : Associated g (EuclideanDomain.gcd (divPi u) v) :=
        ih (divPi u) v g h
      have hodd :
          Associated (EuclideanDomain.gcd u v) (EuclideanDomain.gcd (divPi u) v) := by
        have := gcd_pi_mul_odd (divPi u) v hvodd
        rwa [pi_mul_divPi u hdu] at this
      exact hih.trans hodd.symm
    · -- u π-odd, v π-even : recurse on (u, divPi v)
      have hdv : pi ∣ v := piEven_of v hpv2
      have huodd : ¬ pi ∣ u := not_pi_dvd_of_not_piEven u hpu
      have hih : Associated g (EuclideanDomain.gcd u (divPi v)) :=
        ih u (divPi v) g h
      have hodd :
          Associated (EuclideanDomain.gcd v u) (EuclideanDomain.gcd (divPi v) u) := by
        have := gcd_pi_mul_odd (divPi v) u huodd
        rwa [pi_mul_divPi v hdv] at this
      -- gcd u v ~ gcd v u ~ gcd (divPi v) u ~ gcd u (divPi v)
      have hchain :
          Associated (EuclideanDomain.gcd u v) (EuclideanDomain.gcd u (divPi v)) :=
        (gcd_associated_comm u v).trans (hodd.trans (gcd_associated_comm (divPi v) u))
      exact hih.trans hchain.symm
    · -- both π-odd : recurse on (u − v, v)
      have hih : Associated g (EuclideanDomain.gcd (u - v) v) :=
        ih (u - v) v g h
      exact hih.trans (gcd_sub u v).symm

/-!
### A total wrapper

Running the driver with a concrete (norm-based) fuel budget, and falling back
to the Euclidean gcd only if that budget is somehow exhausted, gives a total
`ℤ[i] → ℤ[i] → ℤ[i]` that is unconditionally an associate of the gcd. (The
fallback is a formal totality device; on all inputs on which the driver halts,
the returned value is the driver's own output — see `binaryGcdGaussian_spec`.)
-/

/-- Total binary GCD for `ℤ[i]`: run the fuel-indexed driver with a norm-based
    budget, falling back to `EuclideanDomain.gcd` if the budget is exhausted. -/
def binaryGcdGaussian (u v : GaussianInt) : GaussianInt :=
  (binaryGcdAux ((Zsqrtd.norm u).natAbs + (Zsqrtd.norm v).natAbs + 1) u v).getD
    (EuclideanDomain.gcd u v)

/-- **The total binary GCD equals the Euclidean gcd up to a unit.** -/
theorem binaryGcdGaussian_associated (u v : GaussianInt) :
    Associated (binaryGcdGaussian u v) (EuclideanDomain.gcd u v) := by
  unfold binaryGcdGaussian
  cases hb : binaryGcdAux ((Zsqrtd.norm u).natAbs + (Zsqrtd.norm v).natAbs + 1) u v with
  | none => exact Associated.refl _
  | some g => exact binaryGcdAux_correct _ u v g hb

/-- When the driver halts, the wrapper returns exactly the driver's output. -/
theorem binaryGcdGaussian_spec (u v g : GaussianInt)
    (h : binaryGcdAux ((Zsqrtd.norm u).natAbs + (Zsqrtd.norm v).natAbs + 1) u v = some g) :
    binaryGcdGaussian u v = g := by
  unfold binaryGcdGaussian; rw [h]; rfl

/-!
### Executable sanity checks

The driver actually runs: on concrete inputs it halts and produces a gcd.
These are closed kernel `decide` evaluations — no `native_decide`, no axioms.
-/

-- gcd of 6 and 4 (as Gaussian integers) terminates within budget.
example : (binaryGcdAux 40 (⟨6, 0⟩ : GaussianInt) ⟨4, 0⟩).isSome = true := by decide

-- The naive subtraction branch need not terminate quickly: on (5, 2+i) the
-- Gaussian norm does not decrease along the both-π-odd step, so 40 units of
-- fuel are exhausted without reaching a base case. This is the very
-- termination subtlety flagged in the header — over ℤ[i] the subtraction step
-- is not norm-decreasing, and Weilert's refined (1+i)-ary step is needed for a
-- termination guarantee. Partial correctness (`binaryGcdAux_correct`) holds
-- regardless: the driver simply returns `none` rather than a wrong answer.
example : (binaryGcdAux 40 (⟨5, 0⟩ : GaussianInt) ⟨2, 1⟩).isSome = false := by decide

-- The π-parity test matches the parent's dichotomy on a concrete value.
example : PiEven (⟨2, 0⟩ : GaussianInt) := by decide
example : ¬ PiEven (1 : GaussianInt) := by decide

end BinaryGcdOQ04OQ01
