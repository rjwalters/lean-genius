/-
  Nth Root Irrationality OQ-02-OQ-02:
  The general prime-exponent criterion for irrationality of ⁿ√m,
  and radicands that no "prime-appears-exactly-once" argument can reach.

  The parent file `NthRootIrrationalOQ02.lean` established the uniform
  prime-factorization criterion for *not being a perfect power*
  (`not_perfect_pow_of_factorization`: a single prime `p` with `n ∤ m.factorization p`
  certifies that `m` is not a perfect `n`-th power).  However, the *irrationality*
  corollaries it exposes all flow through the special case where a prime divides
  `m` **exactly once** (`irrational_nthRoot_of_sq_not_dvd`, hypotheses `p ∣ m`,
  `p² ∤ m`), or where the radicand is itself prime (`irrational_nthRoot_prime`).

  That "exactly once" hypothesis is *strictly weaker* than the general criterion.
  Consider `m = 36 = 2² · 3²`.  **No** prime divides `36` exactly once — every
  prime factor appears squared — so `not_perfect_pow_of_sq_not_dvd` (hence
  `irrational_nthRoot_of_sq_not_dvd`) is simply inapplicable.  Yet `∛36` is
  irrational, because `36` is not a perfect *cube*: the exponent `2` of the prime
  `3` is not divisible by `3`.  Reaching such radicands requires the full
  criterion `¬ n ∣ m.factorization p` with an arbitrary exponent, not just `1`.

  This file supplies that missing capstone:

  * `not_perfect_pow_of_pow_dvd_not_dvd` — the general "exponent `a`" criterion:
    if `pᵃ ∣ m`, `pᵃ⁺¹ ∤ m` (so `p` appears to exponent exactly `a`) and `n ∤ a`,
    then `m` is not a perfect `n`-th power.  Specializes to
    `not_perfect_pow_of_sq_not_dvd` at `a = 1`, and its two divisibility
    hypotheses are size-independent `decide`s on concrete radicands.
  * `irrational_nthRoot_of_pow_dvd_not_dvd` — the irrationality corollary,
    obtained by feeding the criterion through the parent's `not_perfect_pow_int`
    and the base `irrational_nthRoot`.
  * `irrational_nthRoot_of_factorization_not_dvd` — the same statement phrased
    directly against `m.factorization p`, the cleanest form of the criterion.
  * Concrete irrationalities that the "exactly once" argument cannot certify,
    because their radicands have **no** prime factor of multiplicity `1`:
    `∛36`, `⁴√36`, `∛100`, and `⁶√216` (note `216 = 6³` is a perfect *cube*
    but not a perfect *sixth* power).
  * `thirtySix_has_no_multiplicity_one_prime` — a certificate that `36` genuinely
    lies outside the reach of the parent's exactly-once lemma, so the
    generalization here is necessary, not cosmetic.

  Results (0 axioms, 0 sorries): a strict generalization of the parent's
  irrationality corollaries, plus witnesses separating the two.
-/

import Mathlib
import Proofs.NthRootIrrational
import Proofs.NthRootIrrationalOQ02

set_option maxHeartbeats 1000000

namespace NthRootIrrationalOQ02OQ02

open NthRootIrrational NthRootIrrationalOQ02

/-! ## Part 1: The General Exponent Criterion

`not_perfect_pow_of_sq_not_dvd` (parent) fixes the multiplicity of the witnessing
prime at `1`.  Here we allow an arbitrary multiplicity `a`: if `p` appears in `m`
to exponent exactly `a` (pinned by `pᵃ ∣ m` and `pᵃ⁺¹ ∤ m`) and `n ∤ a`, then `m`
is not a perfect `n`-th power.  The proof reads the exact exponent off the two
`pow_dvd_iff_le_factorization` bounds and hands it to
`not_perfect_pow_of_factorization`. -/

/-- **General not-a-perfect-power criterion by pinned multiplicity.**  If the prime
`p` divides `m` to exponent exactly `a` (`pᵃ ∣ m`, `pᵃ⁺¹ ∤ m`) and `n ∤ a`, then
`m` is not a perfect `n`-th power.  At `a = 1` this is the parent's
`not_perfect_pow_of_sq_not_dvd`. -/
theorem not_perfect_pow_of_pow_dvd_not_dvd {m n p a : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hd : p ^ a ∣ m) (hnd : ¬ p ^ (a + 1) ∣ m) (hna : ¬ n ∣ a) :
    ¬ ∃ k : ℕ, k ^ n = m := by
  apply not_perfect_pow_of_factorization (p := p)
  have hle : a ≤ m.factorization p :=
    (hp.pow_dvd_iff_le_factorization hm).mp hd
  have hlt : ¬ a + 1 ≤ m.factorization p := fun h =>
    hnd ((hp.pow_dvd_iff_le_factorization hm).mpr h)
  have heq : m.factorization p = a := by omega
  rwa [heq]

/-! ## Part 2: Irrationality Corollaries

Feed the general criterion through the parent's `ℕ ⟹ ℤ` bridge and the base
`irrational_nthRoot`. -/

/-- **Irrationality of `ⁿ√m` from a pinned prime multiplicity not divisible by `n`.**
If some prime `p` appears in `m` to exponent exactly `a` with `n ∤ a`, then `ⁿ√m`
is irrational.  Generalizes `irrational_nthRoot_of_sq_not_dvd` (the `a = 1` case). -/
theorem irrational_nthRoot_of_pow_dvd_not_dvd {m n p a : ℕ} (hn : 1 < n) (hp : p.Prime)
    (hm : m ≠ 0) (hd : p ^ a ∣ m) (hnd : ¬ p ^ (a + 1) ∣ m) (hna : ¬ n ∣ a) :
    Irrational (nthRoot n m) :=
  irrational_nthRoot n m hn
    (not_perfect_pow_int (not_perfect_pow_of_pow_dvd_not_dvd hp hm hd hnd hna))

/-- **Irrationality of `ⁿ√m` directly from the factorization criterion.**  The
cleanest packaging: if the exponent `m.factorization p` of some prime `p` is not
divisible by `n`, then `ⁿ√m` is irrational.  This is the general form the parent's
exactly-once and prime corollaries are instances of. -/
theorem irrational_nthRoot_of_factorization_not_dvd {m n p : ℕ} (hn : 1 < n)
    (hndvd : ¬ n ∣ m.factorization p) :
    Irrational (nthRoot n m) :=
  irrational_nthRoot n m hn
    (not_perfect_pow_int (not_perfect_pow_of_factorization hndvd))

/-! ## Part 3: Radicands With No Multiplicity-One Prime

Each radicand below is a product of squared primes, so the parent's
`irrational_nthRoot_of_sq_not_dvd` — which needs a prime `p` with `p ∣ m` and
`p² ∤ m` — cannot be applied to any of them.  The general criterion certifies
their irrationality with the same cheap, size-independent divisibility checks. -/

/-- `∛36` irrational.  `36 = 2² · 3²`; witness the prime `3` at multiplicity `2`
(`9 ∣ 36`, `27 ∤ 36`), and `3 ∤ 2`.  No prime divides `36` exactly once, so the
parent's `sq_not_dvd` corollary does not apply. -/
theorem irrational_cbrt_36 : Irrational (nthRoot 3 36) :=
  irrational_nthRoot_of_pow_dvd_not_dvd (by norm_num) (p := 3) (a := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `⁴√36` irrational.  Same radicand; the prime `2` at multiplicity `2`
(`4 ∣ 36`, `8 ∤ 36`) works since `4 ∤ 2`. -/
theorem irrational_fourthRoot_36 : Irrational (nthRoot 4 36) :=
  irrational_nthRoot_of_pow_dvd_not_dvd (by norm_num) (p := 2) (a := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `∛100` irrational.  `100 = 2² · 5²`; witness the prime `5` at multiplicity `2`
(`25 ∣ 100`, `125 ∤ 100`), and `3 ∤ 2`.  Again no prime appears exactly once. -/
theorem irrational_cbrt_100 : Irrational (nthRoot 3 100) :=
  irrational_nthRoot_of_pow_dvd_not_dvd (by norm_num) (p := 5) (a := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `⁶√216` irrational — a striking separation.  `216 = 6³ = 2³ · 3³` is a
*perfect cube*, hence `∛216 = 6` is rational; but it is **not** a perfect sixth
power.  Witness the prime `2` at multiplicity `3` (`8 ∣ 216`, `16 ∤ 216`), and
`6 ∤ 3`.  A per-prime multiplicity that is a proper divisor of `n` — not `1` —
is exactly what the general criterion is for. -/
theorem irrational_sixthRoot_216 : Irrational (nthRoot 6 216) :=
  irrational_nthRoot_of_pow_dvd_not_dvd (by norm_num) (p := 2) (a := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `√72` irrational.  `72 = 2³ · 3²` — the exact radicand the parent entry's
open-questions list named as beyond the reach of its exactly-once corollary
(every prime exponent is `≥ 2`).  Witness the prime `2` at multiplicity `3`
(`8 ∣ 72`, `16 ∤ 72`), and `2 ∤ 3`. -/
theorem irrational_sqrt_72 : Irrational (nthRoot 2 72) :=
  irrational_nthRoot_of_pow_dvd_not_dvd (by norm_num) (p := 2) (a := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Part 4: Certifying the Gap

To confirm the generalization is necessary and not cosmetic, we record that `36`
has no prime factor of multiplicity one: for every prime `p` dividing `36`, in
fact `p² ∣ 36`.  Consequently the parent's `not_perfect_pow_of_sq_not_dvd` (which
requires `p ∣ m` together with `p² ∤ m`) has *no* applicable witness for `36`,
whereas `irrational_cbrt_36` above still certifies `∛36` irrational. -/

/-- **`36` has no multiplicity-one prime.**  Every prime dividing `36` divides it
at least twice, so the exactly-once hypothesis `p² ∤ 36` fails for all of them —
the parent's `sq_not_dvd` route is unavailable for this radicand. -/
theorem thirtySix_has_no_multiplicity_one_prime :
    ∀ p : ℕ, p.Prime → p ∣ 36 → p ^ 2 ∣ 36 := by
  intro p hp hd
  -- The only primes dividing 36 = 2² · 3² are 2 and 3, each to exponent 2.
  have h2 : 2 ≤ p := hp.two_le
  have h36 : p ≤ 36 := Nat.le_of_dvd (by norm_num) hd
  interval_cases p <;> revert hp hd <;> decide

end NthRootIrrationalOQ02OQ02
