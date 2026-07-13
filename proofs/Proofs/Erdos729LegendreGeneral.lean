/-
  Erdős Problem #729 — OQ-02 follow-up: the GENERAL textbook Legendre identity.

  Companion to `Erdos729Problem.lean`.

  Session S1 (PR #24474) discharged the file's `legendre_identity` *axiom* for the
  single case `p = 2`, proving `legendre_for_two : v_2(n!) = n - s_2(n)` from
  Mathlib's `sub_one_mul_padicValNat_factorial` and *deleting* the general-`p`
  axiom. This file restores the general statement — for EVERY prime `p` — as a
  fully machine-checked theorem (0 axioms / 0 sorries), so the classical

        v_p(n!) = (n - s_p(n)) / (p - 1)            (s_p = base-p digit sum)

  is available in proven form, not just the `p = 2` special case.

  ## The bridge

  Mathlib provides Legendre's theorem only in the *multiplied* form
  `sub_one_mul_padicValNat_factorial [Fact p.Prime] (n) :`
  `(p - 1) * padicValNat p (n!) = n - (p.digits n).sum`
  (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:587`). The classical
  *division* form `v_p(n!) = (n - s_p(n))/(p-1)` is not a named Mathlib lemma:
  it requires `(p-1) ∣ (n - s_p(n))`, which is exactly what the multiplied form
  guarantees. Dividing both sides by `p - 1 > 0` and cancelling
  (`Nat.mul_div_cancel_left`) gives the textbook identity in one step.

  We state it both in Mathlib's native digit sum `(p.digits n).sum` and in the
  recursive `digitSum` shape used by `Erdos729Problem.lean`, bridged by
  `digitSum_eq_digits_sum`.

  Bearer lemmas verified against the Mathlib pin `v4.26.0` (sibling checkout):
  `sub_one_mul_padicValNat_factorial` (PadicVal/Basic.lean:587),
  `Nat.mul_div_cancel_left` (usage form `_ (h : 0 < b)`),
  `Nat.digits_def'` (Data/Nat/Digits/Defs.lean:115), `List.sum_cons`,
  `Nat.div_lt_self`, `Nat.strong_induction_on`, `Nat.pos_of_ne_zero`.
-/

import Mathlib

namespace Erdos729Legendre

open Nat

/-- Base-`p` digit sum, matching `Erdos729Problem.digitSum`.  Defined directly as
`(Nat.digits p n).sum`: the naive recursion `n % p + digitSum p (n / p)` is ill-founded for
`p ≤ 1` (`n / 1 = n` never decreases), so — exactly as the repaired
`Erdos729Problem.digitSum` — we take Mathlib's digit list and sum it. -/
def digitSum (p n : ℕ) : ℕ := (p.digits n).sum

/-- The `digitSum p n` agrees with Mathlib's `(p.digits n).sum`.  Definitional; the `1 < p`
hypothesis is retained for call-site compatibility with the recursive shape. -/
theorem digitSum_eq_digits_sum (p : ℕ) (_hp : 1 < p) (n : ℕ) :
    digitSum p n = (p.digits n).sum := rfl

/-- **Legendre's identity, classical division form (Mathlib digit sum).**

For any prime `p` and any `n`,

  `v_p(n!) = (n - s_p(n)) / (p - 1)`,

where `s_p(n) = (p.digits n).sum`. Derived by dividing the Mathlib lemma
`sub_one_mul_padicValNat_factorial` (`(p-1)·v_p(n!) = n - s_p(n)`) through by
`p - 1`. Mathlib does not state this division form as a named lemma. -/
theorem padicValNat_factorial_eq_div (p n : ℕ) (hp : p.Prime) :
    padicValNat p n.factorial = (n - (p.digits n).sum) / (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  rw [← h, Nat.mul_div_cancel_left _ hp1]

/-- **Legendre's identity in the recursive `digitSum` shape** (the exact statement
of the `legendre_identity` axiom that S1 deleted, now proven for all primes). -/
theorem legendre_digit_sum_identity (p n : ℕ) (hp : p.Prime) :
    padicValNat p n.factorial = (n - digitSum p n) / (p - 1) := by
  rw [digitSum_eq_digits_sum p hp.one_lt n, padicValNat_factorial_eq_div p n hp]

/-- **Legendre's identity, multiplied form (recursive `digitSum` shape).**
The un-divided companion of `legendre_digit_sum_identity`: `(p-1)·v_p(n!) = n - s_p(n)`, the
recursive-`digitSum` restatement of Mathlib's `sub_one_mul_padicValNat_factorial`. Unlike the
division form it carries no truncated-division rounding, so it is the convenient starting
point for Kummer-type valuation arguments. -/
theorem sub_one_mul_padicValNat_factorial_digitSum (p n : ℕ) (hp : p.Prime) :
    (p - 1) * padicValNat p n.factorial = n - digitSum p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [digitSum_eq_digits_sum p hp.one_lt n]
  exact sub_one_mul_padicValNat_factorial (p := p) n

/-- **The base-`p` digit-sum defect is divisible by `p - 1`.**
For every prime `p`, `(p - 1) ∣ (n - s_p(n))` — the classical "casting out nines" fact
generalized to base `p` (`n ≡ s_p(n) (mod p - 1)`), here obtained as a corollary of
Legendre's formula: the defect `n - s_p(n)` equals `(p - 1)·v_p(n!)`. -/
theorem sub_one_dvd_sub_digitSum (p n : ℕ) (hp : p.Prime) :
    (p - 1) ∣ (n - digitSum p n) :=
  ⟨padicValNat p n.factorial, (sub_one_mul_padicValNat_factorial_digitSum p n hp).symm⟩

/-- **The base-`p` digit-sum congruence ("casting out `p − 1`'s").**  For every prime `p`,

  `n ≡ s_p(n)  (mod p − 1)`,

i.e. a number is congruent to its base-`p` digit sum modulo `p − 1`.  This is the
`Nat.ModEq` form of the divisibility `sub_one_dvd_sub_digitSum`, upgraded via
`Nat.modEq_iff_dvd'` and the elementary bound `s_p(n) ≤ n` (`Nat.digit_sum_le`).  It is
the prime-base instance of the schoolbook "casting out nines" rule (base `10`, mod `9`):
for `p = 3` a number and its ternary digit sum agree mod `2`, for `p = 7` they agree mod
`6`, and so on.  (The `p = 2` case, mod `1`, is vacuously true.)  Here it drops straight
out of Legendre's formula, since `n − s_p(n) = (p − 1)·v_p(n!)`. -/
theorem modEq_digitSum (p n : ℕ) (hp : p.Prime) :
    n ≡ digitSum p n [MOD p - 1] :=
  ((Nat.modEq_iff_dvd' (by simpa [digitSum] using Nat.digit_sum_le p n)).mpr
    (sub_one_dvd_sub_digitSum p n hp)).symm

/-- **The sharp `n/(p-1)` upper bound, multiplied form.**  For every prime `p`,
`(p - 1)·v_p(n!) ≤ n`.  Immediate from Legendre's identity
`(p-1)·v_p(n!) = n - s_p(n)` and `n - s_p(n) ≤ n`; this is the exact integer form
of the classical estimate `v_p(n!) ≤ n/(p-1)` (and its heuristic `v_p(n!) ≈ n/(p-1)`),
with the digit-sum defect `s_p(n)` measuring the shortfall. -/
theorem sub_one_mul_padicValNat_factorial_le (p n : ℕ) (hp : p.Prime) :
    (p - 1) * padicValNat p n.factorial ≤ n := by
  rw [sub_one_mul_padicValNat_factorial_digitSum p n hp]
  exact Nat.sub_le n (digitSum p n)

/-- **The sharp `n/(p-1)` upper bound, division form.**  For every prime `p`,
`v_p(n!) ≤ n / (p - 1)` (truncated natural division).  The classical bound on the
`p`-adic valuation of a factorial, obtained from the division identity
`v_p(n!) = (n - s_p(n))/(p-1)` by monotonicity of division in the numerator. -/
theorem padicValNat_factorial_le_div (p n : ℕ) (hp : p.Prime) :
    padicValNat p n.factorial ≤ n / (p - 1) := by
  rw [padicValNat_factorial_eq_div p n hp]
  exact Nat.div_le_div_right (Nat.sub_le n ((p.digits n).sum))

/-- **The exact zero-locus of `v_p(n!)`.**  For every prime `p`,

  `v_p(n!) = 0  ↔  n < p`.

The upper-bound lemmas above (`padicValNat_factorial_le_div` etc.) pin the growth of
`v_p(n!)` from above; this identifies exactly where the valuation *vanishes*.  A prime `p`
first appears as a factor of `n!` precisely at `n = p`, so `n! ` is coprime to `p` iff
`n < p`.  Proven directly from `Nat.Prime.dvd_factorial` (`p ∣ n! ↔ p ≤ n`) together with
the standard positivity/vanishing lemmas for `padicValNat`, independently of the
digit-sum machinery — and it is the natural base case for the sandwich
`0 ≤ v_p(n!) ≤ n/(p-1)`. -/
theorem padicValNat_factorial_eq_zero_iff (p n : ℕ) (hp : p.Prime) :
    padicValNat p n.factorial = 0 ↔ n < p := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have hdvd : p ∣ n.factorial := hp.dvd_factorial.mpr hle
    have : 1 ≤ padicValNat p n.factorial :=
      one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) hdvd
    omega
  · intro hlt
    exact padicValNat.eq_zero_of_not_dvd
      (fun hdvd => absurd (hp.dvd_factorial.mp hdvd) (Nat.not_le.mpr hlt))

/-- **The valuation `v_p(n!)` is positive exactly once `n` reaches `p`.**  The
complement of `padicValNat_factorial_eq_zero_iff`: for every prime `p`,

  `0 < v_p(n!)  ↔  p ≤ n`,

i.e. `p` divides `n!` iff `n ≥ p`.  Together with the zero-locus statement this gives the
sharp dichotomy governing the lowest step of Legendre's staircase. -/
theorem padicValNat_factorial_pos_iff (p n : ℕ) (hp : p.Prime) :
    0 < padicValNat p n.factorial ↔ p ≤ n := by
  rw [Nat.pos_iff_ne_zero, ne_eq, padicValNat_factorial_eq_zero_iff p n hp, Nat.not_lt]

/-! ## Kummer's theorem in additive digit-sum form, and its divisibility corollaries

The general Legendre identity `(p-1)·v_p(n!) = n − s_p(n)` above is precisely the
starting point flagged in `sub_one_mul_padicValNat_factorial_digitSum`.  Applying
it to `(m+n)!`, `m!`, `n!` and combining with the valuation-additive factorisation
`C(m+n,m)·m!·n! = (m+n)!` yields the **carry-free additive form of Kummer's
theorem**:

    (p−1)·v_p(C(m+n,m)) + s_p(m+n) = s_p(m) + s_p(n).

Mathlib carries Kummer only in the *truncated-subtraction* shape
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`
(`(p-1)·v_p = s_p(k)+s_p(n) − s_p(n+k)` in ℕ).  The additive rearrangement below
is subtraction-free, which is what makes the two genuinely new corollaries fall
out cleanly and which Mathlib does **not** state:

  * `digitSum_add_le` — base-`p` **digit-sum subadditivity** `s_p(m+n) ≤ s_p(m)+s_p(n)`
    (the base-`p` Hamming-weight triangle inequality; not in Mathlib), and
  * `not_dvd_choose_iff_digitSum_add` / `dvd_choose_iff_digitSum_lt` — the sharp
    **digit-sum criterion for whether a prime divides a binomial coefficient**:
    `p ∤ C(m+n,m) ↔ s_p(m+n) = s_p(m)+s_p(n)` (no carries), and its negation
    `p ∣ C(m+n,m) ↔ s_p(m+n) < s_p(m)+s_p(n)` (at least one carry). -/

/-- **Kummer's theorem, carry-free additive form.**  For every prime `p`,

  `(p − 1)·v_p(C(m+n, m)) + s_p(m+n) = s_p(m) + s_p(n)`.

The subtraction-free rearrangement of Kummer's theorem.  Proof: the factorisation
`C(m+n,m)·m!·n! = (m+n)!` makes `v_p` additive (`padicValNat.mul`, all factors
nonzero), so `v_p((m+n)!) = v_p(C) + v_p(m!) + v_p(n!)`; scaling by `p−1` and
substituting the Legendre identity `(p−1)·v_p(k!) = k − s_p(k)`
(`sub_one_mul_padicValNat_factorial_digitSum`) for each of `m`, `n`, `m+n`, the
`k` terms cancel and `omega` clears the (bounded) natural subtractions using
`s_p(k) ≤ k`. -/
theorem sub_one_mul_padicValNat_choose_add_digitSum (p m n : ℕ) (hp : p.Prime) :
    (p - 1) * padicValNat p ((m + n).choose m) + digitSum p (m + n)
      = digitSum p m + digitSum p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hstep : (m + n).choose m * m.factorial * n.factorial = (m + n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    simpa [Nat.add_sub_cancel_left] using h
  have hcne : (m + n).choose m ≠ 0 := (Nat.choose_pos (Nat.le_add_right m n)).ne'
  have hmf : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hnf : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hval : padicValNat p (m + n).factorial
      = padicValNat p ((m + n).choose m) + padicValNat p m.factorial
        + padicValNat p n.factorial := by
    rw [← hstep, padicValNat.mul (mul_ne_zero hcne hmf) hnf, padicValNat.mul hcne hmf]
  have h2 : (p - 1) * padicValNat p ((m + n).choose m)
      + (p - 1) * padicValNat p m.factorial
      + (p - 1) * padicValNat p n.factorial
      = (p - 1) * padicValNat p (m + n).factorial := by
    rw [hval, Nat.mul_add, Nat.mul_add]
  have leg_m := sub_one_mul_padicValNat_factorial_digitSum p m hp
  have leg_n := sub_one_mul_padicValNat_factorial_digitSum p n hp
  have leg_mn := sub_one_mul_padicValNat_factorial_digitSum p (m + n) hp
  have hsm : digitSum p m ≤ m := by simpa [digitSum] using Nat.digit_sum_le p m
  have hsn : digitSum p n ≤ n := by simpa [digitSum] using Nat.digit_sum_le p n
  have hsmn : digitSum p (m + n) ≤ m + n := by
    simpa [digitSum] using Nat.digit_sum_le p (m + n)
  omega

/-- **Base-`p` digit-sum subadditivity** (the base-`p` Hamming-weight triangle
inequality): for every prime `p`,

  `s_p(m + n) ≤ s_p(m) + s_p(n)`.

Adding never *increases* the total base-`p` digit sum — carries only merge digits.
Immediate from the carry-free Kummer identity: the shortfall
`s_p(m)+s_p(n) − s_p(m+n)` equals `(p−1)·v_p(C(m+n,m)) ≥ 0`.  Not a named Mathlib
lemma. -/
theorem digitSum_add_le (p m n : ℕ) (hp : p.Prime) :
    digitSum p (m + n) ≤ digitSum p m + digitSum p n := by
  have h := sub_one_mul_padicValNat_choose_add_digitSum p m n hp
  omega

/-- **Kummer's theorem, division form (gallery `digitSum` shape).**  For every
prime `p`,

  `v_p(C(m+n, m)) = (s_p(m) + s_p(n) − s_p(m+n)) / (p − 1)`,

the exact count of base-`p` carries when adding `m` and `n`.  Obtained from the
additive form by transposing `s_p(m+n)` and dividing by `p − 1 > 0`
(`Nat.mul_div_cancel_left`); the numerator subtraction is exact by
`digitSum_add_le`.  Mathlib states only the multiplied subtraction form, not this
division form. -/
theorem padicValNat_choose_eq_div (p m n : ℕ) (hp : p.Prime) :
    padicValNat p ((m + n).choose m)
      = (digitSum p m + digitSum p n - digitSum p (m + n)) / (p - 1) := by
  have hadd := sub_one_mul_padicValNat_choose_add_digitSum p m n hp
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have hmul : (p - 1) * padicValNat p ((m + n).choose m)
      = digitSum p m + digitSum p n - digitSum p (m + n) := by omega
  rw [← hmul, Nat.mul_div_cancel_left _ hp1]

/-- **Digit-sum criterion for a prime NOT dividing a binomial coefficient.**  For
every prime `p`,

  `p ∤ C(m+n, m) ↔ s_p(m+n) = s_p(m) + s_p(n)`,

i.e. `p` misses the binomial exactly when adding `m` and `n` in base `p` produces
no carries (Kummer's carry count is `0`).  The `p = 2` case is the classical
"`C(m+n,m)` is odd iff the binary supports of `m` and `n` are disjoint".  Derived
from the additive Kummer identity via `dvd_iff_padicValNat_ne_zero` and
`p − 1 > 0`.  Not a named Mathlib lemma. -/
theorem not_dvd_choose_iff_digitSum_add (p m n : ℕ) (hp : p.Prime) :
    ¬ (p ∣ (m + n).choose m) ↔ digitSum p (m + n) = digitSum p m + digitSum p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcne : (m + n).choose m ≠ 0 := (Nat.choose_pos (Nat.le_add_right m n)).ne'
  have hadd := sub_one_mul_padicValNat_choose_add_digitSum p m n hp
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  rw [dvd_iff_padicValNat_ne_zero hcne, not_not]
  constructor
  · intro h
    rw [h] at hadd
    omega
  · intro h
    have hz : (p - 1) * padicValNat p ((m + n).choose m) = 0 := by omega
    rcases Nat.mul_eq_zero.mp hz with h1 | h2
    · omega
    · exact h2

/-- **Digit-sum criterion for a prime dividing a binomial coefficient.**  The
complement of `not_dvd_choose_iff_digitSum_add`: for every prime `p`,

  `p ∣ C(m+n, m) ↔ s_p(m+n) < s_p(m) + s_p(n)`,

i.e. `p` divides the binomial exactly when adding `m` and `n` in base `p` produces
at least one carry.  Strictness comes from pairing the non-divisibility criterion
with digit-sum subadditivity `s_p(m+n) ≤ s_p(m)+s_p(n)`. -/
theorem dvd_choose_iff_digitSum_lt (p m n : ℕ) (hp : p.Prime) :
    p ∣ (m + n).choose m ↔ digitSum p (m + n) < digitSum p m + digitSum p n := by
  have hle := digitSum_add_le p m n hp
  rw [← not_iff_not, not_dvd_choose_iff_digitSum_add p m n hp, not_lt]
  omega

-- The numerical content (v_p(n!) = (n - s_p(n))/(p-1) for many p, n) is certified
-- independently in `research/problems/erdos-729-oq-02/verify_legendre_general.py`
-- (no Lean `decide` on `Nat.digits`, which is well-founded and does not reduce
-- reliably in the kernel).

/-! ### Digit-sum invariance under multiplication by the base, and the central
binomial coefficient

The base-`p` digit sum is unchanged by multiplying the argument by `p` (a trailing
zero is appended, contributing `0` to the sum).  This general lemma
(`digitSum_base_mul`) is a Mathlib gap in the same family as `digitSum_add_le`.
Specialising the Kummer criteria to `m = n` gives the `p`-adic valuation and
non-divisibility criteria for the **central binomial coefficient** `C(2n, n)`, and
— combining the two — the classical fact that `C(2n, n)` is even for every `n ≥ 1`. -/

/-- **A positive number has positive digit sum.**  For `n ≠ 0` the base-`p` digit
list is non-empty and its most significant digit is nonzero, so `s_p(n) > 0`. -/
theorem digitSum_pos {p n : ℕ} (hn : n ≠ 0) : 0 < digitSum p n := by
  have hne : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (p.digits n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p hn
  have hmem : (p.digits n).getLast hne ∈ p.digits n := List.getLast_mem hne
  have hle : (p.digits n).getLast hne ≤ (p.digits n).sum := List.le_sum_of_mem hmem
  show 0 < (p.digits n).sum
  omega

/-- **Digit-sum invariance under multiplication by the base.**  For every base
`p > 1`, `s_p(p · n) = s_p(n)`: writing `p · n` in base `p` appends a least-significant
digit `0` (`(p·n) % p = 0`, `(p·n) / p = n`), which does not change the digit sum.
A general-purpose lemma not named in Mathlib. -/
theorem digitSum_base_mul (p n : ℕ) (hp : 1 < p) :
    digitSum p (p * n) = digitSum p n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitSum]
  · have hpn : 0 < p * n := Nat.mul_pos (by omega) hn
    show (p.digits (p * n)).sum = (p.digits n).sum
    rw [Nat.digits_def' hp hpn, Nat.mul_mod_right,
      Nat.mul_div_cancel_left n (show 0 < p by omega)]
    simp

/-- **Kummer's theorem for the central binomial coefficient (division form).**
For every prime `p`,

  `v_p(C(2n, n)) = (2·s_p(n) − s_p(2n)) / (p − 1)`,

the base-`p` carry count of `n + n`.  The `m = n` case of `padicValNat_choose_eq_div`
applied to `Nat.centralBinom n = (2n).choose n`. -/
theorem padicValNat_centralBinom_eq_div (p n : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.centralBinom n)
      = (2 * digitSum p n - digitSum p (2 * n)) / (p - 1) := by
  have h := padicValNat_choose_eq_div p n n hp
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul n, h]
  congr 1
  omega

/-- **Digit-sum criterion for a prime not dividing the central binomial coefficient.**
For every prime `p`,

  `p ∤ C(2n, n) ↔ s_p(2n) = 2·s_p(n)`,

i.e. `p` misses `C(2n, n)` exactly when doubling `n` in base `p` produces no carries.
The `m = n` case of `not_dvd_choose_iff_digitSum_add`. -/
theorem not_dvd_centralBinom_iff (p n : ℕ) (hp : p.Prime) :
    ¬ (p ∣ Nat.centralBinom n) ↔ digitSum p (2 * n) = 2 * digitSum p n := by
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul n,
    not_dvd_choose_iff_digitSum_add p n n hp]
  constructor <;> intro hh <;> omega

/-- **The central binomial coefficient is even for `n ≥ 1`.**  A classical fact,
here a corollary of the base-`p` machinery at `p = 2`: `2 ∤ C(2n, n)` would force
`s_2(2n) = 2·s_2(n)` (no-carry criterion), but `s_2(2n) = s_2(n)` (digit-sum base
invariance), so `s_2(n) = 0`, hence `n = 0`. -/
theorem centralBinom_even (n : ℕ) (hn : 0 < n) : 2 ∣ Nat.centralBinom n := by
  by_contra h
  rw [not_dvd_centralBinom_iff 2 n Nat.prime_two,
    digitSum_base_mul 2 n (by norm_num)] at h
  have hpos : 0 < digitSum 2 n := digitSum_pos (p := 2) (by omega)
  omega

/-! ### The sharp 2-adic valuation of the central binomial coefficient

Kummer's carry count, at `p = 2`, collapses to the classical closed form
`v_2(C(2n, n)) = s_2(n)` — the number of `1`s in the binary expansion of `n`.
The key input is that doubling adds a trailing binary `0`, so `s_2(2n) = s_2(n)`
(`digitSum_base_mul`), which cancels one of the two `s_2(n)` terms in the `m = n`
Kummer identity.  The general-`p` exact form is recorded first. -/

/-- **Kummer for the central binomial coefficient (exact multiplied form).**
For every prime `p`,

  `(p − 1)·v_p(C(2n, n)) + s_p(2n) = 2·s_p(n)`,

the subtraction-free `m = n` specialisation of
`sub_one_mul_padicValNat_choose_add_digitSum`.  Rearranged, the base-`p` carry
count of `n + n` is `(2·s_p(n) − s_p(2n))/(p − 1)` (cf. `padicValNat_centralBinom_eq_div`),
but the multiplied form avoids the natural-number division. -/
theorem sub_one_mul_padicValNat_centralBinom (p n : ℕ) (hp : p.Prime) :
    (p - 1) * padicValNat p (Nat.centralBinom n) + digitSum p (2 * n)
      = 2 * digitSum p n := by
  have hadd := sub_one_mul_padicValNat_choose_add_digitSum p n n hp
  have hc : Nat.centralBinom n = (n + n).choose n := by
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
  rw [hc, two_mul n]
  omega

/-- **The sharp 2-adic valuation of the central binomial coefficient.**

  `v_2(C(2n, n)) = s_2(n)`,

i.e. `C(2n, n)` is divisible by exactly `2` to the power of the number of `1`s in
the binary expansion of `n`.  This is the classical Kummer specialisation: doubling
`n` in base 2 never carries (`s_2(2n) = s_2(n)`), so the `m = n` carry count of
`n + n` equals `s_2(n)`.  Not a named Mathlib lemma. -/
theorem padicValNat_centralBinom_two_eq_digitSum (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = digitSum 2 n := by
  have h := sub_one_mul_padicValNat_centralBinom 2 n Nat.prime_two
  rw [digitSum_base_mul 2 n (by norm_num : 1 < 2)] at h
  omega

/-- **The central binomial valuation is positive for `n ≥ 1`** (sharpened evenness).
`1 ≤ v_2(C(2n, n))` because `s_2(n) ≥ 1` for `n ≠ 0` (`digitSum_pos`).  Refines
`centralBinom_even` from "divisible by 2" to an explicit valuation lower bound. -/
theorem one_le_padicValNat_centralBinom_two {n : ℕ} (hn : 0 < n) :
    1 ≤ padicValNat 2 (Nat.centralBinom n) := by
  rw [padicValNat_centralBinom_two_eq_digitSum]
  exact digitSum_pos (by omega)

/-- **The base-2 digit sum of a power of two is `1`.**  Its binary expansion is a
single leading `1` followed by zeros.  By induction: `s_2(2^{k+1}) = s_2(2·2^k)
= s_2(2^k)` via `digitSum_base_mul`, with base case `s_2(1) = 1`. -/
theorem digitSum_two_pow (k : ℕ) : digitSum 2 (2 ^ k) = 1 := by
  induction k with
  | zero =>
      show (Nat.digits 2 (2 ^ 0)).sum = 1
      rw [pow_zero, Nat.digits_def' (by norm_num : 1 < 2) (by norm_num : 0 < 1)]
      simp
  | succ k ih =>
      rw [pow_succ, mul_comm (2 ^ k) 2, digitSum_base_mul 2 (2 ^ k) (by norm_num : 1 < 2), ih]

/-- **At a power of two the central binomial coefficient carries exactly one `2`.**

  `v_2(C(2·2^k, 2^k)) = 1`,

the `n = 2^k` slice of `padicValNat_centralBinom_two_eq_digitSum` (`s_2(2^k) = 1`).
Equivalently, `C(2^{k+1}, 2^k) ≡ 2 (mod 4)` — it is even but not a multiple of 4. -/
theorem padicValNat_centralBinom_two_pow (k : ℕ) :
    padicValNat 2 (Nat.centralBinom (2 ^ k)) = 1 := by
  rw [padicValNat_centralBinom_two_eq_digitSum, digitSum_two_pow]

/-! ### The power-of-two characterization: `s_2(n) = 1 ↔ n` is a power of two

`digitSum_two_pow` gives one direction (`s_2(2^k) = 1`); this block supplies the
**converse** `s_2(n) = 1 → ∃ k, n = 2^k`, upgrading the one-way fact to a full
characterization.  The converse is the honest content: a positive integer has a single
`1`-bit in binary exactly when it is a power of two.  It sharpens
`padicValNat_centralBinom_two_pow` from a one-directional value to the **iff**
`v_2(C(2n, n)) = 1 ↔ n` is a power of two — the exact locus where the central binomial
coefficient is even but not a multiple of `4`. -/

/-- **A positive integer with base-2 digit sum `1` is a power of two.**  The converse of
`digitSum_two_pow`.  By strong induction on `n` via the digit recurrence
`s_2(n) = n % 2 + s_2(n / 2)`: if `n` is even the leading bit is `0`, so `s_2(n/2) = 1`
and `n/2 = 2^j` by induction, whence `n = 2^{j+1}`; if `n` is odd the leading bit is `1`,
forcing `s_2(n/2) = 0`, hence `n/2 = 0` (`digitSum_pos`) and `n = 1 = 2^0`. -/
theorem digitSum_two_eq_one_imp_two_pow :
    ∀ n : ℕ, 0 < n → digitSum 2 n = 1 → ∃ k, n = 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hs
    have hrec : digitSum 2 n = n % 2 + digitSum 2 (n / 2) := by
      show (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n / 2)).sum
      rw [Nat.digits_def' (by norm_num : 1 < 2) hn]; simp
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · -- `n` even: leading bit `0`, so `s_2(n/2) = 1` and we recurse.
      have hd1 : digitSum 2 (n / 2) = 1 := by omega
      have hpos : 0 < n / 2 := by omega
      have hlt : n / 2 < n := Nat.div_lt_self hn (by norm_num)
      obtain ⟨j, hj⟩ := ih (n / 2) hlt hpos hd1
      have hn2 : n = 2 * (n / 2) := by omega
      exact ⟨j + 1, by rw [hn2, hj, pow_succ, Nat.mul_comm]⟩
    · -- `n` odd: leading bit `1` uses up the whole digit sum, so `s_2(n/2) = 0`.
      have hd0 : digitSum 2 (n / 2) = 0 := by omega
      have hz : n / 2 = 0 := by
        by_contra hne
        have := digitSum_pos (p := 2) hne
        omega
      exact ⟨0, by rw [pow_zero]; omega⟩

/-- **The base-2 digit sum is `1` iff `n` is a power of two** (`n ≥ 1`).  Combines
`digitSum_two_pow` (`⇐`) with `digitSum_two_eq_one_imp_two_pow` (`⇒`): among positive
integers, `s_2(n) = 1` characterizes the powers of two exactly. -/
theorem digitSum_two_eq_one_iff (n : ℕ) (hn : 0 < n) :
    digitSum 2 n = 1 ↔ ∃ k, n = 2 ^ k := by
  refine ⟨digitSum_two_eq_one_imp_two_pow n hn, ?_⟩
  rintro ⟨k, rfl⟩
  exact digitSum_two_pow k

/-- **`v_2(C(2n, n)) = 1 ↔ n` is a power of two** (`n ≥ 1`).  The sharp form of
`padicValNat_centralBinom_two_pow`: the central binomial coefficient `C(2n, n)` is even
but not divisible by `4` exactly when `n` is a power of two, since
`v_2(C(2n, n)) = s_2(n)` (`padicValNat_centralBinom_two_eq_digitSum`) and `s_2(n) = 1`
characterizes the powers of two. -/
theorem padicValNat_centralBinom_two_eq_one_iff (n : ℕ) (hn : 0 < n) :
    padicValNat 2 (Nat.centralBinom n) = 1 ↔ ∃ k, n = 2 ^ k := by
  rw [padicValNat_centralBinom_two_eq_digitSum]
  exact digitSum_two_eq_one_iff n hn

/-! ### The carry-count form: bridging `digitSum` to Mathlib's `padicValNat_choose'`

The Kummer identities above are phrased through the base-`p` **digit sum**.  Mathlib's
`padicValNat_choose'` phrases the same valuation through the explicit **carry count**
`#{ i ∈ Ico 1 b | pⁱ ≤ m % pⁱ + n % pⁱ }`.  The two theorems below make the link
explicit — answering the standing `carries`-form follow-up.  The first is Kummer's
theorem in its most recognisable shape ("digit-sum defect `= (p−1)·(number of
carries)`"); the second refines the no-carry criterion into a position-by-position
statement. -/

/-- **Kummer's theorem: digit-sum defect `= (p − 1)·(carry count)`.**  For every prime
`p` and any bound `b > log_p (m + n)`,

  `s_p(m) + s_p(n) − s_p(m+n) = (p − 1) · #{ i ∈ Ico 1 b | pⁱ ≤ m % pⁱ + n % pⁱ }`.

Bridges the gallery `digitSum` machinery (`sub_one_mul_padicValNat_choose_add_digitSum`)
to Mathlib's explicit carry-count form of Kummer's theorem (`padicValNat_choose'`):
the base-`p` digit-sum shortfall of `m + n` is exactly `p − 1` times the number of
carries produced when adding `m` and `n`. -/
theorem digitSum_defect_eq_sub_one_mul_carries (p m n : ℕ) {b : ℕ} (hp : p.Prime)
    (hnb : Nat.log p (m + n) < b) :
    digitSum p m + digitSum p n - digitSum p (m + n)
      = (p - 1) *
          ((Finset.Ico 1 b).filter (fun i => p ^ i ≤ m % p ^ i + n % p ^ i)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : (m + n).choose m = (n + m).choose m := by rw [Nat.add_comm]
  have hcar : padicValNat p ((m + n).choose m)
      = ((Finset.Ico 1 b).filter (fun i => p ^ i ≤ m % p ^ i + n % p ^ i)).card := by
    rw [hcomm]
    exact padicValNat_choose' (p := p) (n := n) (k := m) (b := b)
      (by rw [Nat.add_comm n m]; exact hnb)
  have hadd := sub_one_mul_padicValNat_choose_add_digitSum p m n hp
  have hle := digitSum_add_le p m n hp
  rw [hcar] at hadd
  omega

/-- **Kummer no-carry criterion, position-by-position form.**  For every prime `p`
and any bound `b > log_p (m + n)`,

  `p ∤ C(m+n, m) ↔ ∀ i ∈ Ico 1 b, m % pⁱ + n % pⁱ < pⁱ`,

i.e. `p` misses the binomial coefficient exactly when adding `m` and `n` in base `p`
carries at **no** position.  The explicit-carry refinement of the digit-sum criterion
`not_dvd_choose_iff_digitSum_add`, obtained from `padicValNat_choose'` via
`Finset.filter_eq_empty_iff`. -/
theorem not_dvd_choose_iff_no_carries (p m n : ℕ) {b : ℕ} (hp : p.Prime)
    (hnb : Nat.log p (m + n) < b) :
    ¬ p ∣ (m + n).choose m ↔ ∀ i ∈ Finset.Ico 1 b, m % p ^ i + n % p ^ i < p ^ i := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcne : (m + n).choose m ≠ 0 := (Nat.choose_pos (Nat.le_add_right m n)).ne'
  have hcomm : (m + n).choose m = (n + m).choose m := by rw [Nat.add_comm]
  have hcar : padicValNat p ((m + n).choose m)
      = ((Finset.Ico 1 b).filter (fun i => p ^ i ≤ m % p ^ i + n % p ^ i)).card := by
    rw [hcomm]
    exact padicValNat_choose' (p := p) (n := n) (k := m) (b := b)
      (by rw [Nat.add_comm n m]; exact hnb)
  rw [dvd_iff_padicValNat_ne_zero hcne, not_not, hcar, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  simp only [not_le]

#check @padicValNat_factorial_eq_div
#check @legendre_digit_sum_identity
#check @sub_one_mul_padicValNat_factorial_digitSum
#check @sub_one_dvd_sub_digitSum
#check @sub_one_mul_padicValNat_factorial_le
#check @padicValNat_factorial_le_div
#check @modEq_digitSum
#check @padicValNat_factorial_eq_zero_iff
#check @padicValNat_factorial_pos_iff
#check @sub_one_mul_padicValNat_choose_add_digitSum
#check @digitSum_add_le
#check @padicValNat_choose_eq_div
#check @not_dvd_choose_iff_digitSum_add
#check @dvd_choose_iff_digitSum_lt
#check @digitSum_pos
#check @digitSum_base_mul
#check @padicValNat_centralBinom_eq_div
#check @not_dvd_centralBinom_iff
#check @centralBinom_even
#check @digitSum_defect_eq_sub_one_mul_carries
#check @not_dvd_choose_iff_no_carries
#check @sub_one_mul_padicValNat_centralBinom
#check @padicValNat_centralBinom_two_eq_digitSum
#check @one_le_padicValNat_centralBinom_two
#check @digitSum_two_pow
#check @padicValNat_centralBinom_two_pow
#check @digitSum_two_eq_one_imp_two_pow
#check @digitSum_two_eq_one_iff
#check @padicValNat_centralBinom_two_eq_one_iff

end Erdos729Legendre
