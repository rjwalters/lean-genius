/-
  Erdős Problem #729 — OQ-02 follow-up: the elementary 2-adic digit-sum bound.

  Companion to `Erdos729Problem.lean` (the parent's `legendre_for_two`) and
  `Erdos729LegendreMultinomial.lean`.

  ## The question

  The parent entry (OQ-02) establishes Legendre's identity for `p = 2`,
  `v₂(n!) = n − s₂(n)` with `s₂(n) = (Nat.digits 2 n).sum` the binary digit sum.
  The parent's headline number-theoretic content — the Erdős (1968) constraint
  that `a! · b! ∣ n!` forces `a + b ≤ n + O(log n)` — is carried in the main file
  only by the DEEP axiom `erdos_1968_classical`. Yet the exact 2-adic *core* of
  that constraint is entirely elementary and needs no axiom:

        a! · b! ∣ n!   ⟹   v₂(a!) + v₂(b!) ≤ v₂(n!)
                       ⟹   (a − s₂ a) + (b − s₂ b) ≤ n − s₂ n
                       ⟹   a + b ≤ n + s₂(a) + s₂(b).                        (★)

  Inequality (★) is a correct, *sharp*, subtraction-free quantitative statement
  (no `O(·)` fudge): the excess `a + b − n` is bounded by the total number of
  1-bits in `a` and `b`. Since `s₂(m) ≤ ⌊log₂ m⌋ + 1`, (★) immediately yields the
  recognisable logarithmic shape `a + b ≤ n + (⌊log₂ a⌋ + 1) + (⌊log₂ b⌋ + 1)`.

  ## What this file proves (0 axioms / 0 sorries / 0 native_decide)

  * `v2_factorial`          — `v₂(n!) = n − s₂(n)` (Legendre at `p = 2`).
  * `v2_add_le_of_dvd`      — the valuation-monotonicity step
                              `v₂(a!) + v₂(b!) ≤ v₂(n!)` from `a!·b! ∣ n!`.
  * `erdos_two_adic_bound`  — the digit-sum bound (★), axiom-free.
  * `digitSum_two_le_log`   — `s₂(m) ≤ Nat.log 2 m + 1` (digit sum ≤ bit count).
  * `erdos_two_adic_bound_log` — the logarithmic corollary of (★).

  None of these are named Mathlib lemmas. Bearer lemmas (Mathlib pin `v4.26.0`):
  `sub_one_mul_padicValNat_factorial`, `Nat.factorization_prime_le_iff_dvd`,
  `Nat.factorization_mul`, `Nat.factorization_def`, `Nat.digit_sum_le`,
  `Nat.digits_len`, `Nat.digits_lt_base`, `List.sum_le_card_nsmul`.
-/

import Mathlib

namespace Erdos729DigitSum

open Nat

/-- **Legendre's identity at `p = 2`, subtraction form.**
`v₂(n!) = n − s₂(n)` with `s₂(n) = (Nat.digits 2 n).sum`. Discharged from
Mathlib's `sub_one_mul_padicValNat_factorial`, whose `p − 1` factor is `1`
at `p = 2`. -/
theorem v2_factorial (n : ℕ) :
    padicValNat 2 (n !) = n - (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [show (2 - 1 : ℕ) = 1 from rfl, one_mul] at h
  exact h

/-- **Valuation-monotonicity step.** If `a! · b! ∣ n!` then the 2-adic valuations
add up subordinately: `v₂(a!) + v₂(b!) ≤ v₂(n!)`. Proof via the factorization
order: `factorization` is monotone under divisibility and additive under products,
and agrees with `padicValNat` at the prime `2`. -/
theorem v2_add_le_of_dvd (n a b : ℕ) (h : a ! * b ! ∣ n !) :
    padicValNat 2 (a !) + padicValNat 2 (b !) ≤ padicValNat 2 (n !) := by
  have hab : a ! * b ! ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)
  have hn : n ! ≠ 0 := Nat.factorial_ne_zero n
  have key := (Nat.factorization_prime_le_iff_dvd hab hn).mpr h 2 Nat.prime_two
  rw [Nat.factorization_mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b),
      Finsupp.add_apply,
      Nat.factorization_def (a !) Nat.prime_two,
      Nat.factorization_def (b !) Nat.prime_two,
      Nat.factorization_def (n !) Nat.prime_two] at key
  exact key

/-- **The 2-adic digit-sum bound (★), axiom-free.**
If `a! · b! ∣ n!` then `a + b ≤ n + s₂(a) + s₂(b)`, where `s₂(m)` is the number of
1-bits of `m`. The excess `a + b − n` never exceeds the total 1-bit count of the
two parts — the exact 2-adic content of Erdős's 1968 constraint, with no `O(·)`. -/
theorem erdos_two_adic_bound (n a b : ℕ) (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  have hv := v2_add_le_of_dvd n a b h
  rw [v2_factorial, v2_factorial, v2_factorial] at hv
  have ha := Nat.digit_sum_le 2 a
  have hb := Nat.digit_sum_le 2 b
  have hnn := Nat.digit_sum_le 2 n
  omega

/-- **Digit sum ≤ bit count.** For `m ≥ 1`, the binary digit sum is bounded by the
number of binary digits: `s₂(m) ≤ ⌊log₂ m⌋ + 1`. Each base-2 digit is `< 2`,
hence `≤ 1`, so the sum is at most the length, which is `Nat.log 2 m + 1`. -/
theorem digitSum_two_le_log (m : ℕ) (hm : m ≠ 0) :
    (Nat.digits 2 m).sum ≤ Nat.log 2 m + 1 := by
  have hlen : (Nat.digits 2 m).length = Nat.log 2 m + 1 :=
    Nat.digits_len 2 m (by norm_num) hm
  have hbound : (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length • 1 :=
    List.sum_le_card_nsmul (Nat.digits 2 m) 1 fun x hx => by
      have := Nat.digits_lt_base (by norm_num) hx
      omega
  have hsmul : (Nat.digits 2 m).length • (1 : ℕ) = (Nat.digits 2 m).length := by simp
  rw [hsmul] at hbound
  omega

/-- **Logarithmic corollary of (★).** If `a! · b! ∣ n!` with `a, b ≥ 1` then
`a + b ≤ n + (⌊log₂ a⌋ + 1) + (⌊log₂ b⌋ + 1)` — the recognisable `n + O(log n)`
shape of Erdős's bound, here with explicit constants and no axiom. -/
theorem erdos_two_adic_bound_log (n a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.log 2 a + 1) + (Nat.log 2 b + 1) := by
  have hmain := erdos_two_adic_bound n a b h
  have hla := digitSum_two_le_log a ha
  have hlb := digitSum_two_le_log b hb
  omega

-- ----------------------------------------------------------------------------
-- The honest UNIFORM real-logarithmic Erdős (1968) bound, axiom-free.
--
-- The parent file carries the classical bound only through the axiom
-- `erdos_1968_classical`, stated as `∀ n a b, a!b! ∣ n! → ∃ C>0, a+b ≤ n+C·log n`.
-- That statement is defective on two counts:
--   * it is UNSOUND at `n ∈ {0,1}` — e.g. `n=0, a=b=1`: `1!·1! ∣ 0!` holds, yet
--     `a+b = 2 ≤ 0 + C·log 0 = 0` is false for every `C` (Real.log 0 = 0); and
--   * with `C` chosen per-instance INSIDE the `∀`, it is VACUOUS for `n ≥ 2`
--     (take `C = (a+b)/log n`), so it does not express Erdős's actual content.
-- The mathematically meaningful statement puts a SINGLE uniform `C` outside the
-- quantifiers.  We prove exactly that, axiom-free, with the explicit constant
-- `C = 4 / log 2`, valid for all `n ≥ 2`.  This is the correct replacement for
-- the parent's `erdos_1968_classical`.
-- ----------------------------------------------------------------------------

/-- **`⌊log₂ n⌋ · log 2 ≤ log n`.**  Real-logarithm form of `2^⌊log₂ n⌋ ≤ n`:
take `Real.log` of `2^(Nat.log 2 n) ≤ n` and use `Real.log_pow`. -/
theorem natLog_two_mul_log_two_le_log (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2n : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hpow
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n := by positivity
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log n := Real.log_le_log hpos h2n
  rwa [Real.log_pow] at hlog

/-- **Erdős (1968), uniform real-logarithmic form — axiom-free.**  There is a
    single constant `C = 4 / log 2 > 0` such that for every `n ≥ 2` and all
    `a, b` with `a! · b! ∣ n!`,
        `a + b ≤ n + C · log n`.
    This is the honest, non-vacuous statement of the classical bound (uniform
    `C`, no small-`n` unsoundness), derived entirely from the elementary 2-adic
    digit-sum bound `erdos_two_adic_bound_log`. -/
theorem erdos_1968_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ n a b : ℕ, 2 ≤ n → a ! * b ! ∣ n ! →
      (a + b : ℝ) ≤ n + C * Real.log n := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 / Real.log 2, by positivity, ?_⟩
  intro n a b hn hdvd
  -- log n ≥ log 2 > 0
  have hlogn2 : Real.log 2 ≤ Real.log n := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact Real.log_le_log (by norm_num) h2n
  have hlognpos : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogn2
  -- a ≤ n and b ≤ n from the divisibility
  have han : a ≤ n := by
    by_contra hc
    push_neg at hc
    have hd : a ! ∣ n ! := (dvd_mul_right (a !) (b !)).trans hdvd
    have hle : a ! ≤ n ! := Nat.le_of_dvd (Nat.factorial_pos n) hd
    have hlt : n ! < a ! := (Nat.factorial_lt (by omega)).mpr hc
    omega
  have hbn : b ≤ n := by
    by_contra hc
    push_neg at hc
    have hd : b ! ∣ n ! := (dvd_mul_left (b !) (a !)).trans hdvd
    have hle : b ! ≤ n ! := Nat.le_of_dvd (Nat.factorial_pos n) hd
    have hlt : n ! < b ! := (Nat.factorial_lt (by omega)).mpr hc
    omega
  -- Reduce the RHS constant to a multiple of L := log n / log 2
  have hL : (4 / Real.log 2) * Real.log n = 4 * (Real.log n / Real.log 2) := by ring
  have hL1 : (1 : ℝ) ≤ Real.log n / Real.log 2 := (one_le_div hlog2).mpr hlogn2
  rw [hL]
  set L : ℝ := Real.log n / Real.log 2 with hLdef
  -- Case a = 0 or b = 0: a + b ≤ n directly
  rcases Nat.eq_zero_or_pos a with ha0 | ha1
  · subst ha0
    have hb' : (b : ℝ) ≤ n := by exact_mod_cast hbn
    have : (0 : ℝ) ≤ 4 * L := by positivity
    push_cast; linarith
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    have ha' : (a : ℝ) ≤ n := by exact_mod_cast han
    have : (0 : ℝ) ≤ 4 * L := by positivity
    push_cast; linarith
  -- Main case a, b ≥ 1: elementary bound + logarithm bridge
  have hmain := erdos_two_adic_bound_log n a b (by omega) (by omega) hdvd
  have hla : Nat.log 2 a ≤ Nat.log 2 n := Nat.log_mono_right han
  have hlb : Nat.log 2 b ≤ Nat.log 2 n := Nat.log_mono_right hbn
  have hnat : a + b ≤ n + 2 * Nat.log 2 n + 2 := by omega
  have hcast : (a : ℝ) + b ≤ (n : ℝ) + 2 * (Nat.log 2 n : ℝ) + 2 := by exact_mod_cast hnat
  -- ⌊log₂ n⌋ ≤ L
  have hlogdiv : (Nat.log 2 n : ℝ) ≤ L := by
    rw [hLdef, le_div_iff₀ hlog2]
    exact natLog_two_mul_log_two_le_log n (by omega)
  -- assemble:  a+b ≤ n + 2·⌊log₂ n⌋ + 2 ≤ n + 2L + 2L = n + 4L
  linarith

end Erdos729DigitSum
