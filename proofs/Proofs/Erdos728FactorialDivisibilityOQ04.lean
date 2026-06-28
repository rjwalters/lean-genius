/-
# Erdős #728 → #729: the elementary logarithmic barrier (prime-2 / Legendre form)

Research artifact for `erdos-728-factorial-divisibility-oq-04`:
"How do the techniques of the #728 resolution extend to related problems like #729?"

Erdős #728 (resolved affirmatively, Jan 2026, GPT-5.2 + Aristotle; see
`Erdos728FactorialDivisibility.lean` and arXiv:2601.07421) and Erdős #729 (resolved
by Barreto–Leeham with a modification of the same argument) are both about how far
the *near*-divisibility of `a! b!` into `n!` can push `a + b` beyond `n`.

The classical baseline both results break "beyond" is Erdős's elementary bound:

  if `a! b! ∣ n!` then `a + b ≤ n + O(log n)`.

Erdős's proof needs only the prime `2`.  By Legendre's formula
`v₂(m!) = m − s₂(m)` (with `s₂ m = (Nat.digits 2 m).sum` the binary digit sum),
the divisibility `a! b! ∣ n!` forces `v₂(a!) + v₂(b!) ≤ v₂(n!)`, i.e.
`(a − s₂ a) + (b − s₂ b) ≤ n − s₂ n`, hence `a + b ≤ n + s₂ a + s₂ b`, and each
binary digit sum is at most the binary length `= O(log)`.

This file formalizes that barrier exactly over `ℕ`, 0-sorry / 0-axiom, as the
verified starting point for the #729 generalization.  #729 asks for infinitely many
`a, b, n` with `a + b > n + C log n` for which the denominator of `n!/(a! b!)`
contains only primes bounded in terms of `C` — equivalently, the large-prime
valuations already satisfy `v_p(a!) + v_p(b!) ≤ v_p(n!)`, while small primes (like
the `2` used here) may fail it.  The barrier proved here is precisely the `O(log n)`
statement that #728/#729 must — and do — defeat; the technique that defeats it is
the large-prime carry analysis carried out in `Erdos728FactorialDivisibility.lean`.

This is foundational infrastructure, not a resolution of #729: it is the lower bound
the resolution surpasses, formalized in the same `padicValNat`/Legendre vocabulary
the #728 file already uses (`kappa`, `W`, Kummer carries).
-/
import Mathlib

namespace Erdos728FactorialDivisibilityOQ04

open Nat

/-- **Legendre's formula at `p = 2`, additive `ℕ` form.**  Every `m` splits as the
2-adic valuation of `m!` plus the binary digit sum of `m`:
`m = v₂(m!) + s₂(m)`.  This is `v₂(m!) = m − s₂(m)` rearranged to avoid truncated
subtraction, read off from Mathlib's `sub_one_mul_padicValNat_factorial` at `p = 2`
(where the `(p − 1)` factor is `1`). -/
theorem factorial_val_add_digitsum (m : ℕ) :
    m = padicValNat 2 (m !) + (Nat.digits 2 m).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hleg := sub_one_mul_padicValNat_factorial (p := 2) m
  have hs : (Nat.digits 2 m).sum ≤ m := Nat.digit_sum_le 2 m
  omega

/-- **The logarithmic barrier (exact Legendre/popcount form).**  If `a! · b! ∣ n!`
then `a + b ≤ n + s₂(a) + s₂(b)`, where `s₂` is the binary digit sum.  Proof: the
divisibility gives `v₂(a!) + v₂(b!) ≤ v₂(n!)`; substituting Legendre's
`m = v₂(m!) + s₂(m)` for `a`, `b`, `n` and clearing the valuations yields the bound.
Only the prime `2` is used — this is Erdős's original elementary argument. -/
theorem log_barrier {a b n : ℕ} (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmono : padicValNat 2 (a ! * b !) ≤ padicValNat 2 (n !) :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
      (dvd_trans (pow_padicValNat_dvd (p := 2) (n := a ! * b !)) h)
  rw [padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)] at hmono
  have ha := factorial_val_add_digitsum a
  have hb := factorial_val_add_digitsum b
  have hn := factorial_val_add_digitsum n
  omega

/-- The binary digit sum is at most the binary length: each base-2 digit is `< 2`,
hence `≤ 1`, so the sum is bounded by the number of digits. -/
theorem digitsum_two_le_length (m : ℕ) :
    (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length := by
  have h : (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length • 1 :=
    List.sum_le_card_nsmul (Nat.digits 2 m) 1
      (fun x hx => by have := Nat.digits_lt_base (by norm_num) hx; omega)
  simpa using h

/-- **The logarithmic barrier (explicit `O(log)` form).**  If `a! · b! ∣ n!` then
`a + b ≤ n + len₂(a) + len₂(b)`, where `len₂ m = (Nat.digits 2 m).length` is the
number of binary digits of `m` (`= ⌊log₂ m⌋ + 1` for `m > 0`).  This is the
`a + b ≤ n + O(log n)` barrier in fully explicit form; #728/#729 exhibit triples
violating it once small primes are excluded. -/
theorem log_barrier_length {a b n : ℕ} (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.digits 2 a).length + (Nat.digits 2 b).length := by
  have hbar := log_barrier h
  have ha := digitsum_two_le_length a
  have hb := digitsum_two_le_length b
  omega

#check @factorial_val_add_digitsum
#check @log_barrier
#check @log_barrier_length

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no sorryAx, no Lean.ofReduceBool.
#print axioms factorial_val_add_digitsum
#print axioms log_barrier
#print axioms digitsum_two_le_length
#print axioms log_barrier_length

end Erdos728FactorialDivisibilityOQ04
