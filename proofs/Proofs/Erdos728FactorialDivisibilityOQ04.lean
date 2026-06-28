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

/-!
## General-prime form of the barrier

Erdős's argument uses only the prime `2` because Legendre's `(p−1)·v_p(m!) = m − s_p(m)`
has the `(p−1)` factor equal to `1` there, so the valuation inequality reads off the
digit-sum bound with no division.  But the *same* derivation goes through verbatim for
**every** prime `p`: multiplying the valuation inequality `v_p(a!)+v_p(b!) ≤ v_p(n!)`
by `(p−1)` and substituting Legendre gives

  `(a − s_p a) + (b − s_p b) ≤ (n − s_p n)`,  i.e.  `a + b + s_p(n) ≤ n + s_p(a) + s_p(b)`.

This is a strict sharpening of `log_barrier` in two ways: it adds the `+ s_p(n)` term on
the small side (dropped in the classical statement), and it holds for an arbitrary prime,
so one may take the prime giving the smallest right-hand side.  The prime `2` is the
right choice for the *asymptotic* `O(log n)` bound because `s_2` is the slowest-growing
digit sum, but the inequality itself is prime-uniform.
-/

/-- **Legendre's formula at a general prime `p`, additive `ℕ` form.**
`m = (p − 1)·v_p(m!) + s_p(m)`, where `s_p m = (Nat.digits p m).sum`.  Rearranged from
Mathlib's `sub_one_mul_padicValNat_factorial` to avoid truncated subtraction. -/
theorem factorial_pval_add_digitsum (p m : ℕ) [Fact p.Prime] :
    m = (p - 1) * padicValNat p (m !) + (Nat.digits p m).sum := by
  have hleg := sub_one_mul_padicValNat_factorial (p := p) m
  have hs : (Nat.digits p m).sum ≤ m := Nat.digit_sum_le p m
  omega

/-- **The logarithmic barrier at a general prime `p` (sharp form).**  If `a! · b! ∣ n!`
then `a + b + s_p(n) ≤ n + s_p(a) + s_p(b)` for every prime `p`, where `s_p` is the
base-`p` digit sum.  Only the single prime `p` is used.  Specializing to `p = 2` and
dropping the `s_2(n)` term recovers `log_barrier`; keeping it gives a strictly stronger
bound. -/
theorem log_barrier_prime {a b n : ℕ} (p : ℕ) [Fact p.Prime] (h : a ! * b ! ∣ n !) :
    a + b + (Nat.digits p n).sum ≤ n + (Nat.digits p a).sum + (Nat.digits p b).sum := by
  have hmono : padicValNat p (a ! * b !) ≤ padicValNat p (n !) :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
      (dvd_trans (pow_padicValNat_dvd (p := p) (n := a ! * b !)) h)
  rw [padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)] at hmono
  -- Scale the valuation inequality by `(p − 1)` so Legendre substitutes cleanly.
  have hmul := Nat.mul_le_mul (le_refl (p - 1)) hmono
  rw [Nat.mul_add] at hmul
  have ha := factorial_pval_add_digitsum p a
  have hb := factorial_pval_add_digitsum p b
  have hn := factorial_pval_add_digitsum p n
  -- omega atomizes the identical `(p−1)·v_p(·!)` subterms shared by hmul/ha/hb/hn.
  omega

/-- **The classical barrier is the `p = 2` specialization.**  Recovers `log_barrier`
(`a + b ≤ n + s₂(a) + s₂(b)`) from the general-prime sharp form, discarding the
`s₂(n)` slack. -/
theorem log_barrier_of_prime {a b n : ℕ} (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := log_barrier_prime 2 h
  omega

/-!
## Multinomial / multi-factorial form of the barrier

The two-factorial barrier `log_barrier_prime` generalizes verbatim to an arbitrary
product of factorials `a₁! · … · a_k! ∣ n!` — the natural setting of multinomial
coefficients `n! / (a₁! ⋯ a_k!)`.  The valuation step is identical: `v_p` of a product
of (nonzero) factorials is the sum of the `v_p(aᵢ!)`, so the divisibility forces
`∑ᵢ v_p(aᵢ!) ≤ v_p(n!)`; scaling by `(p − 1)` and substituting Legendre
`m = (p − 1)·v_p(m!) + s_p(m)` term-by-term yields

  `∑ᵢ aᵢ + s_p(n) ≤ n + ∑ᵢ s_p(aᵢ)`   for every prime `p`.

We phrase the family as a `Multiset ℕ` (so repeated values — e.g. the central
multinomial `aᵢ = n/k` — are allowed), and give the indexed `Finset` form as a
corollary.  Specializing the multiset to `{a, b}` recovers `log_barrier_prime`.
-/

/-- **`v_p` of a product of factorials is the sum of the factorial valuations.**
`v_p(∏ᵢ aᵢ!) = ∑ᵢ v_p(aᵢ!)`.  Multiset induction off `padicValNat.mul`, using that
every factorial is nonzero so the product is too. -/
theorem padicValNat_prod_factorials (p : ℕ) [Fact p.Prime] (s : Multiset ℕ) :
    padicValNat p ((s.map (fun a => a !)).prod)
      = (s.map (fun a => padicValNat p (a !))).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    have hne : (t.map (fun a => a !)).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      intro hmem
      obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hmem
      exact absurd hb (Nat.factorial_ne_zero b)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [padicValNat.mul (Nat.factorial_ne_zero a) hne, ih]

/-- **Legendre's additive identity, summed over a multiset.**
`∑ᵢ aᵢ = (p − 1)·∑ᵢ v_p(aᵢ!) + ∑ᵢ s_p(aᵢ)`, the term-by-term lift of
`factorial_pval_add_digitsum`. -/
theorem legendre_sum_multiset (p : ℕ) [Fact p.Prime] (s : Multiset ℕ) :
    s.sum = (p - 1) * (s.map (fun a => padicValNat p (a !))).sum
            + (s.map (fun a => (Nat.digits p a).sum)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.sum_cons, Multiset.map_cons]
    have ha := factorial_pval_add_digitsum p a
    rw [Nat.mul_add]
    omega

/-- **The multinomial barrier (sharp, prime-uniform).**  For any finite family of
naturals presented as a multiset `s` (repeats allowed) with `∏ᵢ aᵢ! ∣ n!`,
`∑ᵢ aᵢ + s_p(n) ≤ n + ∑ᵢ s_p(aᵢ)` for every prime `p`.  This is the multinomial
generalization of `log_barrier_prime`; the two-factorial case is `s = {a, b}`.
Proof: the divisibility gives `∑ᵢ v_p(aᵢ!) ≤ v_p(n!)` (`padicValNat_prod_factorials`
+ `padicValNat_dvd_iff_le`); scaling by `(p − 1)` and substituting the summed Legendre
identity (`legendre_sum_multiset`) and Legendre for `n` lets `omega` finish, atomizing
the shared `(p − 1)·v_p(·!)` products. -/
theorem log_barrier_prime_multiset {p : ℕ} [Fact p.Prime] {s : Multiset ℕ} {n : ℕ}
    (h : (s.map (fun a => a !)).prod ∣ n !) :
    s.sum + (Nat.digits p n).sum
      ≤ n + (s.map (fun a => (Nat.digits p a).sum)).sum := by
  have hmono : padicValNat p ((s.map (fun a => a !)).prod) ≤ padicValNat p (n !) :=
    (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
      (dvd_trans (pow_padicValNat_dvd (p := p) (n := (s.map (fun a => a !)).prod)) h)
  rw [padicValNat_prod_factorials p s] at hmono
  have hscaled := mul_le_mul_left' hmono (p - 1)
  have hleg := legendre_sum_multiset p s
  have hn := factorial_pval_add_digitsum p n
  omega

/-- **The multinomial barrier, indexed `Finset` form.**  For a finite family
`a : ι → ℕ` over `s : Finset ι` with `∏ i ∈ s, (a i)! ∣ n!`,
`(∑ i ∈ s, a i) + s_p(n) ≤ n + ∑ i ∈ s, s_p(a i)` for every prime `p`.  This is the
form matching the multinomial coefficient `n! / ∏ᵢ (a i)!`; it is the multiset barrier
applied to `s.val.map a`. -/
theorem log_barrier_prime_finset {ι : Type*} {p : ℕ} [Fact p.Prime]
    {s : Finset ι} {a : ι → ℕ} {n : ℕ} (h : (∏ i ∈ s, (a i)!) ∣ n !) :
    (∑ i ∈ s, a i) + (Nat.digits p n).sum
      ≤ n + ∑ i ∈ s, (Nat.digits p (a i)).sum := by
  have h' : ((s.val.map a).map (fun x => x !)).prod ∣ n ! := by
    rw [Multiset.map_map]; exact h
  have key := log_barrier_prime_multiset (p := p) (s := s.val.map a) (n := n) h'
  rw [Multiset.map_map] at key
  have e1 : (∑ i ∈ s, a i) = (s.val.map a).sum := rfl
  have e2 : (∑ i ∈ s, (Nat.digits p (a i)).sum)
      = (s.val.map (fun i => (Nat.digits p (a i)).sum)).sum := rfl
  rw [e1, e2]
  simpa [Function.comp] using key

#check @factorial_val_add_digitsum
#check @factorial_pval_add_digitsum
#check @log_barrier
#check @log_barrier_prime
#check @log_barrier_length
#check @log_barrier_prime_multiset
#check @log_barrier_prime_finset

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no sorryAx, no Lean.ofReduceBool.
#print axioms factorial_val_add_digitsum
#print axioms factorial_pval_add_digitsum
#print axioms log_barrier
#print axioms log_barrier_prime
#print axioms log_barrier_of_prime
#print axioms digitsum_two_le_length
#print axioms log_barrier_length
#print axioms padicValNat_prod_factorials
#print axioms legendre_sum_multiset
#print axioms log_barrier_prime_multiset
#print axioms log_barrier_prime_finset

end Erdos728FactorialDivisibilityOQ04
