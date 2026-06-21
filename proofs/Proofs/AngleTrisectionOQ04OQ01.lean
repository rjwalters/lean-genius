import Mathlib

/-!
# An intrinsic prime-factorization criterion for neusis-constructible degrees

**Open question (`angle-trisection-oq-04-oq-01`)**, a slice of the tool-hierarchy
study `angle-trisection-oq-04` ("Angle Trisection: Tool Hierarchy and Generalized
Constructibility").

## Background

By Gleason's theorem (1988), a real number is *neusis-constructible* (constructible
with a marked ruler — the tool that trisects angles and duplicates the cube) iff the
degree `[ℚ(α) : ℚ]` is a **2-3 number**: it divides some `2^a · 3^b`.  The parent
entry `AngleTrisectionOQ04` encodes this as

  `IsTwoThreeNumber d := 0 < d ∧ ∃ a b, d ∣ 2^a · 3^b`

and verifies membership for many specific `d` by exhibiting witnesses `a, b`.

## What this file proves

The existential definition is replaced by an **intrinsic, witness-free criterion**:
a positive `d` is a 2-3 number **iff every prime factor of `d` is `2` or `3`** — i.e.
the 2-3 numbers are exactly the *3-smooth* numbers.

  `isTwoThreeNumber_iff :`
  `  IsTwoThreeNumber d ↔ 0 < d ∧ ∀ p, p.Prime → p ∣ d → p = 2 ∨ p = 3`.

The forward direction is the easy "prime divides `2^a·3^b`" argument; the backward
direction is a strong induction on `d` peeling off `Nat.minFac` (the headline
`exists_dvd_of_primes`).  From the criterion the structural theory of the
neusis-constructible degrees falls out with no witness bookkeeping:

* **closure under divisors** (`isTwoThreeNumber_of_dvd`), **products**
  (`isTwoThreeNumber_mul`), and **least common multiples** (`isTwoThreeNumber_lcm`);
* a **uniform obstruction** (`not_isTwoThreeNumber_of_prime`): every prime `≠ 2, 3`
  fails, instantly recovering `5, 7, 11 ∉` and any `d` with such a factor
  (`ten_not_isTwoThreeNumber`, `fifteen_not_isTwoThreeNumber`);
* the **geometry-facing form** (`isNeusisConstructible_iff`) and the
  trisection witness `degree 3` passing the criterion (`trisection_degree_neusis`).

The point: deciding neusis-constructibility of a degree no longer requires *finding*
`a, b`; one just inspects the prime factorization of `d`.

## Honest scope

This is the **number-theoretic / structural** layer characterizing the 2-3 numbers
themselves.  It is `0`-axiom and self-contained (the predicate is re-stated verbatim
from the parent).  It does **not** re-derive Gleason's field-theoretic equivalence
(degree ↔ neusis construction), which the parent states as the modelling assumption;
nor does it touch the Pierpont-prime polygon criterion (`...-oq-04-oq-03`) or the
multi-fold origami gap (`...-oq-04-oq-04`).

No `axiom`, no `sorry`, no `native_decide`.
-/

namespace NeusisDegreeCharacterization

/-- A natural number is a **2-3 number** if it divides some `2^a · 3^b`.  By
Gleason's theorem these are exactly the degrees of neusis-constructible numbers
(constructible with a marked ruler).  Restated verbatim from `AngleTrisectionOQ04`
to keep this development self-contained. -/
def IsTwoThreeNumber (d : ℕ) : Prop :=
  0 < d ∧ ∃ a b : ℕ, d ∣ 2 ^ a * 3 ^ b

/-- **Backward / hard direction of the criterion.**  If every prime factor of a
positive `d` is `2` or `3`, then `d` divides some `2^a · 3^b`.  Proved by strong
induction: peel off the smallest prime factor `p = d.minFac ∈ {2, 3}`, apply the
hypothesis to `d / p`, and re-absorb the factor `p` into the exponent. -/
theorem exists_dvd_of_primes :
    ∀ d : ℕ, 0 < d → (∀ p : ℕ, p.Prime → p ∣ d → p = 2 ∨ p = 3) →
      ∃ a b : ℕ, d ∣ 2 ^ a * 3 ^ b := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd h
    by_cases hd1 : d = 1
    · exact ⟨0, 0, by simp [hd1]⟩
    · have hp : (d.minFac).Prime := Nat.minFac_prime hd1
      have hpd : d.minFac ∣ d := Nat.minFac_dvd d
      obtain ⟨e, he⟩ := hpd
      have he_pos : 0 < e := by
        rcases Nat.eq_zero_or_pos e with rfl | h'
        · simp at he; omega
        · exact h'
      have he_lt : e < d := by
        rw [he]; exact (Nat.lt_mul_iff_one_lt_left he_pos).mpr hp.one_lt
      have hed : e ∣ d := ⟨d.minFac, by rw [mul_comm]; exact he⟩
      have he_primes : ∀ q : ℕ, q.Prime → q ∣ e → q = 2 ∨ q = 3 :=
        fun q hq hqe => h q hq (hqe.trans hed)
      obtain ⟨a, b, hab⟩ := ih e he_lt he_pos he_primes
      rcases h _ hp (Nat.minFac_dvd d) with h2 | h3
      · refine ⟨a + 1, b, ?_⟩
        have hdvd : (2 : ℕ) * e ∣ 2 * (2 ^ a * 3 ^ b) := mul_dvd_mul_left 2 hab
        have heq : (2 : ℕ) ^ (a + 1) * 3 ^ b = 2 * (2 ^ a * 3 ^ b) := by ring
        rw [he, h2, heq]; exact hdvd
      · refine ⟨a, b + 1, ?_⟩
        have hdvd : (3 : ℕ) * e ∣ 3 * (2 ^ a * 3 ^ b) := mul_dvd_mul_left 3 hab
        have heq : (2 : ℕ) ^ a * 3 ^ (b + 1) = 3 * (2 ^ a * 3 ^ b) := by ring
        rw [he, h3, heq]; exact hdvd

/-- **The intrinsic criterion.**  A positive `d` is a 2-3 number iff every prime
dividing `d` is `2` or `3`.  Equivalently: the neusis-constructible degrees are
exactly the *3-smooth* numbers.  This replaces the existential witness `∃ a b` by a
finite, decidable inspection of the prime factorization of `d`. -/
theorem isTwoThreeNumber_iff (d : ℕ) :
    IsTwoThreeNumber d ↔ 0 < d ∧ ∀ p : ℕ, p.Prime → p ∣ d → p = 2 ∨ p = 3 := by
  constructor
  · rintro ⟨hd, a, b, hab⟩
    refine ⟨hd, fun p hp hpd => ?_⟩
    have hpab : p ∣ 2 ^ a * 3 ^ b := hpd.trans hab
    rcases hp.dvd_mul.mp hpab with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow h3))
  · rintro ⟨hd, h⟩
    exact ⟨hd, exists_dvd_of_primes d hd h⟩

/-- **Uniform obstruction.**  Any prime other than `2` or `3` is not a 2-3 number,
hence is not a neusis-constructible degree.  One lemma supersedes all the parent's
individual `n_not_two_three` results. -/
theorem not_isTwoThreeNumber_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (h3 : p ≠ 3) : ¬ IsTwoThreeNumber p := by
  rw [isTwoThreeNumber_iff]
  rintro ⟨-, hall⟩
  rcases hall p hp dvd_rfl with rfl | rfl
  · exact h2 rfl
  · exact h3 rfl

/-- `5` is not a 2-3 number (instance of the uniform obstruction). -/
theorem five_not_isTwoThreeNumber : ¬ IsTwoThreeNumber 5 :=
  not_isTwoThreeNumber_of_prime (by norm_num) (by norm_num) (by norm_num)

/-- `7` is not a 2-3 number (so the heptagon's trisection-style obstruction is
visible directly from the factor `7`). -/
theorem seven_not_isTwoThreeNumber : ¬ IsTwoThreeNumber 7 :=
  not_isTwoThreeNumber_of_prime (by norm_num) (by norm_num) (by norm_num)

/-- `11` is not a 2-3 number. -/
theorem eleven_not_isTwoThreeNumber : ¬ IsTwoThreeNumber 11 :=
  not_isTwoThreeNumber_of_prime (by norm_num) (by norm_num) (by norm_num)

/-- **Closure under divisors.**  A divisor of a neusis-constructible degree is again
neusis-constructible (a quadratic/cubic sub-tower of a 2-3 tower is a 2-3 tower). -/
theorem isTwoThreeNumber_of_dvd {d e : ℕ} (hd : IsTwoThreeNumber d) (hpos : 0 < e)
    (hed : e ∣ d) : IsTwoThreeNumber e := by
  rw [isTwoThreeNumber_iff] at hd ⊢
  exact ⟨hpos, fun p hp hpe => hd.2 p hp (hpe.trans hed)⟩

/-- **Closure under products** (witness-free re-derivation of the parent's
`two_three_mul`). -/
theorem isTwoThreeNumber_mul {d e : ℕ} (hd : IsTwoThreeNumber d)
    (he : IsTwoThreeNumber e) : IsTwoThreeNumber (d * e) := by
  rw [isTwoThreeNumber_iff] at hd he ⊢
  refine ⟨Nat.mul_pos hd.1 he.1, fun p hp hpde => ?_⟩
  rcases hp.dvd_mul.mp hpde with h | h
  · exact hd.2 p hp h
  · exact he.2 p hp h

/-- **Closure under least common multiples.**  This is the natural "join" of two
neusis-constructible degrees and is *not* immediate from the existential definition
(it needs the prime-factor criterion). -/
theorem isTwoThreeNumber_lcm {d e : ℕ} (hd : IsTwoThreeNumber d)
    (he : IsTwoThreeNumber e) : IsTwoThreeNumber (Nat.lcm d e) := by
  rw [isTwoThreeNumber_iff] at hd he ⊢
  have hpos : 0 < Nat.lcm d e :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd.1.ne' he.1.ne')
  refine ⟨hpos, fun p hp hpl => ?_⟩
  have hlcm_dvd : Nat.lcm d e ∣ d * e :=
    Nat.lcm_dvd (dvd_mul_right d e) (dvd_mul_left e d)
  rcases hp.dvd_mul.mp (hpl.trans hlcm_dvd) with h | h
  · exact hd.2 p hp h
  · exact he.2 p hp h

/-- `10 = 2·5` is not a 2-3 number: the factor `5` is the obstruction, exhibited
directly from the criterion (no search for `a, b`). -/
theorem ten_not_isTwoThreeNumber : ¬ IsTwoThreeNumber 10 := by
  rw [isTwoThreeNumber_iff]
  rintro ⟨-, h⟩
  have := h 5 (by norm_num) (by norm_num)
  omega

/-- `15 = 3·5` is not a 2-3 number. -/
theorem fifteen_not_isTwoThreeNumber : ¬ IsTwoThreeNumber 15 := by
  rw [isTwoThreeNumber_iff]
  rintro ⟨-, h⟩
  have := h 5 (by norm_num) (by norm_num)
  omega

/-- `12 = 2²·3` *is* a 2-3 number, with the explicit witness `2^2 · 3^1`. -/
theorem twelve_isTwoThreeNumber : IsTwoThreeNumber 12 :=
  ⟨by norm_num, 2, 1, by norm_num⟩

/-- Neusis-constructibility of a degree, as in the parent: a real `α` whose minimal
polynomial has degree `d` is neusis-constructible iff `d` is a 2-3 number. -/
def IsNeusisConstructible (_α : ℝ) (d : ℕ) : Prop :=
  IsTwoThreeNumber d

/-- **Geometry-facing criterion.**  A degree-`d` real is neusis-constructible iff
every prime factor of `d` is `2` or `3` — the marked-ruler analogue of the
Gauss–Wantzel prime-factor test for compass constructibility. -/
theorem isNeusisConstructible_iff (α : ℝ) (d : ℕ) :
    IsNeusisConstructible α d ↔ 0 < d ∧ ∀ p : ℕ, p.Prime → p ∣ d → p = 2 ∨ p = 3 :=
  isTwoThreeNumber_iff d

/-- **Trisection witness.**  The degree-`3` extension realizing `cos 20° = cos(π/9)`
passes the intrinsic criterion (its only prime factor is `3`), so trisecting the
`60°` angle is neusis-constructible. -/
theorem trisection_degree_neusis :
    IsNeusisConstructible (Real.cos (Real.pi / 9)) 3 := by
  rw [isNeusisConstructible_iff]
  refine ⟨by norm_num, fun p hp hpd => ?_⟩
  exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd)

end NeusisDegreeCharacterization
