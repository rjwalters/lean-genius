/-
  Jacobi symbol `J(a | n) = 1` as a PARITY count of non-residue prime factors.

  The Jacobi symbol is the product of Legendre symbols over the prime factors of
  the (odd) modulus `n`, *taken with multiplicity*:

      `J(a | n) = ∏_{p ∣ n} (a | p)`   (each `p` repeated `vₚ(n)` times).

  When `gcd(a, n) = 1` every factor `(a | p)` is `±1`, so the whole product is a
  sign determined entirely by HOW MANY of those factors equal `-1`.  Writing
  `k = #{p ∣ n (with multiplicity) : (a | p) = -1}` we obtain the clean dichotomy

      `J(a | n) = (-1)^k`,   hence   `J(a | n) = 1  ↔  k is even`.

  This is the structural fact behind the parent entry's puzzle `J(2 | 15) = 1`
  with `2` a genuine non-residue mod `15`:  both prime factors `3` and `5` are
  non-residue witnesses (`(2|3) = (2|5) = -1`), and `2` of them is an EVEN number,
  so the two `-1`'s cancel.  This is exactly why the Jacobi symbol produces
  "false witnesses" in the Solovay–Strassen primality test: an even number of
  non-residue prime factors hides the non-residuosity of `a`.

  A subtlety the title's set-notation `#{p ∣ n}` glosses over: the count must be
  taken **with multiplicity**.  For `n = 45 = 3² · 5` the distinct bad primes are
  `{3, 5}` (count `2`, even) yet `J(2 | 45) = -1`; the multiplicity-aware count is
  `3` (odd), the list `[3, 3, 5]`.  We work with `Nat.primeFactorsList`, which
  carries multiplicity, so the statement is correct for every modulus.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Nat ZMod

namespace JacobiSymbolOQ0103

/-! ### The list of Legendre symbols over the prime factors of `n` -/

/-- The Legendre symbols `(a | p)` as `p` ranges over the prime factors of `n`
**with multiplicity**.  By definition `jacobiSym a n` is the product of this
list. -/
def legVals (a : ℤ) (n : ℕ) : List ℤ :=
  n.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a)
    (fun _ pf => prime_of_mem_primeFactorsList pf)

/-- `jacobiSym a n` is literally the product of the Legendre-symbol list. -/
theorem jacobiSym_eq_legVals_prod (a : ℤ) (n : ℕ) :
    jacobiSym a n = (legVals a n).prod := rfl

/-- When `gcd(a, n) = 1`, every Legendre symbol over a prime factor of `n` is a
genuine sign `±1` (none vanish, since no prime factor of `n` divides `a`). -/
theorem legVals_mem_eq_one_or_neg_one {a : ℤ} {n : ℕ} (cop : a.gcd n = 1)
    {x : ℤ} (hx : x ∈ legVals a n) : x = 1 ∨ x = -1 := by
  rw [legVals, List.mem_pmap] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hpp : p.Prime := prime_of_mem_primeFactorsList hp
  haveI : Fact p.Prime := ⟨hpp⟩
  apply legendreSym.eq_one_or_neg_one
  rw [Ne, intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have hn0 : n ≠ 0 := by rintro rfl; simp at hp
  have hpn : p ∣ n := ((Nat.mem_primeFactorsList hn0).mp hp).2
  have hpa : p ∣ a.natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at h
  have hdg : p ∣ Nat.gcd a.natAbs n := Nat.dvd_gcd hpa hpn
  have hcop : Nat.gcd a.natAbs n = 1 := by
    have h : Int.gcd a (n : ℤ) = Nat.gcd a.natAbs n := by
      simp [Int.gcd, Int.natAbs_natCast]
    rwa [h] at cop
  rw [hcop] at hdg
  exact hpp.one_lt.ne' (Nat.dvd_one.mp hdg)

/-! ### The product of a list of signs is `(-1)` to the number of `-1`'s -/

/-- For a list of integers each equal to `1` or `-1`, the product equals `-1`
raised to the number of entries equal to `-1`. -/
theorem prod_eq_neg_one_pow_count {L : List ℤ}
    (h : ∀ x ∈ L, x = 1 ∨ x = -1) :
    L.prod = (-1 : ℤ) ^ (L.count (-1)) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      rcases h x (List.mem_cons_self) with hx | hx
      · subst hx
        rw [List.prod_cons, ih', List.count_cons_of_ne (by decide : (1 : ℤ) ≠ -1),
          one_mul]
      · subst hx
        rw [List.prod_cons, ih', List.count_cons_self, pow_succ]
        ring

/-! ### Main results: the parity characterisation -/

/-- The number of prime factors of `n` (counted **with multiplicity**) modulo
which `a` is a quadratic non-residue, i.e. `#{p ∣ n : (a | p) = -1}`. -/
def numNonResidueFactors (a : ℤ) (n : ℕ) : ℕ := (legVals a n).count (-1)

/-- **Sign formula.** For coprime `a, n` the Jacobi symbol is `(-1)` raised to
the number of non-residue prime factors (with multiplicity). -/
theorem jacobiSym_eq_neg_one_pow (a : ℤ) (n : ℕ) (cop : a.gcd n = 1) :
    jacobiSym a n = (-1 : ℤ) ^ numNonResidueFactors a n := by
  rw [jacobiSym_eq_legVals_prod, numNonResidueFactors]
  exact prod_eq_neg_one_pow_count fun _ hx => legVals_mem_eq_one_or_neg_one cop hx

/-- **Parity characterisation of `J(a|n) = 1`.** For coprime `a, n`, the Jacobi
symbol equals `1` exactly when an EVEN number of prime factors of `n` (with
multiplicity) are non-residue witnesses.  This explains how `J(a | n)` can be
`1` while `a` is a non-residue: the `-1`'s cancel in even number. -/
theorem jacobiSym_eq_one_iff_even (a : ℤ) (n : ℕ) (cop : a.gcd n = 1) :
    jacobiSym a n = 1 ↔ Even (numNonResidueFactors a n) := by
  rw [jacobiSym_eq_neg_one_pow a n cop]
  exact neg_one_pow_eq_one_iff_even (by decide)

/-- Dually, `J(a | n) = -1` exactly when an ODD number of prime factors are
non-residue witnesses. -/
theorem jacobiSym_eq_neg_one_iff_odd (a : ℤ) (n : ℕ) (cop : a.gcd n = 1) :
    jacobiSym a n = -1 ↔ Odd (numNonResidueFactors a n) := by
  rw [jacobiSym_eq_neg_one_pow a n cop]
  constructor
  · intro hpow
    rcases Nat.even_or_odd (numNonResidueFactors a n) with he | ho
    · rw [he.neg_one_pow] at hpow; norm_num at hpow
    · exact ho
  · intro ho; exact ho.neg_one_pow

/-! ### Worked examples: multiplicity matters

`J(2 | 15) = 1` with `2` a non-residue mod `15`: an even count (`2`, primes `3, 5`)
of non-residue witnesses.  `J(2 | 45) = -1`: an odd count (`3`, list `[3,3,5]`),
showing the count genuinely needs multiplicity — the distinct-prime count `{3,5}`
is `2` (even) and would give the wrong sign. -/

/-- `J(2 | 15) = 1`, so the number of non-residue prime factors of `15` is even —
even though `2` is a genuine non-residue mod `15`. -/
theorem even_numNonResidue_two_fifteen : Even (numNonResidueFactors 2 15) :=
  (jacobiSym_eq_one_iff_even 2 15 (by decide)).mp (by norm_num)

/-- `J(2 | 45) = -1`, so the **multiplicity-aware** count for `45 = 3² · 5` is odd
(`3`), whereas the count of *distinct* bad primes `{3, 5}` is `2` (even). -/
theorem odd_numNonResidue_two_fortyfive : Odd (numNonResidueFactors 2 45) :=
  (jacobiSym_eq_neg_one_iff_odd 2 45 (by decide)).mp (by norm_num)

end JacobiSymbolOQ0103
