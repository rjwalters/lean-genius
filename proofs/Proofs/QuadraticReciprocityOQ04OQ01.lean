/-
Euler liars exist for every odd squarefree semiprime — and the sharp boundary
(research leaf: quadratic-reciprocity-oq-04-oq-01)

Source problem family: https://erdosproblems.com (quadratic reciprocity)
Status: original supporting theory; fully machine-checked, axiom-free.

## What this promotes

The parent entry `quadratic-reciprocity-oq-04` (`QuadraticReciprocityOQ04.lean`)
records the smallest classical *witness* that the Jacobi symbol LOSES the
residue-detection property of the Legendre symbol:

    J(2 | 15) = 1   yet   2 is not a square mod 15.

Such an `a` — a non-square with Jacobi value `+1` — is exactly an "Euler liar",
the phenomenon that forces the Solovay–Strassen primality test to make errors.
This file promotes the single numeric witness to GENERAL existence theorems, and
— crucially — pins down the SHARP BOUNDARY, correcting a natural but FALSE
over-generalization.

## The results

* `exists_euler_liar_of_two_primes` — for any two distinct odd primes `p ≠ q`
  there is an `a` with `J(a | p·q) = 1` and `a` not a square mod `p·q`.
  (Constructed by CRT: pick a non-square mod `p` and a non-square mod `q`; the
  two Jacobi/Legendre values `-1` multiply to `+1`, while non-squareness mod `p`
  already blocks squareness mod `p·q`.)  `15 = 3·5` is the base case.

* `exists_euler_liar_prime_sq` — for any odd prime `p`, the prime SQUARE `p²`
  also has an Euler liar.  Here the mechanism is different: the Jacobi character
  `J(· | p²) = (·|p)²` is *identically `1`* on the units, so ANY unit that is a
  non-square mod `p²` (e.g. the lift of a non-square mod `p`) is a liar.

* `isSquare_mod_prime_of_jacobiSym_prime_pow_odd` — **the sharp boundary.**
  For an ODD prime power `pᵏ` with `k` ODD, `J(a | pᵏ) = 1` forces `a` to be a
  square *modulo the prime `p`*.  Combined with Hensel lifting (`a` a square mod
  `p` ⟹ `a` a square mod `pᵏ` for odd `p`) this says `pᵏ`, `k` odd, has NO Euler
  liar at all — so the naive statement "every odd composite has an Euler liar"
  is FALSE (smallest counterexample `n = 27`: `J(a|27) = 1 ⟺ a` is a square mod
  27).  The Hensel step is the only piece not in Mathlib; see the note below.

## Why this is the right generalization

Liars exist iff the Jacobi kernel strictly contains the squares.  For odd `n`
the squares have index `2^ω(n)` in the units (`ω` = number of distinct primes),
while the Jacobi kernel has index `2` when `n` is not a perfect square and index
`1` when it is.  Hence liars exist iff `n` is not of the form (odd prime)^(odd
exponent): the two positive families above (`≥ 2` distinct primes; a repeated
prime factor) exhaust the odd composites that have them.

Reference: Solovay–Strassen primality test; the `J(a|n) = 1` non-squares are the
"Euler liars".

Tags: quadratic-reciprocity, jacobi-symbol, legendre-symbol, quadratic-residue,
euler-liar, solovay-strassen, number-theory
-/

import Mathlib

namespace QuadraticReciprocityOQ04OQ01

/-! ## Descent of squares along divisibility -/

/-- If `a` is a square modulo `n` and `m ∣ n`, then `a` is a square modulo `m`
(reduction `ZMod n → ZMod m` is a ring hom, hence preserves squares). -/
theorem isSquare_of_dvd {m n : ℕ} (hmn : m ∣ n) {a : ℤ}
    (h : IsSquare (a : ZMod n)) : IsSquare (a : ZMod m) := by
  have h2 := h.map (ZMod.castHom hmn (ZMod m))
  rwa [map_intCast] at h2

/-! ## Existence of Euler liars: two distinct odd primes -/

/-- **Euler liars exist for every odd squarefree semiprime.**  For distinct odd
primes `p ≠ q` there is an integer `a` with `J(a | p·q) = 1` yet `a` is not a
square modulo `p·q`.  This promotes the single classical witness `J(2|15) = 1`
(`15 = 3·5`) to the whole family of products of two distinct odd primes. -/
theorem exists_euler_liar_of_two_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) :
    ∃ a : ℤ, jacobiSym a (p * q) = 1 ∧ ¬ IsSquare (a : ZMod (p * q)) := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hchp : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hchq : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare hchp
  obtain ⟨v, hv⟩ := FiniteField.exists_nonsquare hchq
  -- an integer congruent to the non-square `u` mod `p` and the non-square `v` mod `q`
  obtain ⟨k, hkp, hkq⟩ := Nat.chineseRemainder hco u.val v.val
  have hap : ((k : ℤ) : ZMod p) = u := by
    rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff k u.val p).mpr hkp, ZMod.natCast_zmod_val]
  have haq : ((k : ℤ) : ZMod q) = v := by
    rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff k v.val q).mpr hkq, ZMod.natCast_zmod_val]
  refine ⟨(k : ℤ), ?_, ?_⟩
  · -- J(a | p·q) = J(a|p)·J(a|q) = (-1)·(-1) = 1
    have hlp : jacobiSym (k : ℤ) p = -1 :=
      ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by rw [hap]; exact hu)
    have hlq : jacobiSym (k : ℤ) q = -1 :=
      ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by rw [haq]; exact hv)
    rw [jacobiSym.mul_right, hlp, hlq]; norm_num
  · -- a square mod p·q would be a square mod p, contradicting the choice of u
    intro hsq
    have hp' : IsSquare ((k : ℤ) : ZMod p) := isSquare_of_dvd (dvd_mul_right p q) hsq
    rw [hap] at hp'
    exact hu hp'

/-! ## Existence of Euler liars: a repeated (squared) prime factor -/

/-- **Euler liars exist for every odd prime square.**  For an odd prime `p`,
there is an integer `a` with `J(a | p²) = 1` yet `a` is not a square modulo `p²`.
The Jacobi character on `ZMod p²` is identically `1` on units (it is a square),
so a non-square unit — the lift of a non-square mod `p` — is automatically a
liar.  This is the second, distinct mechanism producing liars. -/
theorem exists_euler_liar_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ a : ℤ, jacobiSym a (p ^ 2) = 1 ∧ ¬ IsSquare (a : ZMod (p ^ 2)) := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hchp : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare hchp
  have hap : ((u.val : ℤ) : ZMod p) = u := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨(u.val : ℤ), ?_, ?_⟩
  · -- J(a | p²) = (J(a|p))² = (-1)² = 1
    have hlp : jacobiSym (u.val : ℤ) p = -1 :=
      ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by rw [hap]; exact hu)
    rw [jacobiSym.pow_right, hlp]; norm_num
  · intro hsq
    have hp' : IsSquare ((u.val : ℤ) : ZMod p) :=
      isSquare_of_dvd (dvd_pow_self p two_ne_zero) hsq
    rw [hap] at hp'
    exact hu hp'

/-! ## The sharp boundary: odd prime powers with odd exponent -/

/-- **The sharp boundary.**  For an odd prime power `pᵏ` with `k` ODD,
`J(a | pᵏ) = 1` forces `a` to be a square *modulo the prime `p`*.  Since (for odd
`p`) squareness mod `p` lifts to squareness mod `pᵏ` (Hensel), `pᵏ` with `k` odd
has NO Euler liar — the reason the naive claim "every odd composite has a liar"
fails (`n = 27` is the smallest counterexample).  Only the mod-`p` conclusion is
formalized here; the lifting step is the one piece absent from Mathlib. -/
theorem isSquare_mod_prime_of_jacobiSym_prime_pow_odd
    {p : ℕ} [Fact p.Prime] {a : ℤ} {k : ℕ} (hk : Odd k)
    (h : jacobiSym a (p ^ k) = 1) : IsSquare (a : ZMod p) := by
  rw [jacobiSym.pow_right] at h
  have hkne : k ≠ 0 := by rintro rfl; simp at hk
  rcases jacobiSym.trichotomy a p with h0 | h1 | hm1
  · rw [h0, zero_pow hkne] at h; exact absurd h.symm one_ne_zero
  · exact ZMod.isSquare_of_jacobiSym_eq_one h1
  · rw [hm1, Odd.neg_one_pow hk] at h; norm_num at h

/-! ## The classical smallest witnesses, recovered from the general theorems -/

/-- The base case `n = 15 = 3·5`: an Euler liar exists, now as a consequence of
`exists_euler_liar_of_two_primes` rather than a hand computation. -/
theorem exists_euler_liar_fifteen :
    ∃ a : ℤ, jacobiSym a 15 = 1 ∧ ¬ IsSquare (a : ZMod 15) := by
  have h := exists_euler_liar_of_two_primes (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- The prime-square base case `n = 9 = 3²`. -/
theorem exists_euler_liar_nine :
    ∃ a : ℤ, jacobiSym a 9 = 1 ∧ ¬ IsSquare (a : ZMod 9) := by
  have h := exists_euler_liar_prime_sq (p := 3) (by norm_num) (by norm_num)
  simpa using h

end QuadraticReciprocityOQ04OQ01
