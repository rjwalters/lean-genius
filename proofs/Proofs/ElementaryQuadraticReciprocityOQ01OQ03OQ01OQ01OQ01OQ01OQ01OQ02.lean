/-
  The Second Supplement to Quadratic Reciprocity, the Zolotarev Way
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02)

  Open Question (the listed follow-up of the full-odd Zolotarev–Frobenius entry,
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01, open question #3 — the SAME open
  question whose `a = -1` half is the sibling first supplement
  oq-…-oq-01):
  "Recover the supplementary laws (a = -1 and a = 2) for odd n as values of
  signRingHom, completing the dictionary between permutation signs on ℤ/n and
  the full Jacobi symbol."

  This file delivers the SECOND supplement, a = 2:

      J(2 | n) = (-1) ^ ((n² - 1) / 8)      for every odd n > 0,

  and identifies it as the sign of the DOUBLING permutation x ↦ 2·x on ℤ/n
  (the Zolotarev permutation of the unit 2).

  ## The route, and an honest comparison with the first supplement

  The first supplement (`a = -1`) was special: negation `x ↦ -x` is an
  INVOLUTION, so its sign could be read off by a self-contained parity count of
  its fixed points — a genuinely elementary, Gauss-free computation.

  Doubling `x ↦ 2·x` is NOT an involution, so that shortcut is unavailable; an
  independent evaluation of its sign would amount to reproving Gauss's lemma for
  the prime 2.  Instead we route through the parent identity
  `sign(ringMulPerm 2) = J(2 | n)` (the full odd-modulus Zolotarev–Frobenius
  theorem, which already encapsulates Gauss's lemma) and Mathlib's
  `jacobiSym.at_two : J(2 | b) = χ₈ b`.

  The genuinely NEW mathematical content is therefore the closed-form POWER
  formula for the octic character,

      χ₈ n = (-1) ^ ((n² - 1) / 8)      for odd n,

  which Mathlib does *not* provide (it offers only the case-split
  `χ₈_nat_eq_if_mod_eight` on `n mod 8`).  Establishing this power form is a
  clean parity computation: for odd `n = 2m + 1`,

      (n² - 1) / 8 = m(m+1)/2  = T_m   (the m-th triangular number),

  whose parity is governed by `m mod 4`, equivalently by `n mod 8`
  (`n ≡ ±1 mod 8 ⇒ even ⇒ +1`, `n ≡ ±3 mod 8 ⇒ odd ⇒ -1`).  We prove the parity
  fact `exponent_parity` from the single arithmetic identity `m² ≡ m (mod 2)`
  (i.e. `m² % 4 = m % 2`), after which `omega` closes everything.

  Content (all 0 sorries, 0 axioms):
  * `exponent_parity`        — `((n²-1)/8) % 2 = (n mod 8 ∈ {1,7} ? 0 : 1)`.
  * `neg_one_pow_exponent`   — `(-1)^((n²-1)/8) = (n mod 8 ∈ {1,7} ? 1 : -1)`.
  * `chi8_eq_neg_one_pow`    — the NEW power formula `χ₈ n = (-1)^((n²-1)/8)`.
  * `jacobiSym_two`          — THE SECOND SUPPLEMENT: `J(2|n) = (-1)^((n²-1)/8)`.
  * `sign_ringMulPerm_two`   — the doubling-permutation sign equals the supplement.
  * `sign_doubling`          — the canonical (hypothesis-free) doubling statement.
  * `legendreSym_two`        — Euler's criterion at an odd prime: `(2/p) = (-1)^((p²-1)/8)`.

  As with the first supplement, the *value* is classical (Mathlib has
  `jacobiSym.at_two`); what is new here is (i) the explicit `(-1)^((n²-1)/8)`
  power form of `χ₈` and (ii) its reading as the sign of Zolotarev's doubling
  permutation — exactly in the spirit of Zolotarev (1872) / Frobenius (1914).

  References:
  - Zolotarev (1872): Nouvelle démonstration de la loi de réciprocité de Legendre
  - Frobenius (1914): generalization to Jacobi symbols / composite moduli
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01

set_option maxHeartbeats 800000

namespace ZolotarevSecondSupplement

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm)

variable {n : ℕ} [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE PARITY OF THE EXPONENT (n² - 1) / 8
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Parity of the supplement exponent.**  For odd `n`, the exponent `(n²-1)/8`
    is even exactly when `n ≡ ±1 (mod 8)`:

        ((n² - 1) / 8) % 2 = (if n % 8 = 1 ∨ n % 8 = 7 then 0 else 1).

    Since `n = 2m+1` gives `(n²-1)/8 = m(m+1)/2`, the parity is that of the
    triangular number `T_m`, governed by `m mod 4` ↔ `n mod 8`.  With the seed
    `sq_mod_four`, `omega` discharges the whole linear/modular computation. -/
theorem exponent_parity (hodd : Odd n) :
    ((n ^ 2 - 1) / 8) % 2 = (if n % 8 = 1 ∨ n % 8 = 7 then 0 else 1) := by
  obtain ⟨m, rfl⟩ := hodd
  -- `(n²-1)/8 = m(m+1)/2`, the m-th triangular number.
  have hkey : ((2 * m + 1) ^ 2 - 1) / 8 = m * (m + 1) / 2 := by
    have h1 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [hkey]
  -- the parity of `T_m = m(m+1)/2` is governed by `m mod 4`.
  obtain ⟨j, s, hs, rfl⟩ : ∃ j s, s < 4 ∧ m = 4 * j + s :=
    ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 4).symm⟩
  interval_cases s
  · rw [show (4 * j + 0) * (4 * j + 0 + 1) = 2 * (8 * j ^ 2 + 2 * j) by ring]
    split_ifs <;> omega
  · rw [show (4 * j + 1) * (4 * j + 1 + 1) = 2 * (8 * j ^ 2 + 6 * j + 1) by ring]
    split_ifs <;> omega
  · rw [show (4 * j + 2) * (4 * j + 2 + 1) = 2 * (8 * j ^ 2 + 10 * j + 3) by ring]
    split_ifs <;> omega
  · rw [show (4 * j + 3) * (4 * j + 3 + 1) = 2 * (8 * j ^ 2 + 14 * j + 6) by ring]
    split_ifs <;> omega

/-- The supplement value as a signed power: `(-1)^((n²-1)/8)` is `+1` for
    `n ≡ ±1 (mod 8)` and `-1` for `n ≡ ±3 (mod 8)`. -/
theorem neg_one_pow_exponent (hodd : Odd n) :
    (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) = if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  have hpar := exponent_parity hodd
  rcases Nat.even_or_odd ((n ^ 2 - 1) / 8) with h | h
  · rw [h.neg_one_pow, if_pos]
    have : ((n ^ 2 - 1) / 8) % 2 = 0 := Nat.even_iff.mp h
    by_contra hcon; rw [if_neg hcon] at hpar; omega
  · rw [h.neg_one_pow, if_neg]
    have : ((n ^ 2 - 1) / 8) % 2 = 1 := Nat.odd_iff.mp h
    intro hcon; rw [if_pos hcon] at hpar; omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE POWER FORMULA FOR THE OCTIC CHARACTER χ₈  (new in Mathlib's terms)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Closed-form power formula for `χ₈`.**  For every odd `n`,

        χ₈ n = (-1) ^ ((n² - 1) / 8).

    Mathlib supplies only the mod-8 case split `χ₈_nat_eq_if_mod_eight`; this is
    the explicit power form, the octic analogue of `ZMod.χ₄_eq_neg_one_pow`. -/
theorem chi8_eq_neg_one_pow (hodd : Odd n) :
    ZMod.χ₈ (n : ZMod 8) = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, neg_one_pow_exponent hodd, if_neg (by simp [Nat.odd_iff.mp hodd])]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE SECOND SUPPLEMENT TO QUADRATIC RECIPROCITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Second supplementary law of quadratic reciprocity, via Zolotarev.**
    For every odd `n > 0`,

        J(2 | n) = (-1) ^ ((n² - 1) / 8).

    Proof: `jacobiSym.at_two` rewrites `J(2 | n)` as the octic character `χ₈ n`,
    and `chi8_eq_neg_one_pow` puts that in closed power form. -/
theorem jacobiSym_two (hodd : Odd n) :
    jacobiSym 2 n = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_two hodd, chi8_eq_neg_one_pow hodd]

/-- **The doubling-permutation sign (unit form).**  For odd `n` and any unit
    `u : (ℤ/n)ˣ` whose underlying residue is `2`, the sign of the Zolotarev
    permutation `x ↦ u·x` (i.e. doubling `x ↦ 2·x`) on the whole ring `ℤ/n` is

        sign(ringMulPerm u) = (-1) ^ ((n² - 1) / 8).

    This reads the second supplement off Zolotarev's doubling permutation,
    via the parent full-odd Frobenius identity `sign(ringMulPerm u) = J(2 | n)`. -/
theorem sign_ringMulPerm_two (hodd : Odd n) (u : (ZMod n)ˣ) (hu : (u : ZMod n) = 2) :
    (Equiv.Perm.sign (ringMulPerm u) : ℤ) = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  have hA : ((2 : ℤ) : ZMod n) = (u : ZMod n) := by rw [hu]; norm_cast
  rw [ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd hodd u 2 hA, jacobiSym_two hodd]

/-- **The doubling-permutation sign (canonical form).**  For odd `n`, `2` is a
    unit (coprime to `n`); the sign of the canonical doubling permutation
    `x ↦ 2·x` on `ℤ/n` is `(-1)^((n²-1)/8)`.  This is the hypothesis-free
    Zolotarev statement of the second supplement. -/
theorem sign_doubling (hodd : Odd n) :
    (Equiv.Perm.sign (ringMulPerm (ZMod.unitOfCoprime 2
        ((Nat.prime_two.coprime_iff_not_dvd).mpr
          (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd))))) : ℤ)
      = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) :=
  sign_ringMulPerm_two hodd _ (by rw [ZMod.coe_unitOfCoprime]; norm_cast)

/-- **Euler's criterion / second supplement for the Legendre symbol.**  For an
    odd prime `p`,

        (2 / p) = (-1) ^ ((p² - 1) / 8),

    obtained by specializing the Jacobi-symbol supplement to a prime modulus. -/
theorem legendreSym_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_two ((Fact.out : p.Prime).odd_of_ne_two hp)]

end ZolotarevSecondSupplement

#check @ZolotarevSecondSupplement.chi8_eq_neg_one_pow
#check @ZolotarevSecondSupplement.jacobiSym_two
#check @ZolotarevSecondSupplement.sign_doubling
#check @ZolotarevSecondSupplement.legendreSym_two
