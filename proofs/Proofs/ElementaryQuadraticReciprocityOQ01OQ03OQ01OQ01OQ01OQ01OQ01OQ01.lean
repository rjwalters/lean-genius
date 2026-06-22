/-
  The First Supplement to Quadratic Reciprocity, the Zolotarev Way
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01)

  Open Question (the listed follow-up of the full-odd Zolotarev–Frobenius entry,
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01, open question #3):
  "Recover the supplementary laws (a = -1 and a = 2) for odd n as values of
  signRingHom, completing the dictionary between permutation signs on ℤ/n and
  the full Jacobi symbol."

  This file delivers the FIRST supplement, a = -1:

      J(-1 | n) = (-1) ^ ((n - 1) / 2)      for every odd n > 0.

  The mechanism is the whole point of Zolotarev's theory.  The parent proved that
  the sign of x ↦ a·x on ℤ/n IS the Jacobi symbol J(a | n) (for odd n).  Take
  a = -1: the permutation is simply NEGATION, x ↦ -x.  Negation is an INVOLUTION,
  and for odd n its only fixed point is 0 (because 2 is a unit mod n), so it is a
  product of exactly (n-1)/2 disjoint transpositions.  Hence its sign is
  (-1)^((n-1)/2) — a completely elementary parity count.  Equating the two
  evaluations of the same sign gives the first supplement, with NO appeal to
  Gauss sums, Eisenstein's lemma, or Mathlib's reciprocity machinery.

  Content (all 0 sorries, 0 axioms):
  * `ringMulPerm_neg_one_sq`     — negation is an involution: (ringMulPerm (-1))² = 1.
  * `card_fixedPoints_neg_one`   — for odd n, negation fixes exactly one point (0).
  * `sign_neg_one`               — the parity count: sign(x ↦ -x) = (-1)^((n-1)/2).
  * `jacobiSym_neg_one`          — THE FIRST SUPPLEMENT: J(-1 | n) = (-1)^((n-1)/2).
  * `jacobiSym_neg_one_eq_chi4`  — consistency with Mathlib's quadratic character χ₄.
  * `legendreSym_neg_one`        — the Legendre (Euler-criterion) special case at an
                                   odd prime: (-1 / p) = (-1)^((p-1)/2).

  The result itself is classical (Mathlib has `jacobiSym.at_neg_one`); what is new
  here is the route — the supplement read off as the parity of the negation
  permutation, exactly in the spirit of Zolotarev (1872).

  References:
  - Zolotarev (1872): Nouvelle démonstration de la loi de réciprocité de Legendre
  - Frobenius (1914): generalization to Jacobi symbols / composite moduli
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01

set_option maxHeartbeats 800000

namespace ZolotarevFirstSupplement

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm ringMulPerm_apply ringMulPerm_mul ringMulPerm_one)

variable {n : ℕ} [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: NEGATION IS AN INVOLUTION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Zolotarev permutation for `a = -1` is multiplication by `-1`, i.e. the
    negation map `x ↦ -x`.  It is an involution: `(ringMulPerm (-1))² = 1`,
    because `(-1)·(-1) = 1` in the units. -/
theorem ringMulPerm_neg_one_sq :
    (ringMulPerm (-1 : (ZMod n)ˣ)) ^ 2 = 1 := by
  rw [pow_two, ← ringMulPerm_mul, neg_one_mul, neg_neg, ringMulPerm_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: FOR ODD n, NEGATION FIXES EXACTLY ONE POINT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For odd `n`, the negation map `x ↦ -x` on `ℤ/n` has exactly one fixed point,
    namely `0`.  Indeed `-x = x` forces `2x = 0`, and `2` is a unit mod an odd `n`
    (coprime to `n`), so `x = 0`. -/
theorem card_fixedPoints_neg_one (hodd : Odd n) :
    Fintype.card (Function.fixedPoints (ringMulPerm (-1 : (ZMod n)ˣ))) = 1 := by
  rw [Fintype.card_eq_one_iff]
  -- the witness: `0` is fixed.
  have h0 : ringMulPerm (-1 : (ZMod n)ˣ) 0 = 0 := by simp
  refine ⟨⟨0, h0⟩, ?_⟩
  rintro ⟨x, hx⟩
  apply Subtype.ext
  show x = 0
  -- `hx` says `(-1) · x = x`, i.e. `-x = x`.
  have hxx : -x = x := by
    have hx' : (↑(-1 : (ZMod n)ˣ) : ZMod n) * x = x := hx
    simpa [neg_one_mul] using hx'
  -- hence `2x = 0`.
  have h2 : (2 : ZMod n) * x = 0 := by linear_combination -hxx
  -- and `2` is a unit, so `x = 0`.
  have hcop : Nat.Coprime 2 n :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd))
  have hu : IsUnit (2 : ZMod n) := by
    simpa using (ZMod.isUnit_iff_coprime 2 n).mpr hcop
  exact (hu.mul_right_eq_zero).mp h2

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE PARITY OF THE NEGATION PERMUTATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The sign of negation.**  For every odd `n`, the sign of the negation
    permutation `x ↦ -x` on `ℤ/n` is `(-1)^((n-1)/2)`.

    This is the elementary combinatorial heart of the first supplement: negation
    is an involution (`ringMulPerm_neg_one_sq`) on a set of `n` points with a
    single fixed point (`card_fixedPoints_neg_one`), so by the involution-sign
    formula it is a product of `(n-1)/2` transpositions. -/
theorem sign_neg_one (hodd : Odd n) :
    (Equiv.Perm.sign (ringMulPerm (-1 : (ZMod n)ˣ)) : ℤ) = (-1 : ℤ) ^ ((n - 1) / 2) := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one ringMulPerm_neg_one_sq,
    ZMod.card n, card_fixedPoints_neg_one hodd]
  simp [Units.val_pow_eq_pow_val]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE FIRST SUPPLEMENT TO QUADRATIC RECIPROCITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **First supplementary law of quadratic reciprocity, via Zolotarev.**
    For every odd `n > 0`,

        J(-1 | n) = (-1) ^ ((n - 1) / 2).

    Proof: by the full odd-modulus Zolotarev–Frobenius identity (the parent),
    `J(-1 | n)` equals the sign of the negation permutation `x ↦ -x`; by the
    parity count `sign_neg_one`, that sign is `(-1)^((n-1)/2)`. -/
theorem jacobiSym_neg_one (hodd : Odd n) :
    jacobiSym (-1) n = (-1 : ℤ) ^ ((n - 1) / 2) := by
  have hA : ((-1 : ℤ) : ZMod n) = ((-1 : (ZMod n)ˣ) : ZMod n) := by simp
  rw [← ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd hodd (-1) (-1) hA,
    sign_neg_one hodd]

/-- **Consistency with the quadratic character `χ₄`.**  The Zolotarev evaluation
    `(-1)^((n-1)/2)` agrees with Mathlib's character value `J(-1 | n) = χ₄ n`,
    recovering `ZMod.χ₄_eq_neg_one_pow` through the permutation-sign route. -/
theorem jacobiSym_neg_one_eq_chi4 (hodd : Odd n) :
    (-1 : ℤ) ^ ((n - 1) / 2) = ZMod.χ₄ n := by
  rw [← jacobiSym_neg_one hodd, jacobiSym.at_neg_one hodd]

/-- **Euler's criterion / first supplement for the Legendre symbol.**  For an odd
    prime `p`,

        (-1 / p) = (-1) ^ ((p - 1) / 2),

    obtained by specializing the Jacobi-symbol supplement to a prime modulus. -/
theorem legendreSym_neg_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1 : ℤ) ^ ((p - 1) / 2) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym_neg_one ((Fact.out : p.Prime).odd_of_ne_two hp)]

end ZolotarevFirstSupplement

#check @ZolotarevFirstSupplement.sign_neg_one
#check @ZolotarevFirstSupplement.jacobiSym_neg_one
#check @ZolotarevFirstSupplement.legendreSym_neg_one
