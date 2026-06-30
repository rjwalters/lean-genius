/-
  Zolotarev's permutation-sign character (Milestone 1 of the Zolotarev route to
  quadratic reciprocity).

  Companion to `Proofs.QuadraticReciprocityAlgorithmOQ03M2`, which computed the
  sign of the grid-transpose permutation (the Zolotarev–Frobenius shuffle).  This
  file develops the *other* half of the Zolotarev route: the permutation

      mulLeft₀ a : Perm (ZMod p),   x ↦ a · x          (a ≠ 0)

  of the residues mod `p` by multiplication, and its sign as a character of the
  unit group.  Zolotarev's lemma is the statement

      legendreSym p a = sign (mulLeft₀ a)                       (Zolotarev)

  for `a` a unit mod an odd prime `p`.  Mathlib has no `Zolotarev` lemma and no
  `sign`-of-translation formula, so the content here is new.

  WHAT IS PROVED HERE (all 0 sorry / 0 axiom beyond Lean's foundational
  `propext / Classical.choice / Quot.sound`):

    * `mulLeft₀_mul`       — `mulLeft₀ (a*b) = mulLeft₀ a * mulLeft₀ b`, so
                              `a ↦ sign (mulLeft₀ a)` is multiplicative.
    * `sign_mulLeft₀_mul`  — the induced multiplicativity of the sign.
    * `sign_mulLeft₀_isSquare` — squares lie in the kernel: a quadratic residue
                              has sign `+1` (the easy inclusion of Zolotarev).
    * `sign_mulLeft₀_neg_one`   — the genuinely-new sign computation
                              `sign (mulLeft₀ (-1)) = (-1)^((p-1)/2)`, obtained
                              from Mathlib's involution-sign lemma
                              `Equiv.Perm.sign_of_pow_two_eq_one` applied to the
                              fixed-point-free-except-`0` involution `x ↦ -x`.
    * `legendreSym_neg_one_eq_sign_mulLeft₀` — **Zolotarev's lemma at `a = -1`**:
                              the first supplementary law `(-1/p) = (-1)^((p-1)/2)`
                              exhibited as a permutation sign,
                              `legendreSym p (-1) = (sign (mulLeft₀ (-1)) : ℤ)`.

  SCOPE / HONESTY.  This file proves Zolotarev's lemma for the specific unit
  `a = -1` (the first supplementary law) and the structural facts
  (multiplicativity, vanishing on squares) that the general statement rests on.
  The general case `legendreSym p a = sign (mulLeft₀ a)` for an arbitrary unit
  requires the cycle structure of a translation by a *generator* of `(ZMod p)ˣ`
  (a single `(p-1)`-cycle), which Mathlib does not provide; that is recorded as
  the remaining gap.  The `-1` case needs no such machinery because `x ↦ -x` is
  an involution, whose sign Mathlib computes from its fixed-point count.
-/
import Mathlib

namespace QuadraticReciprocityAlgorithmOQ03Zolotarev

open Equiv Equiv.Perm

variable {p : ℕ} [Fact p.Prime]

/-- Multiplication-by-a permutations compose multiplicatively:
`mulLeft₀ (a*b) = mulLeft₀ a * mulLeft₀ b` in `Perm (ZMod p)`. -/
theorem mulLeft₀_mul {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    Equiv.mulLeft₀ (a * b) (mul_ne_zero ha hb)
      = Equiv.mulLeft₀ a ha * Equiv.mulLeft₀ b hb := by
  ext x
  simp [Equiv.Perm.mul_apply, mul_assoc]

/-- The sign of the multiplication permutation is multiplicative in the
multiplier — the heart of "`a ↦ sign (mulLeft₀ a)` is a character of the units". -/
theorem sign_mulLeft₀_mul {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) :
    sign (Equiv.mulLeft₀ (a * b) (mul_ne_zero ha hb))
      = sign (Equiv.mulLeft₀ a ha) * sign (Equiv.mulLeft₀ b hb) := by
  rw [mulLeft₀_mul ha hb, map_mul]

/-- Squares lie in the kernel: the sign of multiplication by a quadratic residue
is `+1`.  This is the easy inclusion of Zolotarev's lemma — `legendreSym p a = 1`
for a square `a`. -/
theorem sign_mulLeft₀_isSquare {a : ZMod p} (ha : a ≠ 0) (hsq : IsSquare a) :
    sign (Equiv.mulLeft₀ a ha) = 1 := by
  obtain ⟨b, rfl⟩ := hsq
  have hb : b ≠ 0 := by
    rintro rfl; simp at ha
  rw [sign_mulLeft₀_mul hb hb]
  exact Int.units_mul_self _

/-- The multiplication permutation `x ↦ -x` (multiplication by `-1`) is an
involution. -/
theorem mulLeft₀_neg_one_sq (h : (-1 : ZMod p) ≠ 0) :
    Equiv.mulLeft₀ (-1 : ZMod p) h ^ 2 = 1 := by
  ext x
  simp [pow_two, Equiv.Perm.mul_apply]

/-- For an odd prime `p`, the only fixed point of `x ↦ -x` is `0`. -/
theorem fixedPoints_neg_eq (h : (-1 : ZMod p) ≠ 0) (hp : p ≠ 2) :
    Fintype.card (Function.fixedPoints (Equiv.mulLeft₀ (-1 : ZMod p) h)) = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hne : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
    simpa using hne
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · show (Equiv.mulLeft₀ (-1 : ZMod p) h) 0 = 0
    simp
  · rintro ⟨y, hy⟩
    have hy' : (Equiv.mulLeft₀ (-1 : ZMod p) h) y = y := hy
    simp only [Equiv.mulLeft₀_apply] at hy'
    have hzero : (2 : ZMod p) * y = 0 := by linear_combination -hy'
    ext
    exact (mul_eq_zero.mp hzero).resolve_left h2

/-- **Zolotarev sign computation at `-1`.**  For an odd prime `p`, the sign of the
multiplication-by-`(-1)` permutation of `ZMod p` (the involution `x ↦ -x`, free
except for the fixed point `0`) is `(-1)^((p-1)/2)`.  Mathlib has no
`sign`-of-translation lemma; this is obtained from the involution-sign formula
`sign_of_pow_two_eq_one`, which reads the sign off the fixed-point count. -/
theorem sign_mulLeft₀_neg_one (h : (-1 : ZMod p) ≠ 0) (hp : p ≠ 2) :
    sign (Equiv.mulLeft₀ (-1 : ZMod p) h) = (-1 : ℤˣ) ^ ((p - 1) / 2) := by
  rw [sign_of_pow_two_eq_one (mulLeft₀_neg_one_sq h), fixedPoints_neg_eq h hp,
      ZMod.card]

/-- **Zolotarev's lemma at `a = -1` (first supplementary law as a permutation
sign).**  For an odd prime `p`,

    legendreSym p (-1) = (sign (mulLeft₀ (-1)) : ℤ),

exhibiting the first supplementary law `(-1/p) = (-1)^((p-1)/2)` concretely as the
sign of the single explicit permutation `x ↦ -x` of `ZMod p`. -/
theorem legendreSym_neg_one_eq_sign_mulLeft₀ (h : (-1 : ZMod p) ≠ 0) (hp : p ≠ 2) :
    legendreSym p (-1)
      = ((sign (Equiv.mulLeft₀ (-1 : ZMod p) h) : ℤˣ) : ℤ) := by
  have hodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hdiv : p / 2 = (p - 1) / 2 := by
    obtain ⟨k, hk⟩ := hodd; omega
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow hp2, hdiv,
      sign_mulLeft₀_neg_one h hp, Units.val_pow_eq_pow_val]
  norm_num

end QuadraticReciprocityAlgorithmOQ03Zolotarev
