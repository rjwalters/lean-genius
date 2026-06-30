/-
  The squared quadratic Gauss sum `p*` is a fundamental discriminant.

  Setup (parent entry `QuadraticGaussSumSquareOQ04`): for an odd prime `p` and a
  primitive additive character `ψ : ZMod p → ℂ`, the quadratic Gauss sum
  `g = gaussSum (chiC p) ψ` satisfies

      g² = p* := (-1)^((p-1)/2) · p,            and      minpoly ℚ g = X² − p*,

  so `g` generates the unique quadratic subfield `ℚ(√p*)` of the `p`-th
  cyclotomic field `ℚ(ζ_p)`.  The parent settled *that* `ℚ(g)` is quadratic; the
  sibling `oq-01` settled the sign/reality of `g`.  This child settles the
  **arithmetic type of the discriminant** `p*` itself.

  The arithmetic engine is the *first supplement to quadratic reciprocity*
  repackaged for `p*`:

      p ≡ 1 (mod 4)  ⟹  p* =  p   (positive),
      p ≡ 3 (mod 4)  ⟹  p* = −p   (negative),

  and — the new point — in **both** cases

      p* ≡ 1 (mod 4).

  Since `|p*| = p` is prime, `p*` is squarefree; together with `p* ≡ 1 (mod 4)`
  this makes `p*` a **fundamental discriminant** (`pstar_isFundamentalDiscriminant`).
  It is therefore exactly the discriminant of the quadratic field `ℚ(√p*) = ℚ(g)`
  the Gauss sum generates — not merely a number whose square root lies there.
  (The congruence `p* ≡ 1 (mod 4)` is also the arithmetic reason that field is
  ramified only at `p`, with conductor `p` rather than `4p`; and it explains why
  the order `ℤ[g]`, of polynomial discriminant `4p*`, is the non-maximal order of
  index `2` inside the ring of integers `ℤ[(1+√p*)/2]`.)

  The capstone `gaussSum_sq_isFundamentalDiscriminant` packages this as a single
  statement about the Gauss sum: `g²` equals an integer that is a fundamental
  discriminant.  This is distinct from the sibling `oq-01` (which proves the
  real/imaginary dichotomy `g.im = 0` ⟺ `p ≡ 1 mod 4`) and from the parent
  `oq-04` (the minimal polynomial and field degree); neither identifies `p*` as a
  fundamental discriminant.

  The parent infrastructure (`chiC`, `gaussSum_sq_eq`) is re-derived here from
  Mathlib's generic `gaussSum_sq` so this file stands alone; everything from
  `pstar_eq_self` onward is the new content.
-/
import Mathlib

open scoped BigOperators
open Polynomial

namespace QuadraticGaussSumSquareOQ04OQ01

variable {p : ℕ} [Fact p.Prime]

/-! ## The character and the square formula (parent entry, re-derived) -/

/-- `ℂ`-valued quadratic character mod `p`, from the integer-valued
`quadraticChar (ZMod p)` composed with `ℤ → ℂ`. -/
noncomputable def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem chiC_ne_one (hp : p ≠ 2) : chiC p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  exact (MulChar.ringHomComp_ne_one_iff ((Int.castRingHom ℂ).injective_int)).mpr
    (quadraticChar_ne_one hchar)

theorem chiC_neg_one (hp : p ≠ 2) :
    chiC p (-1) = (-1 : ℂ) ^ ((p - 1) / 2) := by
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hq : quadraticChar (ZMod p) (-1) = (-1 : ℤ) ^ (p / 2) := by
    rw [quadraticChar_neg_one hchar, ZMod.card p]
    exact ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hodd)
  have hpe : p / 2 = (p - 1) / 2 := by obtain ⟨k, rfl⟩ := hodd; omega
  simp only [chiC, MulChar.ringHomComp_apply, hq, map_pow, map_neg, map_one]
  rw [hpe]

/-- The integer `p* = (-1)^((p-1)/2) · p`. -/
def pstar (p : ℕ) : ℤ := (-1) ^ ((p - 1) / 2) * (p : ℤ)

/-- **Square of the quadratic Gauss sum** (the parent result, restated with the
right-hand side packaged as `p*`). -/
theorem gaussSum_sq_eq (hp : p ≠ 2) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ^ 2 = (pstar p : ℂ) := by
  calc gaussSum (chiC p) ψ ^ 2
      = chiC p (-1) * (Fintype.card (ZMod p) : ℂ) :=
        gaussSum_sq (chiC_ne_one hp) chiC_isQuadratic hψ
    _ = (-1 : ℂ) ^ ((p - 1) / 2) * p := by rw [chiC_neg_one hp, ZMod.card p]
    _ = (pstar p : ℂ) := by simp only [pstar]; push_cast; ring

/-! ## The arithmetic type of `p*` -/

/-- The mod-4 case split for an odd prime: `p % 4 = 1` or `p % 4 = 3`. -/
theorem mod_four_cases (hp : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  have hpp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp)
  omega

omit [Fact p.Prime] in
/-- **First supplement, positive branch.** When `p ≡ 1 (mod 4)`, `p* = p`. -/
theorem pstar_eq_self (hp1 : p % 4 = 1) : pstar p = (p : ℤ) := by
  have he : Even ((p - 1) / 2) := by rw [Nat.even_iff]; omega
  simp [pstar, he.neg_one_pow]

omit [Fact p.Prime] in
/-- **First supplement, negative branch.** When `p ≡ 3 (mod 4)`, `p* = -p`. -/
theorem pstar_eq_neg (hp3 : p % 4 = 3) : pstar p = -(p : ℤ) := by
  have ho : Odd ((p - 1) / 2) := by rw [Nat.odd_iff]; omega
  rw [pstar, ho.neg_one_pow]; ring

/-- `|p*| = p`. -/
theorem pstar_natAbs (hp : p ≠ 2) : (pstar p).natAbs = p := by
  rcases mod_four_cases hp with h | h
  · rw [pstar_eq_self h]; simp
  · rw [pstar_eq_neg h]; simp

/-- **`p*` is positive iff `p ≡ 1 (mod 4)`.** -/
theorem pstar_pos_iff (hp : p ≠ 2) : 0 < pstar p ↔ p % 4 = 1 := by
  have hpp : p.Prime := Fact.out
  have hppos : (0 : ℤ) < p := by exact_mod_cast hpp.pos
  constructor
  · intro hpos
    rcases mod_four_cases hp with h | h
    · exact h
    · rw [pstar_eq_neg h] at hpos; linarith
  · intro h; rw [pstar_eq_self h]; exact hppos

/-- **`p*` is negative iff `p ≡ 3 (mod 4)`.** -/
theorem pstar_neg_iff (hp : p ≠ 2) : pstar p < 0 ↔ p % 4 = 3 := by
  have hpp : p.Prime := Fact.out
  have hppos : (0 : ℤ) < p := by exact_mod_cast hpp.pos
  constructor
  · intro hneg
    rcases mod_four_cases hp with h | h
    · rw [pstar_eq_self h] at hneg; linarith
    · exact h
  · intro h; rw [pstar_eq_neg h]; linarith

/-- **`p* ≡ 1 (mod 4)`** for every odd prime `p`.  This is the arithmetic heart
of the first supplement: in both residue classes `p*` lands in `1 + 4ℤ`. -/
theorem pstar_one_mod_four (hp : p ≠ 2) : pstar p ≡ 1 [ZMOD 4] := by
  rcases mod_four_cases hp with h | h
  · rw [pstar_eq_self h]; exact Int.modEq_iff_dvd.mpr (by omega)
  · rw [pstar_eq_neg h]; exact Int.modEq_iff_dvd.mpr (by omega)

/-- **`p*` is squarefree** (its absolute value `p` is prime). -/
theorem pstar_squarefree (hp : p ≠ 2) : Squarefree (pstar p) := by
  have hpp : p.Prime := Fact.out
  rw [← Int.squarefree_natAbs, pstar_natAbs hp]
  exact hpp.squarefree

/-- **`p*` is a fundamental discriminant**: it is squarefree and `≡ 1 (mod 4)`.
Equivalently, `p*` is exactly the discriminant of the quadratic field `ℚ(√p*)`
that the Gauss sum generates. -/
theorem pstar_isFundamentalDiscriminant (hp : p ≠ 2) :
    Squarefree (pstar p) ∧ pstar p ≡ 1 [ZMOD 4] :=
  ⟨pstar_squarefree hp, pstar_one_mod_four hp⟩

/-! ## The Gauss sum squares to a fundamental discriminant -/

/-- **Capstone.** The square of the quadratic Gauss sum is (the image of) an
integer `D = p*` that is a *fundamental discriminant*: squarefree and `≡ 1
(mod 4)`.  Equivalently, `g² = D` where `D` is exactly the discriminant of the
quadratic field `ℚ(g) = ℚ(√D)`. -/
theorem gaussSum_sq_isFundamentalDiscriminant (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ∃ D : ℤ, gaussSum (chiC p) ψ ^ 2 = (D : ℂ) ∧ Squarefree D ∧ D ≡ 1 [ZMOD 4] :=
  ⟨pstar p, gaussSum_sq_eq hp hψ, pstar_squarefree hp, pstar_one_mod_four hp⟩

end QuadraticGaussSumSquareOQ04OQ01
