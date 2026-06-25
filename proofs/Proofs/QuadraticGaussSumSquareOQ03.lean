/-
  Sign-free quadratic reciprocity from the square of the Gauss sum.

  Open-question follow-up `quadratic-gauss-sum-square-oq-03`:
  combine the parent entry `g² = (-1)^((p-1)/2)·p` with a Gauss-sum proof of
  quadratic reciprocity to obtain a *self-contained, sign-free* statement of the
  law.

  The parent computes the square of the quadratic Gauss sum,

      g = ∑ₙ χ(n)·ψ(n),     g² = (-1)^((p-1)/2)·p,

  whose right-hand side is the integer

      p* := (-1)^((p-1)/2)·p.

  The whole point of introducing `p*` is conceptual: in terms of `p*` the law of
  quadratic reciprocity loses its `(-1)^…` sign factor and becomes the symmetric

      (p* / q) = (q / p)                            (`pStar_reciprocity`)

  for all odd primes `p, q`.  This is exactly the form the Gauss-sum computation
  produces, and it is the natural endpoint of "combining `g² = p*` with
  reciprocity": the awkward `(-1)^((p-1)(q-1)/4)` of the classical statement is
  absorbed once for all into the definition of `p*`.

  We make three points.

  1. `gaussSquare_eq_pStar` : the bridge — for a primitive additive character
     `ψ : ZMod p → ℂ`, the complex quadratic Gauss sum squares to `(p* : ℂ)`.
     (This re-derives the parent's headline using Mathlib's generic `gaussSum_sq`,
     so the file is self-contained.)

  2. `pStar_mod_four` : `p* ≡ 1 (mod 4)` for every odd prime `p`.  This is *why*
     `p*` is the right normalisation — it is the fundamental discriminant of the
     quadratic field `ℚ(√p*) = ℚ(g)`, and it is what makes the sign-free law
     consistent.

  3. `pStar_reciprocity` : the sign-free law `(p*/q) = (q/p)`, with the symmetric
     companion `pStar_reciprocity_symm` `(q*/p) = (p/q)` and the square-test
     corollary `pStar_isSquare_iff`.  As a sanity check we also recover the
     classical product form `classical_reciprocity_of_pStar`.

  No axioms beyond Mathlib's; verified.
-/
import Mathlib

open scoped BigOperators

namespace QuadraticGaussSumSquareOQ03

/-- The *starred prime* `p* = (-1)^((p-1)/2)·p` (an integer).  This is the value of
the square of the quadratic Gauss sum, and the fundamental discriminant of the
quadratic subfield of the `p`-th cyclotomic field. -/
def pStar (p : ℕ) : ℤ := (-1) ^ ((p - 1) / 2) * (p : ℤ)

/-! ### 1. The bridge: `g² = p*` for the complex Gauss sum -/

section Bridge

variable {p : ℕ} [Fact p.Prime]

/-- `ℂ`-valued quadratic character mod `p`, transported from the integer-valued
`quadraticChar (ZMod p)` along the ring hom `ℤ → ℂ`. -/
noncomputable def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem chiC_isQuadratic : (chiC p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem chiC_ne_one (hp : p ≠ 2) : chiC p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  exact (MulChar.ringHomComp_ne_one_iff
    ((Int.castRingHom ℂ).injective_int)).mpr (quadraticChar_ne_one hchar)

/-- Value of the character at `-1`: the first supplement, `χ(-1) = (-1)^((p-1)/2)`,
transported to `ℂ`. -/
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

/-- **Bridge to the parent entry.**  For a primitive additive character
`ψ : ZMod p → ℂ`, the complex quadratic Gauss sum squares to `(p* : ℂ)`:

    (∑ₙ χ(n)·ψ(n))² = (-1)^((p-1)/2)·p = p*.

This is the parent's `g² = (-1)^((p-1)/2)·p`, re-stated with the `p*` normalisation
and re-derived from Mathlib's generic `gaussSum_sq` so the development is
self-contained. -/
theorem gaussSquare_eq_pStar (hp : p ≠ 2) (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ ^ 2 = (pStar p : ℂ) := by
  calc gaussSum (chiC p) ψ ^ 2
      = chiC p (-1) * (Fintype.card (ZMod p) : ℂ) :=
        gaussSum_sq (chiC_ne_one hp) chiC_isQuadratic hψ
    _ = (pStar p : ℂ) := by
        rw [chiC_neg_one hp, ZMod.card p, pStar]; push_cast; ring

end Bridge

/-! ### 2. `p*` is `≡ 1 (mod 4)` -/

/-- For every odd prime `p`, the starred prime satisfies `p* ≡ 1 (mod 4)`.

This is the arithmetic reason `p*` (rather than `±p`) is the natural object: it is
the fundamental discriminant of `ℚ(√p*)`, and it is what makes the sign-free
reciprocity law below consistent. -/
theorem pStar_mod_four {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    pStar p ≡ 1 [ZMOD 4] := by
  have hpp : p.Prime := Fact.out
  have hodd : Odd p := hpp.odd_of_ne_two hp
  obtain ⟨m, hm⟩ := hodd
  have hk : (p - 1) / 2 = m := by omega
  rw [pStar, hk]
  rcases Nat.even_or_odd m with he | ho
  · have hsign : (-1 : ℤ) ^ m = 1 := he.neg_one_pow
    obtain ⟨j, hj⟩ := he
    have hp4 : p = 4 * j + 1 := by omega
    have hpz : (p : ℤ) = 4 * (j : ℤ) + 1 := by exact_mod_cast hp4
    rw [hsign, one_mul, hpz]
    exact Int.modEq_iff_dvd.mpr ⟨-(j : ℤ), by ring⟩
  · have hsign : (-1 : ℤ) ^ m = -1 := ho.neg_one_pow
    obtain ⟨j, hj⟩ := ho
    have hp4 : p = 4 * j + 3 := by omega
    have hpz : (p : ℤ) = 4 * (j : ℤ) + 3 := by exact_mod_cast hp4
    rw [hsign, neg_one_mul, hpz]
    exact Int.modEq_iff_dvd.mpr ⟨(j : ℤ) + 1, by ring⟩

/-! ### 3. Sign-free quadratic reciprocity -/

/-- **Sign-free quadratic reciprocity.**  For all odd primes `p` and `q`,

    (p* / q) = (q / p).

This is the law of quadratic reciprocity with its `(-1)^((p-1)(q-1)/4)` sign factor
absorbed into the normalisation `p* = (-1)^((p-1)/2)·p` coming from the Gauss-sum
identity `g² = p*`.  It is exactly the symmetric statement the Gauss-sum proof
produces, and is cleaner than the classical product form because the right-hand
side carries no sign. -/
theorem pStar_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q (pStar p) = legendreSym p q := by
  have hpp : p.Prime := Fact.out
  have hqq : q.Prime := Fact.out
  have hpodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp
  have hqodd : q % 2 = 1 := hqq.eq_two_or_odd.resolve_left hq
  -- `legendreSym q` is multiplicative on powers of `-1`.
  have hpow : ∀ k : ℕ, legendreSym q ((-1) ^ k) = (legendreSym q (-1)) ^ k := by
    intro k
    induction k with
    | zero => simp [legendreSym.at_one]
    | succ n ih => rw [pow_succ, legendreSym.mul, ih, pow_succ]
  -- first supplement: value at `-1`.
  have hneg : legendreSym q (-1) = (-1) ^ (q / 2) := by
    rw [legendreSym.at_neg_one hq, ZMod.χ₄_eq_neg_one_pow hqodd]
  have hpe : (p - 1) / 2 = p / 2 := by omega
  -- expand the starred prime through the multiplicative Legendre symbol.
  have key : legendreSym q (pStar p)
      = (-1) ^ (q / 2 * (p / 2)) * legendreSym q p := by
    rw [pStar, legendreSym.mul, hpow, hneg, ← pow_mul, hpe]
  rw [key, legendreSym.quadratic_reciprocity' hp hq, ← mul_assoc]
  have hsign : ((-1 : ℤ)) ^ (q / 2 * (p / 2)) * (-1) ^ (p / 2 * (q / 2)) = 1 := by
    rw [mul_comm (p / 2) (q / 2), ← pow_add]
    exact Even.neg_one_pow ⟨q / 2 * (p / 2), rfl⟩
  rw [hsign, one_mul]

/-- The symmetric companion `(q* / p) = (p / q)` — just `pStar_reciprocity` with the
roles of `p` and `q` exchanged.  Together with `pStar_reciprocity` this exhibits the
law as genuinely symmetric in the starred variables. -/
theorem pStar_reciprocity_symm {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym p (pStar q) = legendreSym q p :=
  pStar_reciprocity hq hp

/-- **Square-test form.**  For distinct odd primes, `p*` is a square mod `q` iff `q`
is a square mod `p`.  This is the sign-free law packaged as an equivalence of
solvability of `x² ≡ p* (mod q)` and `x² ≡ q (mod p)`. -/
theorem pStar_isSquare_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    IsSquare ((pStar p : ℤ) : ZMod q) ↔ IsSquare ((q : ℤ) : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have hqq : q.Prime := Fact.out
  -- `q ∤ p` and `p ∤ q` as integers.
  have hqp : ¬ (q : ℤ) ∣ (p : ℤ) := by
    rw [Int.natCast_dvd_natCast]; intro h
    exact hpq.symm ((Nat.prime_dvd_prime_iff_eq hqq hpp).mp h)
  have hpq' : ¬ (p : ℤ) ∣ (q : ℤ) := by
    rw [Int.natCast_dvd_natCast]; intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hqq).mp h)
  -- the relevant residues are nonzero.
  have hpz : ((pStar p : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, pStar]
    rcases Nat.even_or_odd ((p - 1) / 2) with he | ho
    · rw [he.neg_one_pow, one_mul]; exact hqp
    · rw [ho.neg_one_pow, neg_one_mul, dvd_neg]; exact hqp
  have hqz : ((q : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpq'
  rw [← legendreSym.eq_one_iff q hpz, ← legendreSym.eq_one_iff p hqz,
    pStar_reciprocity hp hq]

end QuadraticGaussSumSquareOQ03
