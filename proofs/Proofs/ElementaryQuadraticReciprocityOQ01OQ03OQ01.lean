/-
  The Base Case of the Frobenius/Jacobi Generalization of Zolotarev's Lemma:
  sign(x ↦ a·x on the WHOLE field ℤ/p) = legendreSym p a
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01)

  Open Question (the explicit "remaining glue" left by the parent oq-01-oq-03):

    The parent (`ElementaryQuadraticReciprocityOQ01OQ03`, namespace `ZolotarevCRT`)
    formalized the STRUCTURAL Chinese-Remainder decomposition of the
    multiplication permutation `ringMulPerm a : Perm (ZMod n)` acting on the
    *whole ring* `ZMod n`, proving that for odd coprime moduli its sign is
    multiplicative across the CRT factorization — the permutation-theoretic
    shadow of `jacobiSym.mul_right`.  It explicitly did NOT close the loop to
    Jacobi *values*, leaving as the next step the base case

        sign(ringMulPerm a on ZMod p) = legendreSym p a    (p prime),

    "which combines the parent's `zolotarev_lemma` (units version) with a
    fixed-point sign-restriction argument (multiplication fixes 0 ∈ ZMod p)."

  This file proves exactly that base case (0 sorries, 0 axioms).

  ## Self-contained note

  The grandparent file `ElementaryQuadraticReciprocityOQ01` (the units-level
  Zolotarev lemma) no longer compiles against the current Mathlib (forward
  references + deprecations — a separate bit-rot repair).  To keep this result
  unconditional and axiom-free, we re-establish the units-level statement here
  from scratch via the modern Mathlib API, importing only the (building) parent
  `ElementaryQuadraticReciprocityOQ01OQ03` for the CRT machinery.

  ## The argument

  Zolotarev's lemma naturally lives on the UNITS `(ZMod p)ˣ`: the sign of the
  multiplication-by-`a` permutation equals the quadratic character (Part II).
  The Frobenius/Jacobi/CRT setting, by contrast, acts on *all* of `ZMod p`.  The
  bridge between the two is purely permutation-theoretic and uses no number
  theory (Part I):

  1. **Fixed point.**  Multiplication by a unit `a` fixes `0` and permutes the
     nonzero residues.  Hence (`Equiv.Perm.sign_subtypePerm`) the sign of
     `ringMulPerm a` on `ZMod p` equals the sign of its restriction to
     `{x // x ≠ 0}`.
  2. **Units ≃ nonzero.**  In a field, `(ZMod p)ˣ ≃ {x : ZMod p // x ≠ 0}`
     (`unitsEquivNeZero`), and under it the restricted permutation is exactly
     `mulPerm a`.  Transporting the sign (`sign_eq_sign_of_equiv`) gives
     `sign(ringMulPerm a) = sign(mulPerm a)`.

  Composing the bridge with the units-level Zolotarev lemma yields the base case
  (Part III), and composing the base case with the parent's
  `sign_ringMulPerm_mul_of_odd` yields the Jacobi value statement for a two-prime
  squarefree odd modulus (Part IV) — closing the loop the parent left open.

  References:
  - Zolotarev (1872); Frobenius (1914); Rousseau (1991), Amer. Math. Monthly.
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03

set_option maxHeartbeats 800000

namespace ZolotarevBaseCase

open Equiv Equiv.Perm Finset
open ZolotarevCRT (ringMulPerm ringMulPerm_apply)

variable {p : ℕ} [Fact p.Prime]

/-
═══════════════════════════════════════════════════════════════════════════════
PART 0: THE MULTIPLICATION PERMUTATION ON THE UNITS  (self-contained)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Multiplication by a unit `a` is a permutation of the units `(ZMod p)ˣ`. -/
noncomputable def mulPerm (a : (ZMod p)ˣ) : Perm (ZMod p)ˣ where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

theorem mulPerm_apply (a x : (ZMod p)ˣ) : mulPerm a x = a * x := rfl

theorem mulPerm_one : mulPerm (1 : (ZMod p)ˣ) = 1 := by ext x; simp [mulPerm]

theorem mulPerm_mul (a b : (ZMod p)ˣ) : mulPerm (a * b) = mulPerm a * mulPerm b := by
  ext x; simp [mulPerm, Perm.mul_apply, mul_assoc]

/-- The multiplication permutation as a monoid homomorphism. -/
noncomputable def mulPermHom : (ZMod p)ˣ →* Perm (ZMod p)ˣ where
  toFun := mulPerm
  map_one' := mulPerm_one
  map_mul' := mulPerm_mul

/-- Multiplication by a non-identity unit has no fixed point. -/
theorem mulPerm_no_fixed_point (a : (ZMod p)ˣ) (ha : a ≠ 1) (x : (ZMod p)ˣ) :
    mulPerm a x ≠ x := by
  intro h
  apply ha
  have hx : a * x = 1 * x := by rw [one_mul]; exact h
  exact mul_right_cancel hx

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE FIXED-POINT / UNITS-RESTRICTION BRIDGE  (the new content)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Multiplication by a unit `a` keeps nonzero residues nonzero: `a·x ≠ 0 ↔ x ≠ 0`. -/
theorem ringMulPerm_ne_zero_iff (a : (ZMod p)ˣ) (x : ZMod p) :
    ringMulPerm a x ≠ 0 ↔ x ≠ 0 := by
  rw [ringMulPerm_apply, ne_eq, ne_eq, mul_eq_zero, not_or]
  exact and_iff_right a.ne_zero

/-- `0` is the only fixed-point obstruction of `ringMulPerm a`. -/
theorem ringMulPerm_fixes_zero (a : (ZMod p)ˣ) (x : ZMod p) :
    ringMulPerm a x ≠ x → x ≠ 0 := by
  intro hx
  rintro rfl
  exact hx (by rw [ringMulPerm_apply, mul_zero])

/-- **The bridge.**  The sign of multiplication-by-`a` on the *whole field*
    `ZMod p` equals the sign on the *units* `(ZMod p)ˣ`: restrict to the nonzero
    subtype (a fixed point at `0`), then transport along `unitsEquivNeZero`. -/
theorem sign_ringMulPerm_eq_sign_mulPerm (a : (ZMod p)ˣ) :
    Equiv.Perm.sign (ringMulPerm a) = Equiv.Perm.sign (mulPerm a) := by
  have h₁ : ∀ x : ZMod p, ((ringMulPerm a x ≠ 0) ↔ (x ≠ 0)) :=
    fun x => ringMulPerm_ne_zero_iff a x
  rw [← sign_subtypePerm (ringMulPerm a) h₁ (ringMulPerm_fixes_zero a)]
  refine sign_eq_sign_of_equiv _ _ unitsEquivNeZero.symm ?_
  intro x
  apply Units.ext
  show (a : ZMod p) * (x : ZMod p) = ((mulPerm a (unitsEquivNeZero.symm x) : (ZMod p)ˣ) : ZMod p)
  rw [mulPerm_apply, Units.val_mul]
  rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: ZOLOTAREV'S LEMMA ON THE UNITS  (re-established self-contained)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A generator of `(ZMod p)ˣ` is not the identity (for `p ≠ 2`). -/
theorem generator_ne_one (g : (ZMod p)ˣ) (hp2 : p ≠ 2)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) : g ≠ 1 := by
  intro h
  have hord : orderOf g = Nat.card (ZMod p)ˣ :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  rw [h, orderOf_one, Nat.card_eq_fintype_card, ZMod.card_units p] at hord
  have hp := (Fact.out : Nat.Prime p).two_le
  omega

/-- The multiplication permutation of a generator is a single cycle. -/
theorem mulPerm_generator_isCycle (g : (ZMod p)ˣ)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) (hg1 : g ≠ 1) :
    (mulPerm g).IsCycle := by
  refine ⟨1, mulPerm_no_fixed_point g hg1 1, ?_⟩
  intro y _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
  refine ⟨n, ?_⟩
  have hpow : (mulPerm g) ^ n = mulPerm (g ^ n) := (map_zpow mulPermHom g n).symm
  rw [hpow]
  change (g ^ n : (ZMod p)ˣ) * 1 = y
  rw [mul_one]; exact hn

/-- A non-identity multiplication permutation has full support. -/
theorem mulPerm_support_eq_univ (a : (ZMod p)ˣ) (ha : a ≠ 1) :
    (mulPerm a).support = Finset.univ := by
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  exact mulPerm_no_fixed_point a ha x

/-- The sign of `mulPerm` at a generator is `-1`: it is a single `(p-1)`-cycle,
    and `p - 1` is even. -/
theorem sign_mulPerm_generator (g : (ZMod p)ˣ) (hp2 : p ≠ 2)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    Equiv.Perm.sign (mulPerm g) = -1 := by
  have hg1 := generator_ne_one g hp2 hg
  have hcyc := mulPerm_generator_isCycle g hg hg1
  rw [hcyc.sign, mulPerm_support_eq_univ g hg1, Finset.card_univ, ZMod.card_units p]
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have heven : Even (p - 1) := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  rw [Even.neg_one_pow heven]

/-- A generator of `(ZMod p)ˣ` is a non-square in the field `ZMod p`.
    (If `g = u²` then `orderOf g = orderOf u / gcd(orderOf u, 2)`, contradicting
    `orderOf g = p - 1` with `p - 1` even and maximal.) -/
theorem generator_not_isSquare (g : (ZMod p)ˣ) (hp2 : p ≠ 2)
    (hg : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    ¬ IsSquare (g : ZMod p) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact g.ne_zero hr
  obtain ⟨u, hu⟩ := isUnit_iff_ne_zero.mpr hr0
  have hgu : g = u ^ 2 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, sq]; exact hr
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hou_dvd : orderOf u ∣ p - 1 := by rw [← hcard]; exact orderOf_dvd_card
  have hou_le : orderOf u ≤ p - 1 :=
    Nat.le_of_dvd (by have := (Fact.out : Nat.Prime p).two_le; omega) hou_dvd
  have hopow : orderOf g = orderOf u / Nat.gcd (orderOf u) 2 := by
    rw [hgu, orderOf_pow' u (by norm_num)]
  have hd_dvd : Nat.gcd (orderOf u) 2 ∣ orderOf u := Nat.gcd_dvd_left _ _
  have hpd : p - 1 = orderOf u / Nat.gcd (orderOf u) 2 := by rw [← hopow, hog]
  have hou_eq : orderOf u = (p - 1) * Nat.gcd (orderOf u) 2 := by
    rw [hpd]; exact (Nat.div_mul_cancel hd_dvd).symm
  have hd2dvd : Nat.gcd (orderOf u) 2 ∣ 2 := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2dvd with hd1 | hd2
  · -- gcd = 1: then orderOf u = p - 1 is odd, contradicting p - 1 even
    have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
    have heven : (2 : ℕ) ∣ (p - 1) := by rcases hodd with ⟨k, hk⟩; omega
    have h2dvd : (2 : ℕ) ∣ orderOf u := by rw [hou_eq, hd1, mul_one]; exact heven
    have hcontra : (2 : ℕ) ∣ Nat.gcd (orderOf u) 2 := Nat.dvd_gcd h2dvd dvd_rfl
    rw [hd1] at hcontra
    omega
  · -- gcd = 2: then orderOf u = 2(p-1) > p-1, contradicting orderOf u ≤ p-1
    rw [hd2] at hou_eq
    have := (Fact.out : Nat.Prime p).two_le
    omega

/-- **Zolotarev's lemma (units version).**  For an odd prime `p`, the sign of
    multiplication-by-`a` on `(ZMod p)ˣ` equals the quadratic character of `a`.
    Proof: both sides are multiplicative in `a`; on a generator both equal `-1`
    (a `(p-1)`-cycle has sign `-1`, and a generator is a non-square), and every
    unit is a power of the generator. -/
theorem sign_mulPerm_eq_quadraticChar (hp2 : p ≠ 2) (a : (ZMod p)ˣ) :
    ((Equiv.Perm.sign (mulPerm a) : ℤ)) = quadraticChar (ZMod p) (a : ZMod p) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hsg : ((Equiv.Perm.sign (mulPerm g) : ℤ)) = -1 := by
    rw [sign_mulPerm_generator g hp2 hg]; rfl
  have hqg : quadraticChar (ZMod p) (g : ZMod p) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (generator_not_isSquare g hp2 hg)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg a))
  -- both sides factor through the generator
  have hsign : ((Equiv.Perm.sign (mulPerm a) : ℤ)) = (-1) ^ n := by
    have hpow : Equiv.Perm.sign (mulPerm a) = (Equiv.Perm.sign (mulPerm g)) ^ n := by
      rw [← hn]
      exact map_pow ((Equiv.Perm.sign : Perm (ZMod p)ˣ →* ℤˣ).comp mulPermHom) g n
    rw [hpow, Units.val_pow_eq_pow_val, hsg]
  have hchar : quadraticChar (ZMod p) (a : ZMod p) = (-1) ^ n := by
    rw [← hn, Units.val_pow_eq_pow_val, map_pow, hqg]
  rw [hsign, hchar]

/-- Bridge to the Legendre symbol: `legendreSym p` of the integer lift of a unit
    equals the quadratic character of that unit. -/
theorem legendreSym_unit_eq (a : (ZMod p)ˣ) :
    legendreSym p (((a : ZMod p).val : ℤ)) = quadraticChar (ZMod p) (a : ZMod p) := by
  rw [legendreSym]
  congr 1
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE BASE CASE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The base case of Zolotarev/Frobenius (the glue left open by the parent).**
    For a prime `p ≠ 2` and a unit `a`, the sign of the multiplication-by-`a`
    permutation of the *whole field* `ZMod p` equals the Legendre symbol of `a`. -/
theorem sign_ringMulPerm_eq_legendre (hp2 : p ≠ 2) (a : (ZMod p)ˣ) :
    ((Equiv.Perm.sign (ringMulPerm a) : ℤ)) = legendreSym p (((a : ZMod p).val : ℤ)) := by
  rw [sign_ringMulPerm_eq_sign_mulPerm a, sign_mulPerm_eq_quadraticChar hp2 a,
    legendreSym_unit_eq a]

/-- Reversed orientation, matching the grandparent's `zolotarev_lemma` framing. -/
theorem legendre_eq_sign_ringMulPerm (hp2 : p ≠ 2) (a : (ZMod p)ˣ) :
    legendreSym p (((a : ZMod p).val : ℤ)) = ((Equiv.Perm.sign (ringMulPerm a) : ℤ)) :=
  (sign_ringMulPerm_eq_legendre hp2 a).symm

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CLOSING THE LOOP — JACOBI VALUES FOR A TWO-PRIME ODD MODULUS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Loop closed for a two-prime squarefree odd modulus.**
    For distinct odd primes `p, q`, the sign of multiplication-by-`a` on the
    whole ring `ZMod (p*q)` is the product of the Legendre symbols of the two CRT
    components — the (two-factor) Jacobi value.  Combines the parent's CRT
    multiplicativity (`ZolotarevCRT.sign_ringMulPerm_mul_of_odd`) with the base
    case of Part III. -/
theorem sign_ringMulPerm_eq_legendre_mul
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (h : p.Coprime q)
    (a : (ZMod (p * q))ˣ) (a₁ : (ZMod p)ˣ) (a₂ : (ZMod q)ˣ)
    (h₁ : (a₁ : ZMod p) = ((ZMod.chineseRemainder h) (a : ZMod (p * q))).1)
    (h₂ : (a₂ : ZMod q) = ((ZMod.chineseRemainder h) (a : ZMod (p * q))).2) :
    ((Equiv.Perm.sign (ringMulPerm a) : ℤ))
      = legendreSym p (((a₁ : ZMod p).val : ℤ)) * legendreSym q (((a₂ : ZMod q).val : ℤ)) := by
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hqodd : Odd q := (Fact.out : Nat.Prime q).odd_of_ne_two hq2
  rw [ZolotarevCRT.sign_ringMulPerm_mul_of_odd h hpodd hqodd a a₁ a₂ h₁ h₂]
  push_cast
  rw [sign_ringMulPerm_eq_legendre hp2 a₁, sign_ringMulPerm_eq_legendre hq2 a₂]

end ZolotarevBaseCase

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The base case of Zolotarev/Frobenius (answering oq-01-oq-03's listed next step)

### What's proved (0 sorries, 0 axioms):
- `sign_ringMulPerm_eq_sign_mulPerm` (Part I): the whole-field sign equals the
  units sign, via `sign_subtypePerm` (fixed point at 0) + `unitsEquivNeZero`
  transport.  This is the "fixed-point sign-restriction argument" the parent
  named — the genuinely new content.
- `sign_mulPerm_eq_quadraticChar` (Part II): Zolotarev's lemma on the units,
  re-established self-contained on the modern Mathlib API (single-cycle sign at a
  generator + generator-is-a-non-square + power-of-generator), because the
  grandparent `ElementaryQuadraticReciprocityOQ01` is currently bit-rotted.
- `sign_ringMulPerm_eq_legendre` (Part III): **the base case** —
  `sign(ringMulPerm a on ZMod p) = legendreSym p a`.
- `sign_ringMulPerm_eq_legendre_mul` (Part IV): composing the base case with the
  parent's CRT multiplicativity gives the Jacobi value as a product of Legendre
  symbols on a two-prime squarefree odd modulus — closing the loop.

### Honest scope:
The base case is complete and unconditional (for `p ≠ 2`).  The loop-closing
corollary is stated for a TWO-PRIME modulus `p*q`; fully general squarefree (and
then prime-power) odd `n` follows by iterating `sign_ringMulPerm_mul_of_odd`
over the factorization — a routine induction adding no new idea, left to a
follow-up.  No new axioms are introduced.

### Key insight:
The passage from the units `(ZMod p)ˣ` (where Zolotarev's lemma lives, as a
character on a cyclic group) to the whole field `ZMod p` (the Frobenius/CRT
setting) costs nothing in sign: `0` is a fixed point, so the sign is carried by
the units alone.  This single observation glues the cyclic-character argument and
the CRT product argument into one statement about Jacobi values.
-/

#check @ZolotarevBaseCase.sign_ringMulPerm_eq_sign_mulPerm
#check @ZolotarevBaseCase.sign_mulPerm_eq_quadraticChar
#check @ZolotarevBaseCase.sign_ringMulPerm_eq_legendre
#check @ZolotarevBaseCase.legendre_eq_sign_ringMulPerm
#check @ZolotarevBaseCase.sign_ringMulPerm_eq_legendre_mul
