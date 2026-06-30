/-
  The Frobenius/Zolotarev Sign for EVERY ODD MODULUS:
  sign(x ↦ a·x on ℤ/n) = J(a | n)   for every odd n > 0.
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01)

  Open Question (the explicit follow-up flagged by the parent
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01, the whole-ring prime-power Zolotarev
  lemma):

    "Together with the CRT decomposition `sign_ringMulPerm_crt` (parent
     oq-01-oq-03) and `jacobiSym.mul_right`, this yields the Frobenius/Zolotarev
     identity `sign(ringMulPerm a on ℤ/n) = J(a | n)` for *every* odd `n` —
     completing the program the squarefree-odd lemma began."

  This file performs that final assembly and closes the theorem for ALL odd
  moduli — not merely the squarefree ones (`oq-01-oq-03`) nor merely the prime
  powers (`…OQ01OQ01OQ01OQ01`).

  ## The argument

  Both inputs are now in hand:

  * **Prime-power base.**  `ZolotarevPrimePowerWhole.sign_ringMulPerm_eq_legendre_pow`
    gives `sign(ringMulPerm a on ℤ/pᵉ) = legendreSym p (a mod p) ^ e`, which
    equals `J(a | pᵉ)` (`jacobiSym_prime_pow`).  We repackage it in the
    representative-free form `sign(ringMulPerm a) = J(A | pᵉ)` for any integer
    `A ≡ a (mod pᵉ)`, using that `legendreSym p` factors through `ℤ/p`.

  * **CRT multiplicativity.**  `ZolotarevCRT.sign_ringMulPerm_mul_of_odd` gives,
    for odd coprime `m, n`, the multiplicativity
    `sign(ringMulPerm a) = sign(ringMulPerm a₁) · sign(ringMulPerm a₂)`,
    matching `jacobiSym.mul_right` (`J(A | m·n) = J(A | m)·J(A | n)`).

  The two combine by **multiplicative induction** on `n`
  (`Nat.recOnPosPrimePosCoprime`):

      n = 0  : excluded (NeZero);
      n = 1  : both sides are 1;
      n = pᵉ : the prime-power base (p odd, since pᵉ is odd);
      n = m·n: the CRT step, m, n odd and coprime, reduce to the factors.

  The numerator `A : ℤ` (any representative of the unit `a`) is threaded through
  unchanged: the CRT step feeds the SAME `A` to both factors, exactly as
  `jacobiSym.mul_right` keeps the numerator fixed.

  ## Honest scope

  This is the capstone of the elementary-Zolotarev program: a self-contained,
  0-sorry, 0-axiom proof of `sign(ringMulPerm a on ℤ/n) = J(a | n)` for every
  odd `n > 0`.  The mod-2 case is genuinely excluded (`ℤ/2ⁿ` has even
  cardinality, where the permutation sign degenerates and the Jacobi symbol is
  not even defined for even denominators).

  References:
  - Zolotarev (1872); Frobenius (1914); Lerch (1896); Rousseau (1991), Monthly.
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01

set_option maxHeartbeats 1600000

namespace ZolotarevFullOdd

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm ringMulPerm_apply sign_ringMulPerm_mul_of_odd)

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: GENERIC BRIDGES  (units reduction map; CRT components; legendreSym)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The underlying ring element of `ZMod.unitsMap h u` is the cast of `u`. -/
theorem coe_unitsMap {n m : ℕ} (h : m ∣ n) (u : (ZMod n)ˣ) :
    ((ZMod.unitsMap h u : (ZMod m)ˣ) : ZMod m)
      = ZMod.castHom h (ZMod m) (u : ZMod n) := by
  simp [ZMod.unitsMap, Units.coe_map]

/-- The first CRT component is the cast to `ZMod m`.  Any two ring homs out of
    `ZMod (m*n)` agree (`RingHom.ext_zmod`), so the first projection of
    `chineseRemainder` is forced to be `castHom (dvd_mul_right m n)`. -/
theorem chineseRemainder_fst {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ((ZMod.chineseRemainder h) x).1 = ZMod.castHom (dvd_mul_right m n) (ZMod m) x := by
  have hext := RingHom.ext_zmod
    ((RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (dvd_mul_right m n) (ZMod m))
  simpa using DFunLike.congr_fun hext x

/-- The second CRT component is the cast to `ZMod n`. -/
theorem chineseRemainder_snd {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ((ZMod.chineseRemainder h) x).2 = ZMod.castHom (dvd_mul_left n m) (ZMod n) x := by
  have hext := RingHom.ext_zmod
    ((RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (dvd_mul_left n m) (ZMod n))
  simpa using DFunLike.congr_fun hext x

/-- `legendreSym p` depends only on the residue of the numerator mod `p`:
    equal images in `ℤ/p` give equal Legendre symbols. -/
theorem legendreSym_congr {p : ℕ} [Fact p.Prime] {A B : ℤ}
    (h : (A : ZMod p) = (B : ZMod p)) : legendreSym p A = legendreSym p B := by
  rw [legendreSym.mod p A, legendreSym.mod p B]
  have h' : A % (p : ℤ) = B % (p : ℤ) := (ZMod.intCast_eq_intCast_iff A B p).mp h
  rw [h']

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE PRIME-POWER BASE IN REPRESENTATIVE-FREE FORM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Prime-power base, representative-free.**  For an odd prime `p`, exponent
    `k ≥ 1`, a unit `a : (ℤ/pᵏ)ˣ`, and ANY integer `A` representing `a`
    (`A ≡ a mod pᵏ`), the sign of multiplication by `a` on the whole ring `ℤ/pᵏ`
    equals the Jacobi symbol `J(A | pᵏ)`.  This is `sign_ringMulPerm_eq_legendre_pow`
    repackaged so the numerator is an arbitrary representative. -/
theorem sign_ringMulPerm_eq_jacobiSym_of_cast {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {k : ℕ} (hk : 0 < k) (a : (ZMod (p ^ k))ˣ) (A : ℤ)
    (hA : (A : ZMod (p ^ k)) = (a : ZMod (p ^ k))) :
    (Equiv.Perm.sign (ringMulPerm a) : ℤ) = jacobiSym A (p ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [ZolotarevPrimePowerWhole.sign_ringMulPerm_eq_legendre_pow hp2 m a,
      ZolotarevPrimePowerWhole.jacobiSym_prime_pow A m]
  congr 1
  -- legendreSym p ((a mod p).val) = legendreSym p A, since both reduce mod p to a
  apply legendreSym_congr
  -- ((a mod p).val : ZMod p) = (A : ZMod p)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  -- (a mod p) = (A : ZMod p):  cast hA from ℤ/pᵐ⁺¹ down to ℤ/p
  have hcast := congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero m)) (ZMod p)) hA
  rw [map_intCast] at hcast
  rw [coe_unitsMap]
  exact hcast.symm

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE FULL ODD-MODULUS ZOLOTAREV–FROBENIUS IDENTITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The motive, proved by multiplicative induction below. -/
private theorem main_aux : ∀ (n : ℕ) [NeZero n] (_hodd : Odd n) (a : (ZMod n)ˣ) (A : ℤ),
    (A : ZMod n) = (a : ZMod n) →
      (Equiv.Perm.sign (ringMulPerm a) : ℤ) = jacobiSym A n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime
  · -- prime_pow:  n = p ^ k
    rename_i p k hp hk
    intro hz hodd a A hA
    haveI : NeZero (p ^ k) := hz
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      have heven : (2 ^ k) % 2 = 0 := Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)
      have hodd' : (2 ^ k) % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    exact sign_ringMulPerm_eq_jacobiSym_of_cast hp2 hk a A hA
  · -- zero:  excluded by NeZero
    intro hz
    exact (hz.out rfl).elim
  · -- one:  ℤ/1 is trivial; both sides are 1
    intro _ _ a A _
    haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    have ha1 : ringMulPerm a = 1 := Subsingleton.elim _ _
    rw [ha1]
    simp [jacobiSym.one_right]
  · -- coprime:  n = u * v with u, v > 1 coprime
    rename_i u v hu hv hcop ihu ihv
    intro hz hodd a A hA
    haveI : NeZero (u * v) := hz
    haveI : NeZero u := ⟨by omega⟩
    haveI : NeZero v := ⟨by omega⟩
    obtain ⟨hou, hov⟩ := Nat.odd_mul.mp hodd
    -- CRT components of the unit a
    set a₁ := ZMod.unitsMap (dvd_mul_right u v) a with ha₁
    set a₂ := ZMod.unitsMap (dvd_mul_left v u) a with ha₂
    have h₁ : (a₁ : ZMod u) = ((ZMod.chineseRemainder hcop) (a : ZMod (u * v))).1 := by
      rw [ha₁, coe_unitsMap, chineseRemainder_fst]
    have h₂ : (a₂ : ZMod v) = ((ZMod.chineseRemainder hcop) (a : ZMod (u * v))).2 := by
      rw [ha₂, coe_unitsMap, chineseRemainder_snd]
    -- the numerator A represents each CRT component
    have hAu : (A : ZMod u) = (a₁ : ZMod u) := by
      rw [ha₁, coe_unitsMap, ← hA, map_intCast]
    have hAv : (A : ZMod v) = (a₂ : ZMod v) := by
      rw [ha₂, coe_unitsMap, ← hA, map_intCast]
    -- decompose the sign multiplicatively, then apply the inductive hypotheses
    have hdecomp : (Equiv.Perm.sign (ringMulPerm a) : ℤ)
        = (Equiv.Perm.sign (ringMulPerm a₁) : ℤ) * (Equiv.Perm.sign (ringMulPerm a₂) : ℤ) := by
      rw [sign_ringMulPerm_mul_of_odd hcop hou hov a a₁ a₂ h₁ h₂, Units.val_mul]
    rw [hdecomp, ihu hou a₁ A hAu, ihv hov a₂ A hAv]
    exact (jacobiSym.mul_right A u v).symm

/-- **Zolotarev–Frobenius for every odd modulus.**  For any odd `n > 0`, a unit
    `a : (ℤ/n)ˣ`, and any integer representative `A ≡ a (mod n)`, the sign of the
    multiplication-by-`a` permutation of the whole ring `ℤ/n` is the Jacobi
    symbol `J(A | n)`.  This is the full Frobenius generalization of Zolotarev's
    lemma — valid for ALL odd moduli, not just squarefree ones or prime powers. -/
theorem sign_ringMulPerm_eq_jacobiSym_odd {n : ℕ} [NeZero n] (hodd : Odd n)
    (a : (ZMod n)ˣ) (A : ℤ) (hA : (A : ZMod n) = (a : ZMod n)) :
    (Equiv.Perm.sign (ringMulPerm a) : ℤ) = jacobiSym A n :=
  main_aux n hodd a A hA

/-- **Canonical-representative form.**  Taking the canonical representative
    `A = (a : ℤ/n).val ∈ {0, …, n-1}`, the Zolotarev sign equals `J((a).val | n)`. -/
theorem sign_ringMulPerm_eq_jacobiSym_val {n : ℕ} [NeZero n] (hodd : Odd n) (a : (ZMod n)ˣ) :
    (Equiv.Perm.sign (ringMulPerm a) : ℤ) = jacobiSym ((a : ZMod n).val : ℤ) n :=
  sign_ringMulPerm_eq_jacobiSym_odd hodd a _ (by rw [Int.cast_natCast, ZMod.natCast_zmod_val])

/-- **Character form.**  Through `signRingHom`, the Zolotarev sign CHARACTER on
    `(ℤ/n)ˣ` IS the Jacobi symbol (on canonical representatives) for odd `n`. -/
theorem signRingHom_eq_jacobiSym {n : ℕ} [NeZero n] (hodd : Odd n) (a : (ZMod n)ˣ) :
    (ZolotarevCRT.signRingHom a : ℤ) = jacobiSym ((a : ZMod n).val : ℤ) n := by
  rw [ZolotarevCRT.signRingHom_apply]
  exact sign_ringMulPerm_eq_jacobiSym_val hodd a

end ZolotarevFullOdd

#check @ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd
#check @ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_val
#check @ZolotarevFullOdd.signRingHom_eq_jacobiSym
