/-
  The Frobenius/Zolotarev Sign on a PRIME-POWER Modulus (whole-ring level):
  sign(x ↦ a·x on ℤ/pⁿ) = legendreSym p (a mod p)ⁿ = J(a | pⁿ)   for p an odd prime.
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01)

  Open Question (the explicit follow-up flagged by the parent
  oq-01-oq-03-oq-01-oq-01-oq-01, the prime-power *units*-level Zolotarev lemma):

    "Assembling [the units-level sign] with the action on the non-unit part
     p·(ℤ/pⁿ⁻¹) ⊂ ℤ/pⁿ to obtain the whole-ring statement
     sign(ringMulPerm u on ℤ/pⁿ) = J(u | pⁿ), and thence every odd n, is left to
     the follow-up."

  This file performs that assembly and closes the prime-power case.

  ## The argument

  Fix an odd prime `p` and a unit `a : (ℤ/pⁿ)ˣ`.  Multiplication by `a`,
  `ringMulPerm a : Perm (ℤ/pⁿ)` (from the CRT file `…OQ01OQ03`), preserves both
  the set of units `U = {x | IsUnit x}` and its complement `N = {x | ¬IsUnit x}`
  (the maximal ideal `(p)`).  Hence its sign splits as a product over the two
  invariant blocks (`Equiv.Perm.sign_subtypeCongr`):

      sign(ringMulPerm a) = sign(a· on U) · sign(a· on N).

  * **Units block.**  `U ≃ (ℤ/pⁿ)ˣ` and there `a·` is left translation
    `Equiv.mulLeft a`, whose sign is `legendreSym p (a mod p)` — exactly the
    parent units-level lemma `ZolotarevPrimePower.sign_mulLeft_eq_legendre`.

  * **Non-unit block.**  `N = (p)` is carried isomorphically onto `ℤ/pⁿ⁻¹` by
    `μ : y ↦ p·(lift y)` (`nonUnitsEquiv`), an additive bijection under which
    `a·` becomes multiplication by the reduction `ā ∈ (ℤ/pⁿ⁻¹)ˣ`.  Thus
    `sign(a· on N) = sign(ringMulPerm ā on ℤ/pⁿ⁻¹)`, a strictly smaller instance
    of the same problem.

  The compatibility `μ(ā·y) = a·μ(y)` is the genuinely new computation; it rests
  on the bridge `p·u = p·v ⟺ (u ≡ v mod pⁿ⁻¹)` (`mul_p_of_castHom_eq`).

  Iterating the recursion `n` times gives

      sign(ringMulPerm a on ℤ/pⁿ) = legendreSym p (a mod p) ^ n = J(a | pⁿ).

  ## Honest scope

  This closes the prime-power case `sign(ringMulPerm a on ℤ/pᵉ) = J(a | pᵉ)`.
  Together with the CRT decomposition `sign_ringMulPerm_crt` (parent oq-01-oq-03)
  and `jacobiSym.mul_right`, this yields the Frobenius/Zolotarev identity
  `sign(ringMulPerm a on ℤ/n) = J(a | n)` for *every* odd `n` — completing the
  program the squarefree-odd lemma began.  0 sorries, 0 axioms.

  References:
  - Zolotarev (1872); Frobenius (1914); Rousseau (1991), Amer. Math. Monthly.
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01

set_option maxHeartbeats 1600000

namespace ZolotarevPrimePowerWhole

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm ringMulPerm_apply)

/-
═══════════════════════════════════════════════════════════════════════════════
PART 0: A GROUP'S UNITS ARE ITS IsUnit SUBTYPE  (generic)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The units of a monoid are in bijection with the subtype of unit elements. -/
noncomputable def unitsEquivIsUnit (M : Type*) [Monoid M] : Mˣ ≃ {x : M // IsUnit x} where
  toFun u := ⟨(u : M), u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext u.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE p-MULTIPLICATION BRIDGE ON ℤ/pⁿ⁺¹
═══════════════════════════════════════════════════════════════════════════════ -/

section Bridge
variable {p j : ℕ} [hp : Fact p.Prime] [NeZero (p ^ (j + 1))] [NeZero (p ^ j)]

/-- `p·z = 0` in `ℤ/pʲ⁺¹` iff `z` reduces to `0` in `ℤ/pʲ`; both say `pʲ ∣ z.val`. -/
theorem mul_p_eq_zero_iff (z : ZMod (p ^ (j + 1))) :
    (p : ZMod (p ^ (j + 1))) * z = 0
      ↔ ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j)) z = 0 := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, map_natCast, ZMod.natCast_eq_zero_iff,
    pow_succ, mul_comm (p ^ j) p, Nat.mul_dvd_mul_iff_left hp.out.pos]

/-- If `u` and `v` agree mod `pʲ`, then `p·u = p·v` in `ℤ/pʲ⁺¹`. -/
theorem mul_p_of_castHom_eq {u v : ZMod (p ^ (j + 1))}
    (h : ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j)) u
       = ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j)) v) :
    (p : ZMod (p ^ (j + 1))) * u = (p : ZMod (p ^ (j + 1))) * v := by
  have hz := mul_p_eq_zero_iff (p := p) (j := j) (u - v)
  rw [mul_sub, sub_eq_zero, map_sub, sub_eq_zero] at hz
  exact hz.mpr h

/-- Conversely, `p·u = p·v` forces `u` and `v` to agree mod `pʲ`. -/
theorem castHom_eq_of_mul_p_eq {u v : ZMod (p ^ (j + 1))}
    (h : (p : ZMod (p ^ (j + 1))) * u = (p : ZMod (p ^ (j + 1))) * v) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j)) u
      = ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j)) v := by
  have hz := mul_p_eq_zero_iff (p := p) (j := j) (u - v)
  rw [mul_sub, sub_eq_zero, map_sub, sub_eq_zero] at hz
  exact hz.mp h

end Bridge

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE NON-UNIT BLOCK IS ℤ/pⁿ⁻¹
═══════════════════════════════════════════════════════════════════════════════ -/

/-- `p · z` is never a unit in `ℤ/pʲ⁺¹`. -/
theorem not_isUnit_mul_p {p j : ℕ} [hp : Fact p.Prime] [NeZero (p ^ (j + 1))]
    (z : ZMod (p ^ (j + 1))) : ¬ IsUnit ((p : ZMod (p ^ (j + 1))) * z) := by
  have hp_not : ¬ IsUnit ((p : ℕ) : ZMod (p ^ (j + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    intro hc
    have h1 : p ∣ 1 :=
      hc ▸ Nat.dvd_gcd dvd_rfl (dvd_pow_self p (Nat.succ_ne_zero j))
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h1)
  intro hu
  exact hp_not (IsUnit.mul_iff.mp hu).1

/-- The forward map `y ↦ p · (lift y)` from `ℤ/pʲ` to the non-units of `ℤ/pʲ⁺¹`. -/
def nonUnitsFun {p : ℕ} [Fact p.Prime] (j : ℕ) [NeZero (p ^ (j + 1))] :
    ZMod (p ^ j) → {x : ZMod (p ^ (j + 1)) // ¬ IsUnit x} :=
  fun y => ⟨(p : ZMod (p ^ (j + 1))) * ((y.val : ℕ) : ZMod (p ^ (j + 1))), not_isUnit_mul_p _⟩

theorem nonUnitsFun_bijective {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    [NeZero (p ^ (j + 1))] [NeZero (p ^ j)] :
    Function.Bijective (nonUnitsFun (p := p) j) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · -- injectivity, via the bridge
    intro y y' hyy
    have hval : (p : ZMod (p ^ (j + 1))) * ((y.val : ℕ) : ZMod (p ^ (j + 1)))
        = (p : ZMod (p ^ (j + 1))) * ((y'.val : ℕ) : ZMod (p ^ (j + 1))) :=
      congrArg Subtype.val hyy
    have hcast := castHom_eq_of_mul_p_eq (p := p) (j := j) hval
    simpa only [map_natCast, ZMod.natCast_zmod_val] using hcast
  · -- cardinality
    rw [ZMod.card]
    have hCU : Fintype.card {x : ZMod (p ^ (j + 1)) // IsUnit x}
        = (p ^ (j + 1)).totient := by
      rw [← Fintype.card_congr (unitsEquivIsUnit (ZMod (p ^ (j + 1)))),
        ZMod.card_units_eq_totient]
    have hp1 := hp.out.pos
    have hpe : p ^ j * (p - 1) + p ^ j = p ^ (j + 1) := by
      rw [pow_succ, ← Nat.mul_succ]
      congr 1
      omega
    rw [Fintype.card_subtype_compl, ZMod.card, hCU, Nat.totient_prime_pow_succ hp.out]
    omega

/-- The non-unit elements of `ℤ/pʲ⁺¹` (the maximal ideal `(p)`) are carried in
    bijection from `ℤ/pʲ` by `y ↦ p · (lift y)`. -/
noncomputable def nonUnitsEquiv {p : ℕ} [Fact p.Prime] (j : ℕ)
    [NeZero (p ^ (j + 1))] [NeZero (p ^ j)] :
    ZMod (p ^ j) ≃ {x : ZMod (p ^ (j + 1)) // ¬ IsUnit x} :=
  Equiv.ofBijective (nonUnitsFun (p := p) j) (nonUnitsFun_bijective j)

@[simp] theorem nonUnitsEquiv_apply_coe {p : ℕ} [Fact p.Prime] (j : ℕ)
    [NeZero (p ^ (j + 1))] [NeZero (p ^ j)] (y : ZMod (p ^ j)) :
    ((nonUnitsEquiv (p := p) j y : {x : ZMod (p ^ (j + 1)) // ¬ IsUnit x}) : ZMod (p ^ (j + 1)))
      = (p : ZMod (p ^ (j + 1))) * ((y.val : ℕ) : ZMod (p ^ (j + 1))) := rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE PRIME-POWER RECURSION FOR THE WHOLE-RING SIGN
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The block recursion.**  For an odd prime `p` and a unit `a : (ℤ/pʲ⁺¹)ˣ`,
    the sign of multiplication by `a` on the whole ring is the Legendre symbol of
    the residue `a mod p` times the sign of multiplication by the reduction
    `ā : (ℤ/pʲ)ˣ` on the smaller ring. -/
theorem sign_ringMulPerm_succ {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (j : ℕ)
    (a : (ZMod (p ^ (j + 1)))ˣ) :
    (Equiv.Perm.sign (ringMulPerm a) : ℤ)
      = (legendreSym p ((ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero j)) a : ZMod p).val : ℤ))
        * (Equiv.Perm.sign (ringMulPerm
            (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a)) : ℤ) := by
  classical
  haveI : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ j) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  -- the multiplication permutation preserves units and non-units
  have hUiff : ∀ x, IsUnit (ringMulPerm a x) ↔ IsUnit x := by
    intro x
    rw [ringMulPerm_apply]
    exact ⟨fun h => (IsUnit.mul_iff.mp h).2, fun h => a.isUnit.mul h⟩
  have hNiff : ∀ x, ¬ IsUnit (ringMulPerm a x) ↔ ¬ IsUnit x := fun x => not_congr (hUiff x)
  -- Lemma A: split the permutation into its two invariant blocks
  have hA : ringMulPerm a
      = (Equiv.Perm.subtypePerm (ringMulPerm a) hUiff).subtypeCongr
          (Equiv.Perm.subtypePerm (ringMulPerm a) (p := fun x => ¬ IsUnit x) hNiff) := by
    ext x
    by_cases hx : IsUnit x
    · rw [Perm.subtypeCongr.left_apply _ _ hx]; rfl
    · rw [Perm.subtypeCongr.right_apply _ _ hx]; rfl
  -- Lemma B: the units block is the left regular representation, sign = Legendre
  have hUnits : (Equiv.Perm.sign (Equiv.Perm.subtypePerm (ringMulPerm a) hUiff) : ℤ)
      = legendreSym p ((ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero j)) a : ZMod p).val : ℤ) := by
    have hse : Equiv.Perm.sign (Equiv.mulLeft a)
        = Equiv.Perm.sign (Equiv.Perm.subtypePerm (ringMulPerm a) hUiff) := by
      apply sign_eq_sign_of_equiv _ _ (unitsEquivIsUnit (ZMod (p ^ (j + 1))))
      intro u
      apply Subtype.ext
      show ((a * u : (ZMod (p ^ (j + 1)))ˣ) : ZMod (p ^ (j + 1)))
        = ringMulPerm a (u : ZMod (p ^ (j + 1)))
      rw [ringMulPerm_apply, Units.val_mul]
    rw [← hse]
    exact ZolotarevPrimePower.sign_mulLeft_eq_legendre hp2 (Nat.succ_ne_zero j) a
  -- Lemma C: the non-unit block is multiplication by the reduction ā on ℤ/pʲ
  have hNon : (Equiv.Perm.sign (Equiv.Perm.subtypePerm (ringMulPerm a) (p := fun x => ¬ IsUnit x) hNiff) : ℤ)
      = (Equiv.Perm.sign (ringMulPerm
          (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a)) : ℤ) := by
    have hse : Equiv.Perm.sign (ringMulPerm
          (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a))
        = Equiv.Perm.sign (Equiv.Perm.subtypePerm (ringMulPerm a) (p := fun x => ¬ IsUnit x) hNiff) := by
      apply sign_eq_sign_of_equiv _ _ (nonUnitsEquiv (p := p) j)
      intro y
      apply Subtype.ext
      -- LHS coe: p · (ā·y).val ;  RHS coe: a · (p · y.val)
      have hLHS : ((nonUnitsEquiv (p := p) j
            (ringMulPerm (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a) y) :
            {x : ZMod (p ^ (j + 1)) // ¬ IsUnit x}) : ZMod (p ^ (j + 1)))
          = (p : ZMod (p ^ (j + 1)))
            * (((ringMulPerm (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a) y).val : ℕ)
                : ZMod (p ^ (j + 1))) := nonUnitsEquiv_apply_coe _ _
      have hRHS : ((Equiv.Perm.subtypePerm (ringMulPerm a) (p := fun x => ¬ IsUnit x) hNiff (nonUnitsEquiv (p := p) j y) :
            {x : ZMod (p ^ (j + 1)) // ¬ IsUnit x}) : ZMod (p ^ (j + 1)))
          = (p : ZMod (p ^ (j + 1)))
            * ((a : ZMod (p ^ (j + 1))) * ((y.val : ℕ) : ZMod (p ^ (j + 1)))) := by
        show ringMulPerm a ((nonUnitsEquiv (p := p) j y : _) : ZMod (p ^ (j + 1))) = _
        rw [ringMulPerm_apply, nonUnitsEquiv_apply_coe]
        ring
      rw [hLHS, hRHS]
      -- apply the bridge: both p-multiples reduce mod pʲ to ā · y
      apply mul_p_of_castHom_eq (p := p) (j := j)
      -- LHS reduces mod pʲ to  ā · y
      have hL : ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j))
            (((ringMulPerm (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a) y).val : ℕ)
              : ZMod (p ^ (j + 1)))
          = ringMulPerm (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a) y := by
        rw [map_natCast, ZMod.natCast_zmod_val]
      -- RHS reduces mod pʲ to  ā · y as well
      have hR : ZMod.castHom (pow_dvd_pow p (Nat.le_succ j)) (ZMod (p ^ j))
            ((a : ZMod (p ^ (j + 1))) * ((y.val : ℕ) : ZMod (p ^ (j + 1))))
          = ringMulPerm (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ j)) a) y := by
        rw [map_mul, map_natCast, ZMod.natCast_zmod_val, ringMulPerm_apply]
        congr 1
      rw [hL, hR]
    rw [← hse]
  rw [hA, sign_subtypeCongr, Units.val_mul, hUnits, hNon]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE PRIME-POWER ZOLOTAREV–FROBENIUS IDENTITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Prime-power Zolotarev (Legendre-power form).**  For an odd prime `p` and a
    unit `a : (ℤ/pⁿ)ˣ`, the sign of multiplication by `a` on the whole ring
    `ℤ/pⁿ` is the `n`-th power of the Legendre symbol of `a mod p`. -/
theorem sign_ringMulPerm_eq_legendre_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ (m : ℕ) (a : (ZMod (p ^ (m + 1)))ˣ),
      (Equiv.Perm.sign (ringMulPerm a) : ℤ)
        = (legendreSym p
            ((ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero m)) a : ZMod p).val : ℤ)) ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro a
    rw [sign_ringMulPerm_succ hp2 0 a]
    have htriv : (Equiv.Perm.sign (ringMulPerm
        (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ 0)) a)) : ℤ) = 1 := by
      haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
      have h1 : ringMulPerm (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ 0)) a) = 1 := by
        ext x; exact Subsingleton.elim _ _
      rw [h1]; simp
    rw [htriv, mul_one]
    exact (pow_one _).symm
  | succ k ih =>
    intro a
    have hcomp :
        ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero k))
            (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ (k + 1))) a)
          = ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero (k + 1))) a := by
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    rw [sign_ringMulPerm_succ hp2 (k + 1) a,
      ih (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ (k + 1))) a), hcomp]
    ring

/-- `J(A | pⁿ) = J(A | p)ⁿ = legendreSym p A ^ n` for a prime `p`. -/
theorem jacobiSym_prime_pow {p : ℕ} [Fact p.Prime] (A : ℤ) (m : ℕ) :
    jacobiSym A (p ^ (m + 1)) = (legendreSym p A) ^ (m + 1) := by
  induction m with
  | zero => rw [pow_one, pow_one, jacobiSym.legendreSym.to_jacobiSym]
  | succ k ih =>
    rw [pow_succ p (k + 1), jacobiSym.mul_right, ih, jacobiSym.legendreSym.to_jacobiSym,
      ← pow_succ]

/-- **Prime-power Zolotarev (Jacobi form).**  The sign of multiplication by `a`
    on `ℤ/pⁿ` equals the Jacobi symbol `J(a | pⁿ)`.  This closes the prime-power
    case of the Frobenius/Zolotarev identity. -/
theorem sign_ringMulPerm_eq_jacobiSym {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (m : ℕ) (a : (ZMod (p ^ (m + 1)))ˣ) :
    (Equiv.Perm.sign (ringMulPerm a) : ℤ)
      = jacobiSym ((ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero m)) a : ZMod p).val : ℤ)
          (p ^ (m + 1)) := by
  rw [sign_ringMulPerm_eq_legendre_pow hp2 m a, jacobiSym_prime_pow]

end ZolotarevPrimePowerWhole

#check @ZolotarevPrimePowerWhole.sign_ringMulPerm_eq_legendre_pow
#check @ZolotarevPrimePowerWhole.sign_ringMulPerm_eq_jacobiSym
