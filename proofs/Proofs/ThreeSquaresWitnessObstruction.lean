import Mathlib
import Proofs.ThreeSquaresSufficiency

/-!
# The Dirichlet-witness obstruction at residue `3 (mod 4)`

`Proofs.ThreeSquares` funnels the **entire** sufficiency direction of Legendre's
three-square theorem through the single axiom

    dirichlet_key_lemma {n d p} (hn : n > 1) (hd : d > 0) (hp : p = d * n - 1)
        [Fact p.Prime] (hqr : legendreSym p (-d) = 1) :
        ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n          (ThreeSquares.lean:615)

and `Proofs.ThreeSquaresSufficiency` isolates the remaining open content as the
existence statement `ThreeSquares.DirichletWitnessProperty`: *for every*
non-excluded `m` with `4 ∤ m` and `m > 1`, a witness `(d, p)` with `p = d·m − 1`
prime and `legendreSym p (−d) = 1` exists.

**This file proves that `DirichletWitnessProperty` is FALSE.**  Earlier sessions
only *numerically* certified (`verify_three_squares_residue_routes.py`, audit PR
#24529) that the witness is unsatisfiable for 4-free cores `m ≡ 3 (mod 8)`.  The
real obstruction is sharper and is a *theorem*, proved here from quadratic
reciprocity:

> **`witness_obstruction_residue3`.**  If `m ≡ 3 (mod 4)`, `p ≠ 2` is prime, and
> `p = d·m − 1` with `d > 0`, then `legendreSym p (−d) = −1`.

The derivation: with `d·m = p + 1` one has `(−d)·m ≡ −1 (mod p)`, so
`J(−d|p)·J(m|p) = J(−1|p) = χ₄ p`.  Reciprocity gives
`J(m|p) = (−1)^{(m/2)(p/2)}·J(p|m)`, and `p ≡ −1 (mod m)` makes
`J(p|m) = J(−1|m) = χ₄ m = −1` (since `m ≡ 3 mod 4`).  As `m/2` is odd, the sign
collapses to `χ₄ p`, whence `J(m|p) = −χ₄ p` and `J(−d|p) = −1`.

**Consequence.**  The single-`dirichlet_key_lemma` architecture cannot represent
any non-excluded core `m ≡ 3 (mod 4)`; that class must instead be handled by the
two-square route in `Proofs.ThreeSquaresResidue3` (`Nat.Prime.sq_add_sq`).  Thus
the corrected sufficiency property must restrict the Dirichlet witness to
`m % 4 ≠ 3` and dispatch `m % 4 = 3` separately.  The concrete falsity witness is
`m = 11` (`= 3² + 1² + 1²`, non-excluded, `4 ∤ 11`), for which every prime
`p = 11d − 1` is odd, so the obstruction applies and no witness exists.

NOTE: build-pending — written under a Docker blackout (host `lake`/Docker
unavailable). Not registered in `Proofs.lean`; harmless to the build until a
post-blackout session verifies it via `./proofs/scripts/docker-build.sh`.  All
Mathlib bearers were name-checked against the pinned manifest rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
-/

open ZMod

namespace ThreeSquaresWitnessObstruction

/-- **Witness obstruction at residue `3 (mod 4)`.**

For `m ≡ 3 (mod 4)`, any odd prime `p = d·m − 1` (with `d > 0`) makes `−d` a
quadratic *non*-residue mod `p`, i.e. `legendreSym p (−d) = −1`.  Hence the
`dirichlet_key_lemma` witness `legendreSym p (−d) = 1` is unsatisfiable on this
residue class. -/
theorem witness_obstruction_residue3
    {m d p : ℕ} (hm4 : m % 4 = 3) (hp2 : p ≠ 2) (hd : 0 < d)
    (hpeq : p = d * m - 1) [Fact (Nat.Prime p)] :
    legendreSym p (-(d : ℤ)) = -1 := by
  have hpp : Nat.Prime p := Fact.out
  have hm0 : 0 < m := by omega
  have hp_odd : Odd p := hpp.odd_of_ne_two hp2
  have hp_odd' : p % 2 = 1 := Nat.odd_iff.mp hp_odd
  have hm_odd : Odd m := by rw [Nat.odd_iff]; omega
  have hm2odd : (m / 2) % 2 = 1 := by omega
  -- `d * m = p + 1`
  have hmul : 0 < d * m := Nat.mul_pos hd hm0
  have hdm : d * m = p + 1 := by omega
  have hdmZ : (d : ℤ) * (m : ℤ) = (p : ℤ) + 1 := by exact_mod_cast hdm
  -- `(-d) * m ≡ -1 (mod p)`, hence `J(-d|p) · J(m|p) = χ₄ p`
  have hmod : (-((p : ℤ) + 1)) % (p : ℤ) = (-1 : ℤ) % (p : ℤ) := by
    have h : (-((p : ℤ) + 1)) = -1 + (p : ℤ) * (-1) := by ring
    rw [h, Int.add_mul_emod_self_left]
  have key : jacobiSym (-(d : ℤ)) p * jacobiSym ((m : ℤ)) p = χ₄ (p : ZMod 4) := by
    rw [← jacobiSym.mul_left]
    rw [show (-(d : ℤ)) * (m : ℤ) = -((p : ℤ) + 1) from by linear_combination -hdmZ]
    rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hp_odd]
  -- `p ≡ -1 (mod m)`, hence `J(p|m) = J(-1|m) = χ₄ m = -1`
  have hpmod : (p : ℤ) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) := by
    have h : (p : ℤ) = -1 + (m : ℤ) * (d : ℤ) := by linear_combination -hdmZ
    rw [h, Int.add_mul_emod_self_left]
  have hpm : jacobiSym ((p : ℤ)) m = -1 := by
    rw [jacobiSym.mod_left' hpmod, jacobiSym.at_neg_one hm_odd, χ₄_nat_three_mod_four hm4]
  -- the reciprocity sign `(-1)^{(m/2)(p/2)}` collapses to `χ₄ p` (since `m/2` is odd)
  have hsign : ((-1 : ℤ)) ^ (m / 2 * (p / 2)) = χ₄ (p : ZMod 4) := by
    rw [pow_mul, Odd.neg_one_pow (Nat.odd_iff.mpr hm2odd), χ₄_eq_neg_one_pow hp_odd']
  -- `J(m|p) = -χ₄ p`
  have hmp : jacobiSym ((m : ℤ)) p = -(χ₄ (p : ZMod 4)) := by
    rw [jacobiSym.quadratic_reciprocity hm_odd hp_odd, hsign, hpm]; ring
  -- combine: `J(-d|p) · (-χ₄ p) = χ₄ p` with `(χ₄ p)² = 1`
  have hjval : jacobiSym (-(d : ℤ)) p * (-(χ₄ (p : ZMod 4))) = χ₄ (p : ZMod 4) := by
    rw [← hmp]; exact key
  have hc2 : χ₄ (p : ZMod 4) * χ₄ (p : ZMod 4) = 1 := by
    rw [χ₄_eq_neg_one_pow hp_odd', ← pow_add]
    exact (⟨p / 2, rfl⟩ : Even (p / 2 + p / 2)).neg_one_pow
  rw [legendreSym.to_jacobiSym]
  calc jacobiSym (-(d : ℤ)) p
      = jacobiSym (-(d : ℤ)) p * (χ₄ (p : ZMod 4) * χ₄ (p : ZMod 4)) := by rw [hc2, mul_one]
    _ = (jacobiSym (-(d : ℤ)) p * (-(χ₄ (p : ZMod 4)))) * (-(χ₄ (p : ZMod 4))) := by ring
    _ = χ₄ (p : ZMod 4) * (-(χ₄ (p : ZMod 4))) := by rw [hjval]
    _ = -(χ₄ (p : ZMod 4) * χ₄ (p : ZMod 4)) := by ring
    _ = -1 := by rw [hc2]

/-- **The Dirichlet witness property is false.**

`ThreeSquares.DirichletWitnessProperty` claims a Dirichlet witness for *every*
non-excluded `m` with `4 ∤ m` and `m > 1`.  But `m = 11` (`= 3² + 1² + 1²`, so
non-excluded; `4 ∤ 11`) admits no witness: any prime `p = 11·d − 1` is odd, and
`witness_obstruction_residue3` forces `legendreSym p (−d) = −1 ≠ 1`. -/
theorem not_dirichletWitnessProperty : ¬ ThreeSquares.DirichletWitnessProperty := by
  intro H
  have h11sum : ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = ((11 : ℕ) : ℤ) :=
    ⟨3, 1, 1, by norm_num⟩
  have hne : ¬ ThreeSquares.IsExcludedForm 11 :=
    fun hx => ThreeSquares.excluded_form_not_sum_three_sq hx h11sum
  have h4 : ¬ (4 ∣ 11) := by decide
  obtain ⟨d, p, hd, _hd2, hp, hpp, hqr⟩ := H (m := 11) hne h4 (by norm_num)
  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  have hp2 : p ≠ 2 := by intro h; subst h; omega
  have hobs : legendreSym p (-(d : ℤ)) = -1 :=
    witness_obstruction_residue3 (by norm_num) hp2 hd hp
  rw [hobs] at hqr
  norm_num at hqr

end ThreeSquaresWitnessObstruction
