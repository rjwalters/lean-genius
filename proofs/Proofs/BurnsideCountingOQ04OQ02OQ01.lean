import Mathlib.Tactic
import Proofs.BurnsideCountingOQ04OQ02

/-
# Burnside Counting, OQ-04 → OQ-02 → OQ-01: the rotation half is the gcd-cycle sum

## What this file proves

The parent file `BurnsideCountingOQ04OQ02` built, for every `n`, the dihedral action of
`Dₙ` on the binary colourings `Coloring n = ZMod n → Fin 2` of the `n`-cycle and the
orbit-counting identity

      ∑_{g ∈ Dₙ} |Fix(g)|  =  b(n) · (2n)            (`bracelet_burnside`),

leaving the *closed* evaluation of each side as documented follow-up.  This file discharges
the **rotation half** of that left-hand sum: it evaluates `∑_{rotations} |Fix(r i)|` as the
**gcd-cycle sum**

      ∑_{i ∈ ZMod n} |Fix(r i)|  =  ∑_{i ∈ ZMod n} 2 ^ gcd(n, i)            (`rotation_sum_eq_gcd_cycle_sum`).

The single new ingredient is the per-rotation count

      |Fix(r i)|  =  2 ^ gcd(n, i)            (`card_fixedBy_rotation`).

## Why `gcd(n, i)`

A colouring is fixed by the rotation `r i` (which acts on positions by `x ↦ x + i`) exactly
when it is **constant on the `⟨i⟩-orbits** of `ZMod n`, i.e. constant on the cosets of the
cyclic subgroup `H = ⟨i⟩ = AddSubgroup.zmultiples i`.  Such colourings are therefore in
bijection with functions `(ZMod n ⧸ H) → Fin 2`, of which there are `2 ^ [ZMod n : H]`.  The
index is computed by Lagrange together with `addOrderOf (i : ZMod n) = n / gcd(n, i)`:

      [ZMod n : H]  =  n / |H|  =  n / addOrderOf i  =  n / (n / gcd(n, i))  =  gcd(n, i).

The number of orbits of the rotation is exactly `gcd(n, i)`, recovering the classical fact
that adding `i` modulo `n` decomposes the `n` positions into `gcd(n, i)` cycles.

## Proof strategy

* `rotation_smul_apply`: unfold the parent action at a rotation, `(r i • c) p = c (p - i)`.
* `fixed_iff_periodic`: `r i • c = c ↔ c` is `i`-periodic.
* `periodic_zsmul`: an `i`-periodic colouring is invariant under every `k • i`, `k : ℤ`
  (`Int.induction_on`).
* `fixedRotationEquiv`: the bijection `Fix(r i) ≃ (ZMod n ⧸ ⟨i⟩ → Fin 2)`.
* `card_quotient_zmultiples`: `[ZMod n : ⟨i⟩] = gcd(n, i)` via Lagrange + `addOrderOf_coe`.

`#print axioms` confirms only `propext, Classical.choice, Quot.sound` — no `native_decide`.
-/

namespace BurnsideCountingOQ04OQ02OQ01

open Finset MulAction AddSubgroup BurnsideCountingOQ04OQ02

variable {n : ℕ}

/-! ### Unfolding the rotation action -/

/-- The rotation `r i` acts on a colouring by translating the *argument* by `-i`:
`(r i • c) p = c (p - i)`.  This reads off the parent's `smul_apply` at `g = r i`, where the
position permutation is `ρ (r i) = Equiv.addRight i`, whose inverse is `· - i`. -/
theorem rotation_smul_apply (i : ZMod n) (c : Coloring n) (p : ZMod n) :
    ((DihedralGroup.r i : DihedralGroup n) • c) p = c (p - i) := by
  rw [smul_apply]
  congr 1
  have hρ : (ρ (DihedralGroup.r i) : Equiv.Perm (ZMod n)) = Equiv.addRight i := rfl
  rw [hρ, Equiv.symm_apply_eq]; simp

/-- A colouring is fixed by the rotation `r i` iff it is `i`-periodic: `c (p - i) = c p`. -/
theorem fixed_iff_periodic (i : ZMod n) (c : Coloring n) :
    (DihedralGroup.r i : DihedralGroup n) • c = c ↔ ∀ p, c (p - i) = c p := by
  constructor
  · intro h p
    have := congrFun h p
    rwa [rotation_smul_apply] at this
  · intro h
    funext p
    rw [rotation_smul_apply]
    exact h p

/-- An `i`-periodic colouring is invariant under translation by every integer multiple of `i`:
`c (a + k • i) = c a` for all `k : ℤ`.  Proved by integer induction, using the periodicity in
both the `+ i` and `- i` directions. -/
theorem periodic_zsmul (i : ZMod n) {c : Coloring n} (hc : ∀ p, c (p - i) = c p) :
    ∀ (k : ℤ) (a : ZMod n), c (a + k • i) = c a := by
  have hplus : ∀ p, c (p + i) = c p := by
    intro p; have h := hc (p + i); rw [add_sub_cancel_right] at h; exact h.symm
  intro k
  induction k using Int.induction_on with
  | zero => intro a; simp
  | succ k ih =>
    intro a
    have key : a + (k + 1 : ℤ) • i = a + (k : ℤ) • i + i := by
      rw [add_smul, one_smul, add_assoc]
    rw [key, hplus]; exact ih a
  | pred k ih =>
    intro a
    have key : a + (-(k : ℤ) - 1) • i = a + (-(k : ℤ)) • i - i := by
      rw [sub_smul, one_smul, ← add_sub_assoc]
    rw [key, hc]; exact ih a

/-! ### The bijection with functions on the orbit quotient -/

/-- **Fixed colourings ≃ functions on the orbit quotient.**  A colouring fixed by `r i` is
constant on the cosets of `H = ⟨i⟩`, so it descends to a function on `ZMod n ⧸ H`; conversely
any function on the quotient pulls back to an `i`-periodic colouring.  These are mutually
inverse. -/
def fixedRotationEquiv (i : ZMod n) :
    ↥(fixedBy (Coloring n) (DihedralGroup.r i))
      ≃ (ZMod n ⧸ AddSubgroup.zmultiples i → Fin 2) where
  toFun c := Quotient.lift c.1 (by
    intro a b hab
    replace hab : -a + b ∈ AddSubgroup.zmultiples i := QuotientAddGroup.leftRel_apply.mp hab
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hab
    have hper : ∀ p, c.1 (p - i) = c.1 p :=
      (fixed_iff_periodic i c.1).mp ((mem_fixedBy).mp c.2)
    have hb : b = a + k • i := by rw [hk]; abel
    rw [hb, periodic_zsmul i hper k a])
  invFun f :=
    ⟨fun p => f (QuotientAddGroup.mk p), by
      rw [mem_fixedBy, fixed_iff_periodic]
      intro p
      show f (QuotientAddGroup.mk (p - i)) = f (QuotientAddGroup.mk p)
      congr 1
      rw [QuotientAddGroup.eq]
      have : -(p - i) + p = i := by abel
      rw [this]
      exact AddSubgroup.mem_zmultiples i⟩
  left_inv := by
    rintro ⟨c, hc⟩
    rfl
  right_inv := by
    intro f
    funext q
    induction q using QuotientAddGroup.induction_on with
    | _ a => rfl

/-! ### Counting the quotient: the index is `gcd(n, i)` -/

/-- **Index of the rotation subgroup.**  The cyclic subgroup `⟨i⟩ ≤ ZMod n` has index
`gcd(n, i)`: by Lagrange the index is `n / |⟨i⟩| = n / addOrderOf i`, and
`addOrderOf (i : ZMod n) = n / gcd(n, i)`. -/
theorem card_quotient_zmultiples [NeZero n] (i : ZMod n) :
    Nat.card (ZMod n ⧸ AddSubgroup.zmultiples i) = Nat.gcd n i.val := by
  have hn : n ≠ 0 := NeZero.ne n
  -- addOrderOf i = n / gcd(n, i.val)
  have hord : addOrderOf i = n / Nat.gcd n i.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val i]
    exact ZMod.addOrderOf_coe i.val hn
  -- Lagrange: n = card quotient * card subgroup
  have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples i)
  rw [Nat.card_zmultiples, hord, Nat.card_zmod] at hlag
  -- hlag : n = Nat.card (quotient) * (n / gcd)
  have hgdvd : Nat.gcd n i.val ∣ n := Nat.gcd_dvd_left _ _
  have hgpos : 0 < Nat.gcd n i.val := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  have hdpos : 0 < n / Nat.gcd n i.val := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hgdvd) hgpos
  -- gcd * (n / gcd) = n, so n = card * (n/gcd) = gcd * (n/gcd) ⟹ card = gcd
  have hmul : Nat.gcd n i.val * (n / Nat.gcd n i.val) = n := Nat.mul_div_cancel' hgdvd
  have : Nat.card (ZMod n ⧸ AddSubgroup.zmultiples i) * (n / Nat.gcd n i.val)
      = Nat.gcd n i.val * (n / Nat.gcd n i.val) := by
    rw [hmul, ← hlag]
  exact Nat.eq_of_mul_eq_mul_right hdpos this

/-! ### The per-rotation fixed count and the rotation half -/

/-- **Per-rotation count.**  The number of binary colourings fixed by the rotation `r i` is
`2 ^ gcd(n, i)`: the colourings are functions on the `gcd(n, i)` rotation orbits. -/
theorem card_fixedBy_rotation [NeZero n] (i : ZMod n) :
    Fintype.card (fixedBy (Coloring n) (DihedralGroup.r i)) = 2 ^ Nat.gcd n i.val := by
  classical
  rw [Fintype.card_congr (fixedRotationEquiv i), Fintype.card_fun, Fintype.card_fin]
  congr 1
  rw [← Nat.card_eq_fintype_card, card_quotient_zmultiples]

/-- **The rotation half of the Burnside sum is the gcd-cycle sum.**

      ∑_{i ∈ ZMod n} |Fix(r i)|  =  ∑_{i ∈ ZMod n} 2 ^ gcd(n, i).

This is the closed evaluation, promised by the parent, of the rotation contribution to the
bracelet orbit-counting identity. -/
theorem rotation_sum_eq_gcd_cycle_sum [NeZero n] :
    ∑ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.r i))
      = ∑ i : ZMod n, 2 ^ Nat.gcd n i.val := by
  exact Finset.sum_congr rfl (fun i _ => card_fixedBy_rotation i)

end BurnsideCountingOQ04OQ02OQ01

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ02OQ01.card_fixedBy_rotation
#print axioms BurnsideCountingOQ04OQ02OQ01.rotation_sum_eq_gcd_cycle_sum
