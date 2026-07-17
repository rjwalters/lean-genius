/-
# Hexagrammum Mysticum — OQ-03: the reflection coset of the hexagonal group

The parent file `PascalsHexagonOQ03` builds the dihedral symmetry group
`hexagonalGroup = ⟨hexRot, hexRev⟩ ≤ Sym(6)` behind the Pascal-line map: it
proves the rotation `hexRot = finRotate 6` has order 6, the reversal
`hexRev = Fin.rev` is an involution, the conjugation relation
`s·r·s = r⁻¹`, and the isomorphism to `DihedralGroup 6` (order 12).

What the parent does *not* record is the **reflection coset** — the six
non-rotation elements `r^k·s`.  In a dihedral group these are exactly the
reflections, and they carry the multiplication table that makes the group
non-abelian.  This file supplies that layer, fully self-contained and
axiom-free (the base relations `r^6 = 1`, `s^2 = 1`, `s·r·s = r⁻¹` are
re-established here by `decide`, so nothing depends on the parent's
Cayley–Bacharach axiom or its two open combinatorial `sorry`s):

  * `hexRefl k := hexRot^k * hexRev`         — the `k`-th reflection;
  * `hexRefl_mul_self`                        — **every reflection is an
                                                 involution** `(r^k s)^2 = 1`;
  * `hexRefl_inv`                             — a reflection is self-inverse;
  * `hexRot_pow_mul_hexRefl`                  — `r^a · (r^b s) = r^{a+b} s`
                                                 (rotations act simply-transitively
                                                 on the reflection coset);
  * `hexRefl_mul_hexRefl`                     — **the product of two reflections
                                                 is a rotation** `r^a·(r^b)⁻¹`;
  * `hexRefl_left_cancel`                     — reflections are indexed injectively
                                                 by their rotation part;
  * `hexRot_mul_hexRev_ne_hexRev_mul_hexRot`  — `r·s ≠ s·r`: **the group is
                                                 non-abelian**;
  * `hexRefl_mem_closure`                     — every reflection lies in
                                                 `⟨hexRot, hexRev⟩`.

Together with the parent's rotation relations this gives the complete Cayley
table of the `D₆`-symmetry acting on a hexagon inscribed in a conic, the group
under which the Pascal line of the Hexagrammum Mysticum is invariant.

Reference: Pascal's theorem / Hexagrammum Mysticum, Erdős-adjacent OQ-03.
-/

import Mathlib

namespace PascalsHexagonOQ03Reflections

open Equiv

/-- Cyclic rotation of `Fin 6` by one position (`Mathlib`'s `finRotate 6`). -/
def hexRot : Equiv.Perm (Fin 6) := finRotate 6

/-- Reversal of `Fin 6`: `i ↦ 5 - i` (`Mathlib`'s `Fin.rev`). -/
def hexRev : Equiv.Perm (Fin 6) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

/-! ## The three dihedral relations (re-established here by `decide`). -/

/-- `hexRot ^ 6 = 1`. -/
theorem hexRot_pow_six : hexRot ^ 6 = 1 := by
  ext i; fin_cases i <;> decide

/-- `hexRev` is an involution: `hexRev * hexRev = 1`. -/
theorem hexRev_mul_self : hexRev * hexRev = 1 := by
  ext i; fin_cases i <;> decide

/-- Conjugation relation: `hexRev * hexRot * hexRev = hexRot⁻¹`. -/
theorem hexRev_hexRot_hexRev : hexRev * hexRot * hexRev = hexRot⁻¹ := by
  ext i; fin_cases i <;> decide

/-- `hexRev` is self-inverse. -/
theorem hexRev_inv : hexRev⁻¹ = hexRev :=
  inv_eq_of_mul_eq_one_right hexRev_mul_self

/-- `hexRev` is not the identity (it swaps `0` and `5`). -/
theorem hexRev_ne_one : hexRev ≠ 1 := by
  intro h
  have : hexRev 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  simp [hexRev, Fin.rev] at this

/-- **`orderOf hexRev = 2`**: the reversal is an involution distinct from `1`. -/
theorem orderOf_hexRev : orderOf hexRev = 2 := by
  apply (orderOf_eq_iff (by norm_num)).mpr
  refine ⟨by rw [pow_two]; exact hexRev_mul_self, ?_⟩
  intro m hlt hm
  interval_cases m
  rw [pow_one]; exact hexRev_ne_one

/-- Powered conjugation: `hexRev * hexRot ^ n * hexRev = (hexRot ^ n)⁻¹`.
    The `SemiconjBy` extension of `hexRev_hexRot_hexRev` to all powers. -/
theorem hexRev_hexRot_pow_hexRev (n : ℕ) :
    hexRev * hexRot ^ n * hexRev = (hexRot ^ n)⁻¹ := by
  have hsc : SemiconjBy hexRev hexRot hexRot⁻¹ := by
    unfold SemiconjBy
    calc hexRev * hexRot
        = hexRev * hexRot * (hexRev * hexRev) := by rw [hexRev_mul_self, mul_one]
      _ = (hexRev * hexRot * hexRev) * hexRev := by rw [← mul_assoc]
      _ = hexRot⁻¹ * hexRev := by rw [hexRev_hexRot_hexRev]
  have h : SemiconjBy hexRev (hexRot ^ n) (hexRot⁻¹ ^ n) := hsc.pow_right n
  rw [inv_pow] at h
  rw [h.eq, mul_assoc, hexRev_mul_self, mul_one]

/-! ## The reflection coset `{ r^k · s }`. -/

/-- The `k`-th reflection of the hexagonal group: `r^k · s`. -/
def hexRefl (k : ℕ) : Equiv.Perm (Fin 6) := hexRot ^ k * hexRev

/-- `hexRefl 0` is the reversal `hexRev` itself. -/
theorem hexRefl_zero : hexRefl 0 = hexRev := by
  simp [hexRefl]

/-- **Every reflection is an involution**: `(r^k · s)^2 = 1`.  The heart of the
    dihedral structure: `r^k s · r^k s = r^k (s r^k s) = r^k (r^k)⁻¹ = 1`. -/
theorem hexRefl_mul_self (k : ℕ) : hexRefl k * hexRefl k = 1 := by
  have h : hexRefl k * hexRefl k = hexRot ^ k * (hexRev * hexRot ^ k * hexRev) := by
    unfold hexRefl; group
  rw [h, hexRev_hexRot_pow_hexRev]; group

/-- A reflection is its own inverse. -/
theorem hexRefl_inv (k : ℕ) : (hexRefl k)⁻¹ = hexRefl k :=
  inv_eq_of_mul_eq_one_right (hexRefl_mul_self k)

/-- **Rotations act on the reflection coset by index translation**:
    `r^a · (r^b · s) = r^{a+b} · s`.  The six reflections `hexRefl 0,…,hexRefl 5`
    form a single orbit under the rotation subgroup, acting simply transitively. -/
theorem hexRot_pow_mul_hexRefl (a b : ℕ) :
    hexRot ^ a * hexRefl b = hexRefl (a + b) := by
  unfold hexRefl
  rw [← mul_assoc, ← pow_add]

/-- **The product of two reflections is a rotation**: `(r^a s)(r^b s) = r^a (r^b)⁻¹`.
    This is why the reflections do not form a subgroup, and why composing two of
    them lands back in the cyclic rotation part — the defining feature of `D₆`. -/
theorem hexRefl_mul_hexRefl (a b : ℕ) :
    hexRefl a * hexRefl b = hexRot ^ a * (hexRot ^ b)⁻¹ := by
  have h : hexRefl a * hexRefl b = hexRot ^ a * (hexRev * hexRot ^ b * hexRev) := by
    unfold hexRefl; group
  rw [h, hexRev_hexRot_pow_hexRev]

/-- **Reflections are indexed injectively by their rotation part**: if two
    reflections coincide then so do the underlying rotations.  (Right-cancel the
    common factor `hexRev`.) -/
theorem hexRefl_left_cancel {a b : ℕ} (h : hexRefl a = hexRefl b) :
    hexRot ^ a = hexRot ^ b := by
  unfold hexRefl at h
  exact mul_right_cancel h

/-- **The hexagonal group is non-abelian**: `r · s ≠ s · r`.  Concretely
    `(r·s)(0) = 0` while `(s·r)(0) = 4`, so the two products differ. -/
theorem hexRot_mul_hexRev_ne_hexRev_mul_hexRot :
    hexRot * hexRev ≠ hexRev * hexRot := by
  intro h
  have h0 : (hexRot * hexRev) 0 = (hexRev * hexRot) 0 := by rw [h]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h0
  revert h0
  decide

/-- Every reflection lies in the hexagonal group `⟨hexRot, hexRev⟩`. -/
theorem hexRefl_mem_closure (k : ℕ) :
    hexRefl k ∈ Subgroup.closure ({hexRot, hexRev} : Set (Equiv.Perm (Fin 6))) := by
  apply Subgroup.mul_mem
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) k
  · exact Subgroup.subset_closure (by simp)

end PascalsHexagonOQ03Reflections
