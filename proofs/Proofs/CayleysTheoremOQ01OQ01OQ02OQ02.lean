/-
Proof: The centralizer of the left-regular image is the right-regular image,
and the two regular representations have equal image iff the group is abelian.
Research: cayleys-theorem-oq-01-oq-01-oq-02-oq-02

Open question (from the `cayleys-theorem-oq-01-oq-01-oq-02` chain):
  Cayley's theorem embeds a group `G` into `Equiv.Perm G` as the *left-regular*
  representation `L g : x ↦ g * x`.  Identify the centralizer of `L(G)` inside
  the full symmetric group `Equiv.Perm G`, and characterise exactly when the
  left- and right-regular representations coincide.

This file works directly over `Equiv.Perm G` for an arbitrary group `G` (no
finiteness assumption — strictly more general than the parent's `Fin n` setting).
We define the two regular representations as genuine group homomorphisms:

* **Left regular** `leftReg G : G →* Equiv.Perm G`, `leftReg G g = Equiv.mulLeft g`,
  i.e. `x ↦ g * x`.  Since `Equiv.mulLeft (a*b) = Equiv.mulLeft a * Equiv.mulLeft b`
  this is a homomorphism on the nose.
* **Right regular** `rightReg G : G →* Equiv.Perm G`, `rightReg G g = Equiv.mulRight g⁻¹`,
  i.e. `x ↦ x * g⁻¹`.  The inverse is forced: plain right multiplication is an
  *anti*-homomorphism (`mulRight (a*b) = mulRight b * mulRight a`), so inverting
  the argument repairs the order and makes `rightReg` a homomorphism.

Main results:

* `centralizer_leftReg_range`:
    `Subgroup.centralizer ↑(leftReg G).range = (rightReg G).range`.
  A permutation commutes with every left translation iff it is a right
  translation.  The forward direction is the classical "evaluate at `1`" trick:
  if `σ` commutes with all `L g`, then `σ x = x * σ 1`, so `σ = mulRight (σ 1)`.
* `centralizer_rightReg_range`: the mirror statement, with the roles swapped.
* `leftReg_range_eq_rightReg_range_iff`:
    `(leftReg G).range = (rightReg G).range ↔ ∀ x y : G, x * y = y * x`.
  The two regular images coincide exactly when `G` is abelian.

Together these say: the centralizer of the regular representation is the *other*
regular representation (the structural fact underlying the holomorph of `G`),
and the two only collapse onto each other in the commutative case.  We also
record that both representations are faithful (`leftReg_injective`,
`rightReg_injective`), so the abelian characterisation is genuinely about `G`.
-/

import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic

namespace CayleyCentralizer

variable {G : Type*} [Group G]

/-- The **left-regular representation** `g ↦ (x ↦ g * x)` as a group
homomorphism into the symmetric group on `G`.  It is a homomorphism because
`Equiv.mulLeft` turns multiplication into composition. -/
def leftReg (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := Equiv.mulLeft_one
  map_mul' := Equiv.mulLeft_mul

/-- The **right-regular representation** `g ↦ (x ↦ x * g⁻¹)` as a group
homomorphism.  The inverse on the argument is what makes it a homomorphism:
without it, `Equiv.mulRight` is an anti-homomorphism. -/
def rightReg (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun g := Equiv.mulRight g⁻¹
  map_one' := by rw [inv_one, Equiv.mulRight_one]
  map_mul' a b := by rw [mul_inv_rev, Equiv.mulRight_mul]

@[simp] theorem leftReg_apply (g x : G) : leftReg G g x = g * x := rfl

@[simp] theorem rightReg_apply (g x : G) : rightReg G g x = x * g⁻¹ := rfl

/-- The left-regular representation is faithful. -/
theorem leftReg_injective : Function.Injective (leftReg G) := by
  intro a b hab
  have h := DFunLike.congr_fun hab 1
  rwa [leftReg_apply, leftReg_apply, mul_one, mul_one] at h

/-- The right-regular representation is faithful. -/
theorem rightReg_injective : Function.Injective (rightReg G) := by
  intro a b hab
  have h := DFunLike.congr_fun hab 1
  rw [rightReg_apply, rightReg_apply, one_mul, one_mul] at h
  exact inv_injective h

/-- **Centralizer of the left-regular image.**  A permutation of `G` commutes
with every left translation iff it is itself a right translation.  Hence the
centralizer of `L(G)` inside `Equiv.Perm G` is exactly `R(G)`. -/
theorem centralizer_leftReg_range :
    Subgroup.centralizer (↑(leftReg G).range : Set (Equiv.Perm G)) = (rightReg G).range := by
  apply le_antisymm
  · -- A centralizing `σ` satisfies `σ x = x * σ 1`, so `σ = rightReg (σ 1)⁻¹`.
    intro σ hσ
    rw [Subgroup.mem_centralizer_iff] at hσ
    refine ⟨(σ 1)⁻¹, ?_⟩
    ext x
    rw [rightReg_apply, inv_inv]
    have hcomm := hσ (leftReg G x) ⟨x, rfl⟩
    have h := DFunLike.congr_fun hcomm 1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, leftReg_apply, leftReg_apply, mul_one] at h
    exact h
  · -- Right translations commute with left translations by associativity.
    rintro σ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨g', rfl⟩
    ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, leftReg_apply, rightReg_apply,
      rightReg_apply, leftReg_apply, mul_assoc]

/-- **Centralizer of the right-regular image** — the mirror statement.  A
permutation commutes with every right translation iff it is a left translation. -/
theorem centralizer_rightReg_range :
    Subgroup.centralizer (↑(rightReg G).range : Set (Equiv.Perm G)) = (leftReg G).range := by
  apply le_antisymm
  · -- A centralizing `σ` satisfies `σ x = σ 1 * x`, so `σ = leftReg (σ 1)`.
    intro σ hσ
    rw [Subgroup.mem_centralizer_iff] at hσ
    refine ⟨σ 1, ?_⟩
    ext x
    rw [leftReg_apply]
    have hcomm := hσ (rightReg G x⁻¹) ⟨x⁻¹, rfl⟩
    have h := DFunLike.congr_fun hcomm 1
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, rightReg_apply, rightReg_apply,
      inv_inv, one_mul] at h
    exact h
  · -- Left translations commute with right translations by associativity.
    rintro σ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨g', rfl⟩
    ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, rightReg_apply, leftReg_apply,
      leftReg_apply, rightReg_apply, mul_assoc]

/-- **Left and right regular images coincide iff the group is abelian.**  The
two regular representations of `G` have the same image inside `Equiv.Perm G`
exactly when `G` is commutative. -/
theorem leftReg_range_eq_rightReg_range_iff :
    (leftReg G).range = (rightReg G).range ↔ ∀ x y : G, x * y = y * x := by
  constructor
  · intro hEq x y
    -- `leftReg x` lies in `rightReg`'s range, forcing `mulLeft x = mulRight x`.
    have hmem : (leftReg G) x ∈ (rightReg G).range := by rw [← hEq]; exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    -- Evaluate at `1`: `z⁻¹ = x`, i.e. `z = x⁻¹`.
    have h1 := DFunLike.congr_fun hz 1
    rw [rightReg_apply, leftReg_apply, one_mul, mul_one] at h1
    have hzx : z = x⁻¹ := by rw [← h1, inv_inv]
    -- Evaluate at `y`: `y * x = x * y`.
    have hy := DFunLike.congr_fun hz y
    rw [rightReg_apply, leftReg_apply, hzx, inv_inv] at hy
    exact hy.symm
  · intro hcomm
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      ext x
      rw [rightReg_apply, inv_inv, leftReg_apply]
      exact (hcomm g x).symm
    · rintro _ ⟨g, rfl⟩
      refine ⟨g⁻¹, ?_⟩
      ext x
      rw [leftReg_apply, rightReg_apply]
      exact hcomm g⁻¹ x

/-- Consequence: the left-regular image is abelian (as a subgroup of `Equiv.Perm G`)
iff `G` is abelian — it sits inside its own centralizer exactly when the two
regular images coincide. -/
theorem leftReg_range_le_centralizer_iff :
    (leftReg G).range ≤ Subgroup.centralizer (↑(leftReg G).range : Set (Equiv.Perm G)) ↔
      ∀ x y : G, x * y = y * x := by
  rw [centralizer_leftReg_range]
  constructor
  · intro hle x y
    have hmem : (leftReg G) x ∈ (rightReg G).range := hle ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    have h1 := DFunLike.congr_fun hz 1
    rw [rightReg_apply, leftReg_apply, one_mul, mul_one] at h1
    have hzx : z = x⁻¹ := by rw [← h1, inv_inv]
    have hy := DFunLike.congr_fun hz y
    rw [rightReg_apply, leftReg_apply, hzx, inv_inv] at hy
    exact hy.symm
  · intro hcomm
    rw [(leftReg_range_eq_rightReg_range_iff).mpr hcomm]

end CayleyCentralizer
