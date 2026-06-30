import Mathlib

/-
# Dihedral groups are solvable — an infinite solvable family beyond Sₙ

`abel-ruffini-oq-04-oq-02-oq-04`

The parent entry `abel-ruffini-oq-04-oq-02` ("S₂, S₃, S₄ Are Solvable") classifies
solvability for the symmetric groups and asks, among its open questions:

> "What about other infinite families? Can analogues be proved for dihedral groups
>  `Dₙ` (solvable for all `n`, since they have cyclic subgroups of index 2), or for the
>  general linear groups `GLₙ(𝔽ₚ)` (not solvable for `n ≥ 2`)?"

This file settles the **dihedral half**: `DihedralGroup n` is solvable for *every* `n`
(including `n = 0`, the infinite dihedral group).  Unlike `Sₙ`, which becomes
non-solvable at `n = 5`, the dihedral family is solvable across the board — a clean
contrast that illustrates how the Abel–Ruffini obstruction is special to the symmetric
groups, not a generic feature of infinite families of finite groups.

## The structural reason, formalized

`Dₙ` is **metabelian**: it has the cyclic (hence abelian) rotation subgroup `⟨r⟩ ≅ ℤ/n`
as a normal subgroup of index `2`, with abelian quotient `ℤ/2`.  Concretely we exhibit

* an inclusion `rotation : Multiplicative (ZMod n) →* DihedralGroup n`, `i ↦ r i`, whose
  range is the rotation subgroup, and
* a parity homomorphism `parity : DihedralGroup n →* Multiplicative (ZMod 2)` sending
  every rotation to `1` and every reflection to the generator,

and observe `ker (parity) = range (rotation)`.  Both `Multiplicative (ZMod n)` and
`Multiplicative (ZMod 2)` are abelian, hence solvable, so `solvable_of_ker_le_range`
gives `IsSolvable (DihedralGroup n)`.  (Mathlib has no prior solvability result for
`DihedralGroup`.)

## What is proved (fully verified: 0 axioms, 0 sorries)

* `DihedralGroup.parity` / `DihedralGroup.rotation` — the index-2 parity hom and the
  rotation inclusion, with `parity_ker_eq_rotation_range`.
* `DihedralGroup.isSolvable` — `IsSolvable (DihedralGroup n)` for all `n`.
* `S5_not_isSolvable_but_dihedral_is` — the contrast packaged: `Sym (Fin 5)` is *not*
  solvable while every `DihedralGroup n` is.

The `GLₙ(𝔽ₚ)` non-solvability half of the open question is genuinely harder (it needs the
simplicity of `PSL₂`) and is left open.
-/

open DihedralGroup

namespace AbelRuffiniOQ04OQ02OQ04

variable {n : ℕ}

/-- The **parity homomorphism** `Dₙ → ℤ/2`: every rotation `r i` maps to `0` and every
reflection `sr i` maps to `1`.  Its kernel is exactly the rotation subgroup. -/
def parity : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun x := match x with
    | r _ => (1 : Multiplicative (ZMod 2))
    | sr _ => Multiplicative.ofAdd 1
  map_one' := by rw [one_def]
  map_mul' x y := by
    cases x <;> cases y <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;>
      · rfl

/-- The **rotation inclusion** `ℤ/n → Dₙ`, `i ↦ r i`, a homomorphism since `r i · r j =
r (i+j)`.  Its range is the rotation (cyclic) subgroup of `Dₙ`. -/
def rotation : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun i := r (Multiplicative.toAdd i)
  map_one' := by rw [one_def]; rfl
  map_mul' i j := (r_mul_r _ _).symm

@[simp] theorem parity_r (i : ZMod n) : parity (r i) = 1 := rfl

@[simp] theorem parity_sr (i : ZMod n) :
    parity (sr i) = Multiplicative.ofAdd 1 := rfl

@[simp] theorem rotation_apply (i : Multiplicative (ZMod n)) :
    rotation i = r (Multiplicative.toAdd i) := rfl

/-- The kernel of the parity hom equals the range of the rotation inclusion: both are the
rotation subgroup `{ r i : i }`.  This is the index-2 normal abelian subgroup witnessing
that `Dₙ` is metabelian. -/
theorem parity_ker_eq_rotation_range :
    (parity (n := n)).ker = (rotation (n := n)).range := by
  ext x
  cases x with
  | r i =>
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, rotation_apply]
    exact ⟨fun _ => ⟨Multiplicative.ofAdd i, by simp⟩, fun _ => rfl⟩
  | sr i =>
    simp only [MonoidHom.mem_ker, parity_sr, MonoidHom.mem_range, rotation_apply]
    constructor
    · intro h
      -- `ofAdd 1 = 1` in `Multiplicative (ZMod 2)` would force `(1 : ZMod 2) = 0`.
      rw [ofAdd_eq_one] at h
      exact absurd h (by decide)
    · rintro ⟨j, hj⟩
      exact absurd hj (by simp)

/-- **Dihedral groups are solvable.**  For every `n`, `DihedralGroup n` is solvable — it
is metabelian, an abelian (cyclic) normal subgroup with abelian quotient.  Contrast with
`Sym (Fin n)`, which is non-solvable for `n ≥ 5`. -/
instance isSolvable : IsSolvable (DihedralGroup n) :=
  solvable_of_ker_le_range rotation parity (parity_ker_eq_rotation_range.le)

/-- The open question's contrast, packaged: the symmetric group `S₅` is **not** solvable,
yet **every** dihedral group is.  Abel–Ruffini's obstruction is special to `Sₙ`. -/
theorem S5_not_isSolvable_but_dihedral_is :
    ¬ IsSolvable (Equiv.Perm (Fin 5)) ∧ ∀ m : ℕ, IsSolvable (DihedralGroup m) :=
  ⟨Equiv.Perm.fin_5_not_solvable, fun _ => isSolvable⟩

end AbelRuffiniOQ04OQ02OQ04
