import Mathlib

/-
# Burnside Counting, OQ-04 → OQ-02: the general-`n` dihedral bracelet machinery

## What this file provides

The sibling entry `burnside-counting-oq-04-oq-01` (`BurnsideCountingOQ04OQ01.lean`) builds the
concrete dihedral action of `D₄` on the `16` binary colourings of the `4`-cycle and reads off
the unconditional bracelet count `|bracelets(4,2)| = 6`.  Its construction is, however,
hard-wired to `n = 4`: the permutation representation, the `MulAction`, the decidability
instances, and the Burnside step are all stated for `DihedralGroup 4`.

This file **generalises that machinery to every `n`**.  For arbitrary `n` (with `NeZero n`) we
build

* the faithful permutation representation `ρ : DihedralGroup n →* Equiv.Perm (ZMod n)`,
  `r i ↦ (x ↦ x + i)`, `sr i ↦ (x ↦ -i - x)`;
* the induced left `MulAction` of `DihedralGroup n` on `Coloring n = ZMod n → Fin 2`;
* the decidability / `Fintype` infrastructure that makes the orbit count (the *bracelet number*
  `b(n)`) a well-defined natural number;

and we prove, **for every `n`**, the Burnside bracelet identity

      ∑_{g ∈ Dₙ} |Fix(g)|  =  b(n) · (2n)            (`bracelet_burnside`)

(`2n = |Dₙ|`).  This is the orbit-counting engine behind the closed form
`b(n) = (necklaces(n) + reflection-total(n)) / (2n)`: each fixed-point total
`∑_{rotations} |Fix|` and `∑_{reflections} |Fix|` is one half of the right-hand sum.

As concrete corollaries we discharge the general identity at several lengths by *kernel*
`decide` on the fixed-point sum (no `native_decide`, so no `Lean.ofReduceBool`):

      b(3) = 4,   b(5) = 8                          (OEIS A000029)

matching the binary-bracelet sequence `2, 3, 4, 6, 8, 13, …`.  The sibling already records
`b(4) = 6`; these add the next available lengths from the *general* construction rather than a
length-specific one.

## Honesty / scope

The genuinely new content here is the **uniform-in-`n`** construction and Burnside identity
(the sibling only had `n = 4`).  Burnside's lemma itself is Mathlib's
(`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`); `|Dₙ| = 2n` is
`DihedralGroup.card`.  The fully *closed* form — evaluating `∑_{rotations} |Fix(r i)|` as the
gcd-cycle sum `∑_i 2^{gcd(n,i)}` and `∑_{reflections} |Fix(sr i)|` by the parity of `n` — is
left as documented follow-up; this file supplies the structural identity those evaluations plug
into.  `#print axioms` on the headlines confirms only `propext, Classical.choice, Quot.sound`.
-/

namespace BurnsideCountingOQ04OQ02

open Finset MulAction

variable (n : ℕ)

/-! ## Part I: positions, colourings, and the dihedral permutation representation -/

/-- The `n` vertices of the regular `n`-gon, as `ZMod n` so that rotation is `+ i`. -/
abbrev Pos : Type := ZMod n

/-- A binary colouring of the `n` vertices. There are `2^n` of them. -/
abbrev Coloring : Type := Pos n → Fin 2

variable {n}

/-- The faithful permutation representation of `DihedralGroup n` on the `n` vertices:
rotations `r i` act by `x ↦ x + i`, reflections `sr i` act by `x ↦ -i - x`. The reflection
form `-i - x` (rather than `i - x`) is what makes the assignment a *homomorphism* for Mathlib's
dihedral multiplication convention `sr i * sr j = r (j - i)`. -/
def posPerm : DihedralGroup n → Equiv.Perm (Pos n)
  | .r i => Equiv.addRight i
  | .sr i => Equiv.subLeft (-i)

@[simp] theorem posPerm_r (i : ZMod n) : posPerm (.r i) = Equiv.addRight i := rfl
@[simp] theorem posPerm_sr (i : ZMod n) : posPerm (.sr i) = Equiv.subLeft (-i) := rfl

/-- `posPerm` sends the identity to the identity permutation. -/
theorem posPerm_one : posPerm (1 : DihedralGroup n) = 1 := by
  ext x
  show (Equiv.addRight (0 : ZMod n)) x = x
  simp

/-- **`posPerm` is multiplicative.** Checked case-by-case against Mathlib's dihedral
multiplication table; every case reduces to a `ZMod n` arithmetic identity after `ext`. -/
theorem posPerm_mul (g h : DihedralGroup n) :
    posPerm (g * h) = posPerm g * posPerm h := by
  cases g with
  | r i =>
    cases h with
    | r j => ext x; simp [DihedralGroup.r_mul_r, add_comm, add_left_comm]
    | sr j => ext x; simp [DihedralGroup.r_mul_sr]; ring
  | sr i =>
    cases h with
    | r j => ext x; simp [DihedralGroup.sr_mul_r]; ring
    | sr j => ext x; simp [DihedralGroup.sr_mul_sr]; ring

/-- The bundled homomorphism `ρ : DihedralGroup n →* Equiv.Perm (ZMod n)`. -/
def ρ : DihedralGroup n →* Equiv.Perm (Pos n) where
  toFun := posPerm
  map_one' := posPerm_one
  map_mul' := posPerm_mul

/-! ## Part II: the induced action on colourings -/

/-- The dihedral action on colourings: a symmetry `g` relabels positions by `ρ g`, sending the
colouring `c` to `p ↦ c ((ρ g)⁻¹ p)`.  This is a genuine left `MulAction` because `ρ` is a
homomorphism. -/
instance : MulAction (DihedralGroup n) (Coloring n) where
  smul g c := fun p => c ((ρ g).symm p)
  one_smul c := by
    funext p; show c ((ρ 1).symm p) = c p; rw [ρ.map_one]; rfl
  mul_smul g h c := by
    funext p
    show c ((ρ (g * h)).symm p) = c ((ρ h).symm ((ρ g).symm p))
    rw [ρ.map_mul]
    rfl

/-- Unfold the action pointwise (handy for the fixed-point computations). -/
theorem smul_apply (g : DihedralGroup n) (c : Coloring n) (p : Pos n) :
    (g • c) p = c ((ρ g).symm p) := rfl

/-! ## Part III: Fintype instances for Burnside's lemma -/

variable [NeZero n]

instance decFixed (g : DihedralGroup n) :
    DecidablePred (fun c : Coloring n => g • c = c) := fun c => decEq (g • c) c

instance fintypeFixedBy (g : DihedralGroup n) : Fintype (fixedBy (Coloring n) g) :=
  Subtype.fintype _

/-- The orbit relation of the dihedral action is decidable: two colourings lie in the same
orbit iff `∃ g, g • b = a`, decidable because `DihedralGroup n` is a `Fintype` and colourings
have decidable equality. -/
instance : DecidableRel (orbitRel (DihedralGroup n) (Coloring n)).r := fun a b =>
  decidable_of_iff (∃ g : DihedralGroup n, g • b = a) MulAction.mem_orbit_iff.symm

/-- The quotient of colourings by the dihedral action is a `Fintype`, so its cardinality — the
bracelet count `b(n)` — is well-defined. -/
noncomputable instance : Fintype (orbitRel.Quotient (DihedralGroup n) (Coloring n)) := by
  letI s : Setoid (Coloring n) := orbitRel (DihedralGroup n) (Coloring n)
  haveI : DecidableRel (α := Coloring n) (· ≈ ·) := fun a b =>
    decidable_of_iff (∃ g : DihedralGroup n, g • b = a) MulAction.mem_orbit_iff.symm
  exact Quotient.fintype _

variable (n) in
/-- The **bracelet number** `b(n)`: the number of binary colourings of the `n`-cycle up to the
full dihedral symmetry group (rotations and reflections). -/
noncomputable def braceletCard : ℕ :=
  Fintype.card (orbitRel.Quotient (DihedralGroup n) (Coloring n))

/-! ## Part IV: the general Burnside bracelet identity -/

variable (n) in
/-- **The general-`n` Burnside bracelet identity.**  For every `n`,

      ∑_{g ∈ Dₙ} |Fix(g)|  =  b(n) · (2n).

This is Burnside's lemma `sum_card_fixedBy_eq_card_orbits_mul_card_group` for the dihedral
action built above, with `|Dₙ| = 2n` substituted via `DihedralGroup.card`.  It is the orbit-
counting engine for the closed form `b(n) = (necklaces(n) + reflection-total(n))/(2n)`: the
rotation part of the left sum is `necklaces(n)·n`-worth of fixed points and the reflection part
is `reflection-total(n)`. -/
theorem bracelet_burnside :
    ∑ g : DihedralGroup n, Fintype.card (fixedBy (Coloring n) g) = braceletCard n * (2 * n) := by
  have hburnside :
      ∑ g : DihedralGroup n, Fintype.card (fixedBy (Coloring n) g)
        = Fintype.card (orbitRel.Quotient (DihedralGroup n) (Coloring n))
            * Fintype.card (DihedralGroup n) :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (Coloring n)
  rw [hburnside, DihedralGroup.card, braceletCard]

/-! ## Part V: concrete bracelet counts from the general machinery

We feed small `n` into the *general* identity.  The single computation in each case is the
fixed-point sum, discharged by *kernel* `decide`; Burnside then pins down `b(n)`. -/

/-- The Burnside fixed-point sum at `n = 3` is `24` (`8 + 2 + 2` rotations, `4·3` reflections),
by kernel `decide`. -/
theorem fixed_point_sum_three :
    ∑ g : DihedralGroup 3, Fintype.card (fixedBy (Coloring 3) g) = 24 := by decide

/-- **There are exactly `4` binary bracelets of length `3`**, from the general construction. -/
theorem bracelet_three : braceletCard 3 = 4 := by
  have h := bracelet_burnside 3
  rw [fixed_point_sum_three] at h
  omega

/-- The Burnside fixed-point sum at `n = 5` is `80`, by kernel `decide`. -/
theorem fixed_point_sum_five :
    ∑ g : DihedralGroup 5, Fintype.card (fixedBy (Coloring 5) g) = 80 := by decide

/-- **There are exactly `8` binary bracelets of length `5`**, from the general construction. -/
theorem bracelet_five : braceletCard 5 = 8 := by
  have h := bracelet_burnside 5
  rw [fixed_point_sum_five] at h
  omega

/-- The Burnside fixed-point sum at `n = 6` is `156` (rotations `64+2+4+8+4+2 = 84`,
reflections `16·3 + 8·3 = 72`), by kernel `decide`.  This is the largest length at which the
kernel computation stays comfortably feasible. -/
theorem fixed_point_sum_six :
    ∑ g : DihedralGroup 6, Fintype.card (fixedBy (Coloring 6) g) = 156 := by decide

/-- **There are exactly `13` binary bracelets of length `6`**, from the general construction. -/
theorem bracelet_six : braceletCard 6 = 13 := by
  have h := bracelet_burnside 6
  rw [fixed_point_sum_six] at h
  omega

end BurnsideCountingOQ04OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ02.bracelet_burnside
#print axioms BurnsideCountingOQ04OQ02.bracelet_three
#print axioms BurnsideCountingOQ04OQ02.bracelet_five
#print axioms BurnsideCountingOQ04OQ02.bracelet_six
