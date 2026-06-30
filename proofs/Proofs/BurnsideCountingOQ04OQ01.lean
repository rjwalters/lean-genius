import Mathlib

/-
# Burnside Counting, OQ-04 → OQ-01: Unconditional `|bracelets(4,2)| = 6`

## What This Proves

The parent entry `burnside-counting-oq-04` (`BurnsideCountingOQ04.lean`) proves the abstract
index-2 orbit-folding identity and, as a numeric corollary, recovers the binary length-4
bracelet count `6` — but only *conditionally*: its `binary_four_bracelet_count` takes the
necklace count (`6`) and the reflection fixed-point total (`24`) as **hypotheses**, because
recomputing those finite counts from scratch would require a concrete dihedral action, which
the parent does not build. The parent's open question OQ-01 asks precisely for this:

  > "Build a concrete dihedral action on `Coloring n k` and discharge the necklace and
  >  reflection-total hypotheses of `binary_four_bracelet_count` by kernel computation,
  >  yielding an *unconditional* `|bracelets| = 6` (the parent closes the analogous cyclic
  >  count only with `native_decide`)."

This file answers it. We build the genuine dihedral action of `D₄ = DihedralGroup 4` on the
`16` binary colourings of the 4-cycle, `Coloring = ZMod 4 → Fin 2`, and prove

      `Fintype.card (orbitRel.Quotient (DihedralGroup 4) Coloring) = 6`

with **no hypotheses, no axioms, and no `native_decide`** — the fixed-point counts are
discharged by *kernel* `decide`.

## How

The action is the faithful permutation representation of `D₄` on the four vertices,
  `r i  ↦  (x ↦ x + i)`        (rotation by `i`),
  `sr i ↦  (x ↦ -i - x)`       (reflection),
lifted to colourings by `(g • c) p = c ((ρ g)⁻¹ p)`.  That `ρ : D₄ → Perm (ZMod 4)` is a
homomorphism is checked against Mathlib's dihedral multiplication table (`r_mul_r`,
`r_mul_sr`, `sr_mul_r`, `sr_mul_sr`), so the `MulAction` laws hold on the nose.

With the action in hand, Burnside's lemma
(`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) gives

      `∑_{g ∈ D₄} |Fix(g)|  =  |Coloring / D₄| · |D₄|`.

We evaluate the left-hand sum to `48` by kernel `decide` (this is the only computation, and
it is light: `8` group elements × `16` colourings) and `|D₄| = 8`
(`DihedralGroup.card`), so `|bracelets| · 8 = 48`, i.e. `|bracelets| = 6`.  No reflection
total or necklace count is assumed; both are subsumed by the single fixed-point sum.

## Honesty / Scope

The contribution is the *unconditional* and *axiom-free* (kernel-`decide`, not
`native_decide`) bracelet count, together with the concrete dihedral action that the parent
OQ-04 leaves unbuilt.  Burnside's lemma itself is Mathlib's; the folding identity is the
parent's.  `#print axioms` on the headline confirms only `propext`, `Classical.choice`,
`Quot.sound` (no `Lean.ofReduceBool`, no `sorryAx`).
-/

namespace BurnsideCountingOQ04OQ01

open Finset MulAction

/-! ## Part I: positions, colourings, and the dihedral permutation representation -/

/-- The four vertices of the square, as `ZMod 4` so that rotation is `+ i`. -/
abbrev Pos : Type := ZMod 4

/-- A binary colouring of the four vertices. There are `2^4 = 16` of them. -/
abbrev Coloring : Type := Pos → Fin 2

/-- The faithful permutation representation of `DihedralGroup 4` on the four vertices:
rotations `r i` act by `x ↦ x + i`, reflections `sr i` act by `x ↦ -i - x`. The reflection
form `-i - x` (rather than `i - x`) is what makes the assignment a *homomorphism* for
Mathlib's dihedral multiplication convention `sr i * sr j = r (j - i)`. -/
def posPerm : DihedralGroup 4 → Equiv.Perm Pos
  | .r i => Equiv.addRight i
  | .sr i => Equiv.subLeft (-i)

@[simp] theorem posPerm_r (i : ZMod 4) : posPerm (.r i) = Equiv.addRight i := rfl
@[simp] theorem posPerm_sr (i : ZMod 4) : posPerm (.sr i) = Equiv.subLeft (-i) := rfl

/-- `posPerm` sends the identity to the identity permutation. -/
theorem posPerm_one : posPerm 1 = 1 := by
  ext x
  show (Equiv.addRight (0 : ZMod 4)) x = x
  simp

/-- **`posPerm` is multiplicative.** Checked case-by-case against Mathlib's dihedral
multiplication table; every case reduces to a `ZMod 4` arithmetic identity after `ext`. -/
theorem posPerm_mul (g h : DihedralGroup 4) :
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

/-- The bundled homomorphism `ρ : DihedralGroup 4 →* Equiv.Perm (ZMod 4)`. -/
def ρ : DihedralGroup 4 →* Equiv.Perm Pos where
  toFun := posPerm
  map_one' := posPerm_one
  map_mul' := posPerm_mul

/-! ## Part II: the induced action on colourings -/

/-- The dihedral action on colourings: a symmetry `g` relabels positions by `ρ g`, sending the
colouring `c` to `p ↦ c ((ρ g)⁻¹ p)`.  This is a genuine left `MulAction` because `ρ` is a
homomorphism. -/
instance : MulAction (DihedralGroup 4) Coloring where
  smul g c := fun p => c ((ρ g).symm p)
  one_smul c := by
    funext p; show c ((ρ 1).symm p) = c p; rw [ρ.map_one]; rfl
  mul_smul g h c := by
    funext p
    show c ((ρ (g * h)).symm p) = c ((ρ h).symm ((ρ g).symm p))
    rw [ρ.map_mul]
    rfl

/-- Unfold the action pointwise (handy for the fixed-point computations). -/
theorem smul_apply (g : DihedralGroup 4) (c : Coloring) (p : Pos) :
    (g • c) p = c ((ρ g).symm p) := rfl

/-! ## Part III: Fintype instances for Burnside's lemma -/

instance decFixed (g : DihedralGroup 4) :
    DecidablePred (fun c : Coloring => g • c = c) := fun c => decEq (g • c) c

instance fintypeFixedBy (g : DihedralGroup 4) : Fintype (fixedBy Coloring g) :=
  Subtype.fintype _

/-- The orbit relation of the dihedral action is decidable: two colourings lie in the same
orbit iff `∃ g, g • b = a`, decidable because `DihedralGroup 4` is a `Fintype` and colourings
have decidable equality. -/
instance : DecidableRel (orbitRel (DihedralGroup 4) Coloring).r := fun a b =>
  decidable_of_iff (∃ g : DihedralGroup 4, g • b = a) MulAction.mem_orbit_iff.symm

/-- The quotient of colourings by the dihedral action is a `Fintype` (finite carrier plus the
decidable orbit relation), so its cardinality — the bracelet count — is well-defined. -/
noncomputable instance : Fintype (orbitRel.Quotient (DihedralGroup 4) Coloring) := by
  letI s : Setoid Coloring := orbitRel (DihedralGroup 4) Coloring
  haveI : DecidableRel (α := Coloring) (· ≈ ·) := fun a b =>
    decidable_of_iff (∃ g : DihedralGroup 4, g • b = a) MulAction.mem_orbit_iff.symm
  exact Quotient.fintype _

/-! ## Part IV: the unconditional bracelet count -/

/-- **The Burnside fixed-point sum equals `48`**, by *kernel* `decide`.

This is the heart of the unconditional count: it tallies, over all eight dihedral symmetries
of the square, how many of the `16` binary colourings each one fixes
(`16 + 2 + 4 + 2` for the rotations, `8 + 8 + 4 + 4` for the reflections).  Unlike the
parent's analogous cyclic computation, this is discharged by kernel reduction
(`decide`), not `native_decide`, so it carries no `Lean.ofReduceBool` axiom. -/
theorem fixed_point_sum :
    ∑ g : DihedralGroup 4, Fintype.card (fixedBy Coloring g) = 48 := by
  decide

/-- **There are exactly `6` binary bracelets of length `4`** — unconditionally.

Burnside's lemma turns the fixed-point sum (`48`) and the group order (`|D₄| = 8`) into the
orbit count: `|bracelets| · 8 = 48`, hence `|bracelets| = 6`.  No necklace count or reflection
total is assumed (contrast the parent's `binary_four_bracelet_count`, which takes both as
hypotheses); both are absorbed into the single kernel-`decide`d sum above. -/
theorem binary_four_bracelet_unconditional :
    Fintype.card (orbitRel.Quotient (DihedralGroup 4) Coloring) = 6 := by
  have hburnside :
      ∑ g : DihedralGroup 4, Fintype.card (fixedBy Coloring g)
        = Fintype.card (orbitRel.Quotient (DihedralGroup 4) Coloring)
            * Fintype.card (DihedralGroup 4) :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup 4) Coloring
  rw [fixed_point_sum, DihedralGroup.card] at hburnside
  -- `48 = |bracelets| * 8`
  omega

end BurnsideCountingOQ04OQ01

-- Axiom audit: only the standard foundational axioms, in particular no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ01.binary_four_bracelet_unconditional
