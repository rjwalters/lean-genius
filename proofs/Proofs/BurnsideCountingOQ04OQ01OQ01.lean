import Mathlib

/-
# Burnside Counting, OQ-04-OQ-01-OQ-01: unconditional bracelet counts `b(5) = 8`, `b(6) = 13`

## What This Proves

The grandparent `burnside-counting-oq-04` reduced dihedral *bracelet* counting to cyclic
*necklace* counting via the index-2 folding identity, and the parent
`burnside-counting-oq-04-oq-01` (`BurnsideCountingOQ04OQ01.lean`) built a *concrete* dihedral
action on the binary colourings of the `4`-cycle and discharged the length-`4` bracelet count
`6` unconditionally (kernel `decide`, no `native_decide`, no axioms beyond the foundational
three).  Its open question OQ-01 asks for the obvious next instances — the binary bracelet
counts for `n = 5` and `n = 6`, the first two lengths where the dihedral group genuinely
exceeds the cyclic one (odd `5`, even `6` exercise both reflection types).

This file answers it.  Rather than hard-code one length, we build the dihedral action of
`DihedralGroup n` on the colourings `ZMod n → Fin 2` **generically in `n`**, prove it is a
genuine `MulAction` (so Burnside's lemma applies for every `n`), and then read off

      `Fintype.card (orbitRel.Quotient (DihedralGroup 5) (Coloring 5)) = 8`
      `Fintype.card (orbitRel.Quotient (DihedralGroup 6) (Coloring 6)) = 13`

by evaluating the Burnside fixed-point sum with *kernel* `decide`.  These are the values
`A000029(5) = 8` and `A000029(6) = 13` of the OEIS "number of binary bracelets" sequence.

## How

The action is the faithful permutation representation of `D_n` on its `n` vertices,
  `r i  ↦  (x ↦ x + i)`        (rotation by `i`),
  `sr i ↦  (x ↦ -i - x)`       (reflection),
lifted to colourings by `(g • c) p = c ((ρ g)⁻¹ p)`.  That `ρ : D_n → Perm (ZMod n)` is a
homomorphism is checked against Mathlib's dihedral multiplication table (`r_mul_r`,
`r_mul_sr`, `sr_mul_r`, `sr_mul_sr`), giving the `MulAction` laws on the nose — **for all `n`**.

Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) then reads

      `∑_{g ∈ D_n} |Fix(g)|  =  |Coloring / D_n| · |D_n|`,

and `|D_n| = 2n` (`DihedralGroup.card`).  The fixed-point sum is `80` for `n = 5`
(`= 8 · 10`) and `156` for `n = 6` (`= 13 · 12`), each discharged by kernel `decide`
(`10` group elements × `32` colourings; `12` × `64`), so the orbit counts are `8` and `13`.

## Honesty / Scope

The mathematical content is the *generic* concrete dihedral action (the parent built only the
single length-`4` instance) plus the two unconditional, axiom-free (kernel-`decide`, not
`native_decide`) bracelet counts.  Burnside's lemma is Mathlib's; the folding identity is the
grandparent's.  `#print axioms` on each headline confirms only `propext`, `Classical.choice`,
`Quot.sound` (no `Lean.ofReduceBool`, no `sorryAx`).
-/

namespace BurnsideBracelets

open Finset MulAction

/-! ## Part I: the generic dihedral permutation representation -/

/-- A binary colouring of the `n` vertices of the `n`-cycle. There are `2^n` of them. -/
abbrev Coloring (n : ℕ) : Type := ZMod n → Fin 2

/-- The faithful permutation representation of `DihedralGroup n` on the `n` vertices
(`ZMod n`): rotations `r i` act by `x ↦ x + i`, reflections `sr i` act by `x ↦ -i - x`. The
reflection form `-i - x` (rather than `i - x`) is what makes the assignment a *homomorphism*
for Mathlib's dihedral convention `sr i * sr j = r (j - i)`. -/
def posPerm {n : ℕ} : DihedralGroup n → Equiv.Perm (ZMod n)
  | .r i => Equiv.addRight i
  | .sr i => Equiv.subLeft (-i)

@[simp] theorem posPerm_r {n : ℕ} (i : ZMod n) : posPerm (.r i) = Equiv.addRight i := rfl
@[simp] theorem posPerm_sr {n : ℕ} (i : ZMod n) : posPerm (.sr i) = Equiv.subLeft (-i) := rfl

/-- `posPerm` sends the identity to the identity permutation. -/
theorem posPerm_one {n : ℕ} : posPerm (1 : DihedralGroup n) = 1 := by
  ext x
  show (Equiv.addRight (0 : ZMod n)) x = x
  simp

/-- **`posPerm` is multiplicative.** Checked case-by-case against Mathlib's dihedral
multiplication table; every case reduces to a `ZMod n` arithmetic identity after `ext`. -/
theorem posPerm_mul {n : ℕ} (g h : DihedralGroup n) :
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
def ρ {n : ℕ} : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun := posPerm
  map_one' := posPerm_one
  map_mul' := posPerm_mul

/-! ## Part II: the induced action on colourings -/

/-- The dihedral action on colourings: a symmetry `g` relabels positions by `ρ g`, sending the
colouring `c` to `p ↦ c ((ρ g)⁻¹ p)`.  This is a genuine left `MulAction` because `ρ` is a
homomorphism — and it is defined uniformly in `n`. -/
instance instMulAction {n : ℕ} : MulAction (DihedralGroup n) (Coloring n) where
  smul g c := fun p => c ((ρ g).symm p)
  one_smul c := by
    funext p; show c ((ρ (1 : DihedralGroup n)).symm p) = c p; rw [ρ.map_one]; rfl
  mul_smul g h c := by
    funext p
    show c ((ρ (g * h)).symm p) = c ((ρ h).symm ((ρ g).symm p))
    rw [ρ.map_mul]; rfl

/-- Unfold the action pointwise (handy for the fixed-point computations). -/
theorem smul_apply {n : ℕ} (g : DihedralGroup n) (c : Coloring n) (p : ZMod n) :
    (g • c) p = c ((ρ g).symm p) := rfl

/-! ## Part III: Fintype / decidability instances for Burnside's lemma -/

instance decFixed {n : ℕ} [NeZero n] (g : DihedralGroup n) :
    DecidablePred (fun c : Coloring n => g • c = c) := fun c => decEq (g • c) c

instance fintypeFixedBy {n : ℕ} [NeZero n] (g : DihedralGroup n) :
    Fintype (fixedBy (Coloring n) g) := Subtype.fintype _

instance decOrbitRel {n : ℕ} [NeZero n] :
    DecidableRel (orbitRel (DihedralGroup n) (Coloring n)).r := fun a b =>
  decidable_of_iff (∃ g : DihedralGroup n, g • b = a) MulAction.mem_orbit_iff.symm

noncomputable instance fintypeQuot {n : ℕ} [NeZero n] :
    Fintype (orbitRel.Quotient (DihedralGroup n) (Coloring n)) := by
  letI s : Setoid (Coloring n) := orbitRel (DihedralGroup n) (Coloring n)
  haveI : DecidableRel (α := Coloring n) (· ≈ ·) := fun a b =>
    decidable_of_iff (∃ g : DihedralGroup n, g • b = a) MulAction.mem_orbit_iff.symm
  exact Quotient.fintype _

/-! ## Part IV: the generic Burnside reduction -/

/-- **Generic Burnside count.** If the dihedral fixed-point sum equals `S`, then the bracelet
count (number of orbits) satisfies `bracelets · 2n = S`.  Specialising `S` and dividing by
`2n` yields the individual counts below. -/
theorem bracelet_count_mul {n : ℕ} [NeZero n] (S : ℕ)
    (hS : ∑ g : DihedralGroup n, Fintype.card (fixedBy (Coloring n) g) = S) :
    Fintype.card (orbitRel.Quotient (DihedralGroup n) (Coloring n)) * (2 * n) = S := by
  have hb :
      ∑ g : DihedralGroup n, Fintype.card (fixedBy (Coloring n) g)
        = Fintype.card (orbitRel.Quotient (DihedralGroup n) (Coloring n))
            * Fintype.card (DihedralGroup n) :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (Coloring n)
  rw [hS, DihedralGroup.card] at hb
  omega

/-! ## Part V: the two unconditional bracelet counts -/

/-- The Burnside fixed-point sum for `n = 5` is `80`, by *kernel* `decide`
(`10` dihedral symmetries × `32` binary colourings of the pentagon: the identity fixes `32`,
the four non-trivial rotations fix `2` each, the five reflections fix `2^3 = 8` each;
`32 + 4·2 + 5·8 = 80`). -/
theorem fixed_sum_five :
    ∑ g : DihedralGroup 5, Fintype.card (fixedBy (Coloring 5) g) = 80 := by
  decide

/-- **There are exactly `8` binary bracelets of length `5`** — unconditionally
(`A000029(5) = 8`).  Burnside turns the fixed-point sum `80` and `|D₅| = 10` into the orbit
count `80 / 10 = 8`. -/
theorem bracelet_five :
    Fintype.card (orbitRel.Quotient (DihedralGroup 5) (Coloring 5)) = 8 := by
  have h := bracelet_count_mul 80 fixed_sum_five
  omega

/-- The Burnside fixed-point sum for `n = 6` is `156`, by *kernel* `decide`
(`12` dihedral symmetries × `64` binary colourings of the hexagon: rotations contribute
`64 + 2 + 4 + 8 + 4 + 2 = 84`, the three vertex-axis reflections fix `2^4 = 16` each and the
three edge-axis reflections fix `2^3 = 8` each, `84 + 3·16 + 3·8 = 156`). -/
theorem fixed_sum_six :
    ∑ g : DihedralGroup 6, Fintype.card (fixedBy (Coloring 6) g) = 156 := by
  decide

/-- **There are exactly `13` binary bracelets of length `6`** — unconditionally
(`A000029(6) = 13`).  Burnside turns the fixed-point sum `156` and `|D₆| = 12` into the orbit
count `156 / 12 = 13`. -/
theorem bracelet_six :
    Fintype.card (orbitRel.Quotient (DihedralGroup 6) (Coloring 6)) = 13 := by
  have h := bracelet_count_mul 156 fixed_sum_six
  omega

end BurnsideBracelets

-- Axiom audit: only the standard foundational axioms, in particular no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideBracelets.bracelet_five
#print axioms BurnsideBracelets.bracelet_six
