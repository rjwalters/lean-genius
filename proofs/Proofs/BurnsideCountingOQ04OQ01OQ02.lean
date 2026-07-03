import Mathlib
import Proofs.BurnsideCountingOQ04OQ01OQ01
import Proofs.BurnsideCountingOQ04OQ01OQ01OQ01

/-!
# Burnside Counting OQ-04-OQ-01-OQ-02: a closed form for the binary bracelet numbers

## What this proves

The grandparent chain reduced dihedral *bracelet* counting to a Burnside sum over
`DihedralGroup n` acting on the binary colourings `Coloring n = ZMod n → Fin 2`
(`BurnsideCountingOQ04OQ01OQ01.lean`, namespace `BurnsideBracelets`), and the sibling file
`BurnsideCountingOQ04OQ01OQ01OQ01.lean` proved the *rotation* half of the per-element
fixed-point count in closed form: a rotation by `i` fixes exactly `2 ^ gcd(n, i.val)`
colourings.  Both files still computed the *bracelet numbers themselves* — `b(4) = 6`,
`b(5) = 8`, `b(6) = 13` — by evaluating the Burnside sum with kernel `decide`, one length at a
time, and neither wrote down the classical **closed form** for `b(n)`.

This file writes that closed form down and validates it.  Burnside's lemma over
`D_n = DihedralGroup n` (`|D_n| = 2n`) gives

      `b(n) = (1 / 2n) · [ (rotation fixed-point total) + (reflection fixed-point total) ]`.

Using the sibling's rotation closed form `2 ^ gcd(n, i.val)` and the classical reflection
counts (odd `n`: every reflection fixes `2 ^ ((n+1)/2)`; even `n`: the `n/2` vertex-axis
reflections fix `2 ^ (n/2 + 1)` each and the `n/2` edge-axis reflections fix `2 ^ (n/2)`
each) this becomes the fully explicit

      `rotTerm n  = ∑_{i : ZMod n} 2 ^ gcd(n, i.val)`
      `reflTerm n = if n odd  then n · 2 ^ ((n+1)/2)`
      `            else (n/2) · 2 ^ (n/2 + 1) + (n/2) · 2 ^ (n/2)`
      `braceletClosed n = (rotTerm n + reflTerm n) / (2n)`.

We prove:

* `rotTerm_eq` — the rotation term **is** the sum of the true rotation fixed-point counts
  `∑_i |Fix(r i)|`, uniformly in `n`, straight from the sibling's `card_rotFixed`
  (no computation).
* `braceletClosed_eq_orbitCount_{three,four,five,six}` — the closed form agrees with the
  genuine dihedral orbit count `|Coloring n / D_n|` for `n = 3, 4, 5, 6`, the last three of
  which are the grandparents' unconditionally-proved values and the first (`b(3) = 4`) a fresh
  Burnside computation added here.  These pin the formula to ground truth, not to an OEIS
  lookup.
* `bracelet_seven … bracelet_ten` — the closed form then *predicts* the next bracelet numbers
  `b(7)=18, b(8)=30, b(9)=46, b(10)=78` by pure arithmetic on the formula, **without** building
  or enumerating the (rapidly growing) orbit quotients — the values are `A000029(7..10)` of the
  OEIS "binary bracelets" sequence, beyond the length-`6` ceiling the parents reached by
  `decide` on the quotient.

## Honesty / Scope

The *rotation* half of the formula is tied to the real fixed-point counts by a general,
computation-free theorem (`rotTerm_eq`).  The *reflection* half is used here in its classical
closed form and validated against the true orbit counts for every `n ≤ 6` (both reflection
parities, vertex- and edge-axis, occur); a fully generic Lean proof of the per-reflection count
`2 ^ (orbits of the reflection involution)` — the exact analogue of the sibling's rotation
theorem — is the natural next open question and is *not* proved here.  So this is an explicit,
ground-truth-anchored closed form plus its onward predictions, not a from-`n` derivation of the
reflection term.  Everything below is axiom-free: no `native_decide`, only kernel `decide` on
closed `ℕ`/finite data.  `#print axioms` on the headlines reports only `propext`,
`Classical.choice`, `Quot.sound`.
-/

namespace BurnsideBraceletClosedForm

open Finset MulAction

/-! ## Part I: the closed-form formula -/

/-- Rotation contribution to the Burnside sum: `∑_{i : ZMod n} 2 ^ gcd(n, i.val)`.  By the
sibling's `card_rotFixed` this is exactly `∑_i |Fix(r i)|` (see `rotTerm_eq`), i.e. `n` times
the classical binary *necklace* count `(1/n) ∑_{d ∣ n} φ(d) 2^{n/d}`. -/
def rotTerm (n : ℕ) [NeZero n] : ℕ := ∑ i : ZMod n, 2 ^ Nat.gcd n i.val

/-- Reflection contribution to the Burnside sum.  For odd `n` all `n` reflections pass through
one vertex and the opposite edge-midpoint and each fixes `2 ^ ((n+1)/2)` colourings.  For even
`n` the `n/2` vertex-axis reflections fix `2 ^ (n/2 + 1)` each and the `n/2` edge-axis
reflections fix `2 ^ (n/2)` each. -/
def reflTerm (n : ℕ) : ℕ :=
  if n % 2 = 1 then n * 2 ^ ((n + 1) / 2)
  else (n / 2) * 2 ^ (n / 2 + 1) + (n / 2) * 2 ^ (n / 2)

/-- **The closed form for the number of binary bracelets of length `n`.**
`b(n) = (rotTerm n + reflTerm n) / (2n)`, the Burnside average of the fixed-point counts over
the `2n` symmetries of `DihedralGroup n`. -/
def braceletClosed (n : ℕ) [NeZero n] : ℕ := (rotTerm n + reflTerm n) / (2 * n)

/-! ## Part II: the rotation term is the true rotation fixed-point total -/

/-- **The rotation term is genuine.**  `rotTerm n` equals the sum over all rotations of the
true number of colourings each fixes — uniformly in `n`, with no computation — because the
sibling file proved `|Fix(r i)| = 2 ^ gcd(n, i.val)`. -/
theorem rotTerm_eq (n : ℕ) [NeZero n] :
    rotTerm n = ∑ i : ZMod n, Fintype.card (BurnsideRotationFix.RotFixed n i) := by
  simp only [rotTerm, BurnsideRotationFix.card_rotFixed]

/-! ## Part III: ground-truth Burnside orbit counts for `n = 3` and `n = 4`

`b(5)` and `b(6)` are imported from the grandparent (`BurnsideBracelets.bracelet_five`,
`bracelet_six`); here we add `b(3)` and `b(4)` with the same generic action. -/

open BurnsideBracelets in
/-- Burnside fixed-point sum for the triangle (`D₃`, `6` symmetries × `8` colourings):
identity fixes `8`, the two nontrivial rotations fix `2` each, the three reflections fix
`2^2 = 4` each; `8 + 2·2 + 3·4 = 24`. -/
theorem fixed_sum_three :
    ∑ g : DihedralGroup 3, Fintype.card (fixedBy (Coloring 3) g) = 24 := by decide

/-- **There are exactly `4` binary bracelets of length `3`** (`A000029(3) = 4`): Burnside turns
the fixed-point sum `24` and `|D₃| = 6` into `24 / 6 = 4`. -/
theorem bracelet_three :
    Fintype.card (orbitRel.Quotient (DihedralGroup 3) (BurnsideBracelets.Coloring 3)) = 4 := by
  have h := BurnsideBracelets.bracelet_count_mul 24 fixed_sum_three
  omega

open BurnsideBracelets in
/-- Burnside fixed-point sum for the square (`D₄`, `8` symmetries × `16` colourings):
rotations contribute `16 + 2 + 4 + 2 = 24`, the two vertex-axis reflections fix `2^3 = 8` each
and the two edge-axis reflections fix `2^2 = 4` each; `24 + 2·8 + 2·4 = 48`. -/
theorem fixed_sum_four :
    ∑ g : DihedralGroup 4, Fintype.card (fixedBy (Coloring 4) g) = 48 := by decide

/-- **There are exactly `6` binary bracelets of length `4`** (`A000029(4) = 6`): Burnside turns
the fixed-point sum `48` and `|D₄| = 8` into `48 / 8 = 6`. -/
theorem bracelet_four :
    Fintype.card (orbitRel.Quotient (DihedralGroup 4) (BurnsideBracelets.Coloring 4)) = 6 := by
  have h := BurnsideBracelets.bracelet_count_mul 48 fixed_sum_four
  omega

/-! ## Part IV: the closed form matches the ground-truth orbit counts, `n = 3,…,6` -/

/-- The closed form evaluates to `4` at `n = 3`. -/
theorem braceletClosed_three : braceletClosed 3 = 4 := by decide
/-- The closed form evaluates to `6` at `n = 4`. -/
theorem braceletClosed_four : braceletClosed 4 = 6 := by decide
/-- The closed form evaluates to `8` at `n = 5`. -/
theorem braceletClosed_five : braceletClosed 5 = 8 := by decide
/-- The closed form evaluates to `13` at `n = 6`. -/
theorem braceletClosed_six : braceletClosed 6 = 13 := by decide

/-- The closed form reproduces the true number of dihedral orbits at `n = 3`. -/
theorem braceletClosed_eq_orbitCount_three :
    braceletClosed 3 =
      Fintype.card (orbitRel.Quotient (DihedralGroup 3) (BurnsideBracelets.Coloring 3)) := by
  rw [braceletClosed_three, bracelet_three]

/-- The closed form reproduces the true number of dihedral orbits at `n = 4`. -/
theorem braceletClosed_eq_orbitCount_four :
    braceletClosed 4 =
      Fintype.card (orbitRel.Quotient (DihedralGroup 4) (BurnsideBracelets.Coloring 4)) := by
  rw [braceletClosed_four, bracelet_four]

/-- The closed form reproduces the true number of dihedral orbits at `n = 5`
(grandparent's `bracelet_five`). -/
theorem braceletClosed_eq_orbitCount_five :
    braceletClosed 5 =
      Fintype.card (orbitRel.Quotient (DihedralGroup 5) (BurnsideBracelets.Coloring 5)) := by
  rw [braceletClosed_five, BurnsideBracelets.bracelet_five]

/-- The closed form reproduces the true number of dihedral orbits at `n = 6`
(grandparent's `bracelet_six`). -/
theorem braceletClosed_eq_orbitCount_six :
    braceletClosed 6 =
      Fintype.card (orbitRel.Quotient (DihedralGroup 6) (BurnsideBracelets.Coloring 6)) := by
  rw [braceletClosed_six, BurnsideBracelets.bracelet_six]

/-! ## Part V: onward predictions beyond the parents' computational ceiling

The closed form now yields the next binary bracelet numbers by pure arithmetic — no orbit
quotient is built or enumerated.  These are `A000029(7..10)`. -/

/-- `b(7) = 18` from the closed form (odd length; `rotTerm = 128 + 6·2 = 140`,
`reflTerm = 7·2^4 = 112`, `(140+112)/14 = 18`). -/
theorem bracelet_seven : braceletClosed 7 = 18 := by decide
/-- `b(8) = 30` from the closed form (even length; `rotTerm = 288`,
`reflTerm = 4·2^5 + 4·2^4 = 192`, `(288+192)/16 = 30`). -/
theorem bracelet_eight : braceletClosed 8 = 30 := by decide
/-- `b(9) = 46` from the closed form. -/
theorem bracelet_nine : braceletClosed 9 = 46 := by decide
/-- `b(10) = 78` from the closed form. -/
theorem bracelet_ten : braceletClosed 10 = 78 := by decide

end BurnsideBraceletClosedForm

-- Axiom audit: only the standard foundational axioms, in particular no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideBraceletClosedForm.braceletClosed_eq_orbitCount_six
#print axioms BurnsideBraceletClosedForm.bracelet_ten
#print axioms BurnsideBraceletClosedForm.rotTerm_eq
