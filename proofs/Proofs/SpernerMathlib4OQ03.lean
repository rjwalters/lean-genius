/-
  Sperner–Mathlib4 OQ-03: The combinatorial fixed-point index (mod 2).

  The parent file `SpernerMathlib4` proves, for an abstract `CellComplex V d`
  with a vertex colouring `c : V → Fin (d+1)`, the

    * **Sperner Parity Theorem** (`sperner_parity`):
        #{panchromatic cells}  ≡  #{boundary doors}   (mod 2),

    * and **Sperner's Lemma** (`sperner`): an odd boundary-door count forces the
      existence of a panchromatic cell.

  The open question OQ-03 asks to combine the parity theorem with a *fixed-point
  index computation* en route to Brouwer's fixed-point theorem.  This file
  isolates and formalises exactly that index computation, i.e. the algebraic
  core of degree/index theory mod 2 that the Sperner→Brouwer argument runs on.

  We package the two counts as an element of `ZMod 2` — the **combinatorial
  fixed-point index** `fpIndex` and the **boundary index** `boundaryIndex` — and
  prove:

    * `fpIndex_eq_boundaryIndex`         fpIndex = boundaryIndex   (the parity
                                          theorem as an identity of indices);
    * `exists_panchromatic_of_boundaryIndex_ne_zero`
                                          index ≠ 0 ⟹ a fixed point exists
                                          (the existence engine of Brouwer);
    * `boundaryIndex_eq_zero_of_no_panchromatic`
                                          no fixed point ⟹ index vanishes
                                          (the "no-retraction" shadow, the
                                          contrapositive Brouwer uses);
    * `even_panchromaticCount_iff_even_boundaryDoorCount`  the full parity
                                          dichotomy;
    * `even_panchromaticCount_of_no_boundary_doors`  a boundaryless complex has
                                          an even fixed-point count (index 0).

  Scope / honesty.  This is the *combinatorial* half of "Brouwer via Sperner":
  the fixed-point index and its existence / vanishing theorems on a discrete
  cell complex.  The remaining *geometric realization* — subdividing the
  standard simplex, deriving the Sperner labelling from a continuous self-map,
  showing the boundary index is `1` by induction on dimension, and passing to a
  fixed point by compactness — is a separate, large development and is NOT done
  here.  Nothing below asserts topological Brouwer; the index layer is a
  verified stepping stone on its critical path.

  All results are 0-axiom, built on the verified parent theorems.
-/
import Proofs.SpernerMathlib4
import Mathlib.Algebra.CharP.Two

open Finset

namespace CellComplex

variable {V : Type*} [DecidableEq V] {d : ℕ}
variable (c : V → Fin (d + 1)) (K : CellComplex V d)

/-- The number of panchromatic (fully coloured) cells. -/
def panchromaticCount : ℕ :=
  (univ.filter (fun s : K.Cell => IsPanchromatic c K s)).card

/-- The number of boundary doors (door facets with no adjacent cell). -/
def boundaryDoorCount : ℕ :=
  (univ.filter
    (fun p : K.Cell × Fin (d + 1) =>
      IsDoor c K p.1 p.2 ∧ K.adj p.1 p.2 = none)).card

/-- **Sperner parity, in `Nat.ModEq` form**: the panchromatic count and the
boundary-door count are congruent mod 2. This is `sperner_parity` repackaged
against the named counts above. -/
theorem panchromaticCount_modEq_boundaryDoorCount :
    panchromaticCount c K ≡ boundaryDoorCount c K [MOD 2] :=
  sperner_parity c K

/-- The **combinatorial fixed-point index** of a coloured cell complex: the
panchromatic cell count taken mod 2, as an element of `ZMod 2`. This is the
mod-2 degree the Sperner→Brouwer argument computes. -/
def fpIndex : ZMod 2 := (panchromaticCount c K : ZMod 2)

/-- The **boundary index**: the boundary-door count taken mod 2. -/
def boundaryIndex : ZMod 2 := (boundaryDoorCount c K : ZMod 2)

/-- **Fixed-point index computation**: the fixed-point index equals the boundary
index. This is the Sperner Parity Theorem stated as an identity of `ZMod 2`
indices — the exact "index computation" OQ-03 asks for. -/
theorem fpIndex_eq_boundaryIndex : fpIndex c K = boundaryIndex c K := by
  unfold fpIndex boundaryIndex
  rw [ZMod.natCast_eq_natCast_iff]
  exact panchromaticCount_modEq_boundaryDoorCount c K

/-- In `ZMod 2`, the cast of a natural number vanishes iff the number is even. -/
private theorem natCast_zmod2_eq_zero_iff (n : ℕ) :
    (n : ZMod 2) = 0 ↔ Even n :=
  ZMod.natCast_eq_zero_iff_even

/-- **Existence engine**: if the boundary index is nonzero, a panchromatic cell
(a combinatorial "fixed point") exists. This is the index-theoretic form of
Sperner's Lemma and the mechanism behind Brouwer's existence conclusion. -/
theorem exists_panchromatic_of_boundaryIndex_ne_zero
    (h : boundaryIndex c K ≠ 0) :
    ∃ s : K.Cell, IsPanchromatic c K s := by
  apply sperner c K
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact h (by
    unfold boundaryIndex
    exact (natCast_zmod2_eq_zero_iff _).mpr heven)

/-- **Vanishing / no-retraction shadow**: if no cell is panchromatic (no
combinatorial fixed point), the boundary index vanishes. This is the
contrapositive that Brouwer's proof exploits: a fixed-point-free labelling
cannot have nonzero boundary index. -/
theorem boundaryIndex_eq_zero_of_no_panchromatic
    (h : ∀ s : K.Cell, ¬ IsPanchromatic c K s) :
    boundaryIndex c K = 0 := by
  rw [← fpIndex_eq_boundaryIndex]
  unfold fpIndex panchromaticCount
  have : (univ.filter (fun s : K.Cell => IsPanchromatic c K s)) = ∅ := by
    rw [filter_eq_empty_iff]
    exact fun s _ => h s
  rw [this, card_empty, Nat.cast_zero]

/-- **Parity dichotomy**: the panchromatic count is even iff the boundary-door
count is even. Both directions follow from the parity theorem. -/
theorem even_panchromaticCount_iff_even_boundaryDoorCount :
    Even (panchromaticCount c K) ↔ Even (boundaryDoorCount c K) := by
  have h : panchromaticCount c K % 2 = boundaryDoorCount c K % 2 :=
    panchromaticCount_modEq_boundaryDoorCount c K
  rw [Nat.even_iff, Nat.even_iff, h]

/-- A **boundaryless** cell complex (no boundary doors) has an even number of
panchromatic cells, i.e. fixed-point index `0`. This is the discrete shadow of
"a self-map of a closed manifold has even mod-2 degree data" for this setup. -/
theorem even_panchromaticCount_of_no_boundary_doors
    (h : boundaryDoorCount c K = 0) :
    Even (panchromaticCount c K) := by
  rw [even_panchromaticCount_iff_even_boundaryDoorCount, h]
  exact ⟨0, rfl⟩

/-- Recovering Sperner's Lemma in index language: an odd boundary index forces a
fixed point. (Here "odd boundary index" means the underlying count is odd.) -/
theorem exists_panchromatic_of_odd_boundaryDoorCount
    (hbdry : Odd (boundaryDoorCount c K)) :
    ∃ s : K.Cell, IsPanchromatic c K s :=
  sperner c K hbdry

end CellComplex
