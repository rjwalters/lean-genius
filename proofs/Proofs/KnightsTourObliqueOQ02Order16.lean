/-
  Knight's Tour Oblique Angles: The Order-16 Symmetry Group (OQ-02, Target D → E)

  The sibling files established two *independent* symmetries of the oblique-turn
  count on closed knight's tours:

  * the order-8 dihedral **board group** `D4` acting via `applyD4Tour`
    (`KnightsTourObliqueOQ02.lean`, packaged as `Group D4` + `MulAction D4`), and
  * the order-2 **time reversal** `reverseTour`
    (`KnightsTourObliqueOQ02Reverse.lean` / `…ReverseCount.lean`), whose
    count-invariance capstone is `obliqueCount_reverseTour`.

  This file fuses them into the full **order-16 symmetry group** acting on the
  level sets of `obliqueDistribution`.

  ## What this file proves (verified, 0 sorries, 0 axioms)

  * `applyD4Tour_reverseTour_comm` — the two symmetries **commute**: a board
    transformation of a reversed tour equals the reversal of the transformed
    tour. This is the mathematical crux: because reversal permutes the
    *traversal order* while `D4` permutes the *squares*, they commute, so the
    combined group is the **direct product** `D4 × C2`, not a semidirect one.
  * `levelSet_image_reverseTour_eq` — reversal restricts to a bijection of each
    histogram level set onto itself (the reversal analogue of the D4 result
    `levelSet_image_applyD4Tour_eq`).
  * `C2` — the order-2 reversal group (a `Bool` synonym under `xor`), and the
    combined group `D4xC2 := D4 × C2` of order 16, acting on `ClosedTour` via
    `applyD4Tour g.1 (revBool g.2 ·)`.
  * `fullOrbit_card_dvd_sixteen` — every orbit of the order-16 group has
    cardinality *dividing* 16, so each level set of `obliqueDistribution`
    decomposes into blocks of size `1, 2, 4, 8` or `16`
    (`fullOrbit_card_eq`). This strictly enlarges the D4 orbit-divisibility
    picture `d4Orbit_card_dvd_eight` by the independent reversal factor.

  Parent: `KnightsTourOblique.lean`.
  Siblings: `KnightsTourObliqueOQ02.lean`, `…OQ02Reverse.lean`, `…OQ02ReverseCount.lean`.
-/

import Mathlib
import Proofs.KnightsTourObliqueOQ02ReverseCount

namespace KnightsTourOblique

open List

/-! ## The two symmetries commute -/

/-- The squares of a board-transformed tour are the mapped squares (`rfl`). -/
theorem applyD4Tour_squares (g : Bool × Fin 4) (t : ClosedTour) :
    (applyD4Tour g t).squares = t.squares.map (applyD4 g) := rfl

/-- **Commutation of the two symmetries.** Applying a `D4` board transformation
    to a time-reversed tour equals reversing the transformed tour:
    `applyD4Tour g (reverseTour t) = reverseTour (applyD4Tour g t)`.

    Both sides have square list `(t.squares.map (applyD4 g)).reverse`, since
    `List.map` commutes with `List.reverse`. Because the board action permutes
    squares while reversal permutes traversal order, the two commute — hence
    the combined symmetry group is a *direct* product. -/
theorem applyD4Tour_reverseTour_comm (g : Bool × Fin 4) (t : ClosedTour) :
    applyD4Tour g (reverseTour t) = reverseTour (applyD4Tour g t) := by
  rw [closedTour_eq_iff]
  simp only [applyD4Tour_squares, reverseTour_squares, List.map_reverse]

/-! ## Reversal restricts to a bijection of each level set -/

/-- Reversal maps `levelSet k` into itself (count-invariance,
    `obliqueCount_reverseTour`). -/
theorem levelSet_image_reverseTour_subset (k : ℕ) :
    (levelSet k).image reverseTour ⊆ levelSet k := by
  intro u hu
  simp only [Finset.mem_image, levelSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hu ⊢
  obtain ⟨t, htk, hgu⟩ := hu
  rw [← hgu, obliqueCount_reverseTour]
  exact htk

/-- Reversal preserves the cardinality of a level set (injectivity). -/
theorem levelSet_image_reverseTour_card (k : ℕ) :
    ((levelSet k).image reverseTour).card = (levelSet k).card :=
  Finset.card_image_of_injective _ reverseTour_injective

/-- **Reversal is a level-set bijection**: time reversal induces a bijection of
    `levelSet k` onto itself, the reversal analogue of the D4 result
    `levelSet_image_applyD4Tour_eq`. -/
theorem levelSet_image_reverseTour_eq (k : ℕ) :
    (levelSet k).image reverseTour = levelSet k := by
  apply Finset.eq_of_subset_of_card_le (levelSet_image_reverseTour_subset k)
  rw [levelSet_image_reverseTour_card]

/-! ## The order-2 reversal group `C2` -/

/-- Type synonym carrying the order-2 cyclic group of time reversal. A synonym
    is required because `Bool` already carries Mathlib's boolean-ring `Mul`
    (`and`, unit `true`), a *different* algebraic structure from the reversal
    group (`xor`, unit `false`, every element self-inverse). -/
def C2 : Type := Bool

namespace C2

instance : DecidableEq C2 := inferInstanceAs (DecidableEq Bool)
instance : Fintype C2 := inferInstanceAs (Fintype Bool)
instance : Mul C2 := ⟨xor⟩
instance : One C2 := ⟨false⟩
instance : Inv C2 := ⟨id⟩

/-- `C2` is a group: `xor` is associative with unit `false`, and every element
    is its own inverse. All laws are finite Boolean identities (`decide`). -/
instance : Group C2 where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

/-- The reversal group has order 2. -/
@[simp] theorem card_C2 : Fintype.card C2 = 2 := by
  show Fintype.card Bool = 2
  simp

end C2

/-! ## The reversal endofunction selected by a `C2`/`Bool` flag -/

/-- `revBool b t` is the identity for `b = false` and time reversal for
    `b = true`. This turns a `Bool` flag into the corresponding element of the
    reversal action. -/
def revBool (b : Bool) (t : ClosedTour) : ClosedTour :=
  bif b then reverseTour t else t

@[simp] theorem revBool_false (t : ClosedTour) : revBool false t = t := rfl
@[simp] theorem revBool_true (t : ClosedTour) : revBool true t = reverseTour t := rfl

/-- The reversal flag composes by `xor`: `revBool (b₂ ⊕ b₁) = revBool b₂ ∘
    revBool b₁`. The only nontrivial case is `b₂ = b₁ = true`, where the two
    reversals cancel by `reverseTour_involutive`. -/
theorem revBool_mul (b₂ b₁ : Bool) (t : ClosedTour) :
    revBool (xor b₂ b₁) t = revBool b₂ (revBool b₁ t) := by
  cases b₂ <;> cases b₁
  · rfl
  · rfl
  · rfl
  · exact (reverseTour_involutive t).symm

/-- The board action commutes with the reversal flag:
    `applyD4Tour g (revBool b t) = revBool b (applyD4Tour g t)`. Immediate from
    `applyD4Tour_reverseTour_comm` in the `b = true` case. -/
theorem applyD4Tour_revBool_comm (g : Bool × Fin 4) (b : Bool) (t : ClosedTour) :
    applyD4Tour g (revBool b t) = revBool b (applyD4Tour g t) := by
  cases b with
  | false => rfl
  | true => simpa only [revBool_true] using applyD4Tour_reverseTour_comm g t

/-! ## The full order-16 symmetry group `D4xC2 = D4 × C2` -/

/-- The full symmetry group: the order-8 board group `D4` times the order-2
    reversal group `C2`. Because reversal commutes with every board symmetry
    (`applyD4Tour_reverseTour_comm`), this is a genuine *direct* product of
    order `8 · 2 = 16`. -/
abbrev D4xC2 : Type := D4 × C2

/-- The order-16 group acts on closed tours: `(g, ε)` reverses (if `ε = true`)
    then applies the board transformation `g`. `one_smul` is `applyD4Tour_id`
    on the unreversed tour; `mul_smul` uses the composition law
    `applyD4Tour_mul`, the flag law `revBool_mul`, and the commutation
    `applyD4Tour_revBool_comm`. -/
instance : MulAction D4xC2 ClosedTour where
  smul g t := applyD4Tour g.1 (revBool g.2 t)
  one_smul t := by
    show applyD4Tour (false, 0) (revBool false t) = t
    rw [revBool_false]
    exact applyD4Tour_id t
  mul_smul g₂ g₁ t := by
    obtain ⟨a₂, e₂⟩ := g₂
    obtain ⟨a₁, e₁⟩ := g₁
    show applyD4Tour (d4Mul a₂ a₁) (revBool (xor e₂ e₁) t)
        = applyD4Tour a₂ (revBool e₂ (applyD4Tour a₁ (revBool e₁ t)))
    rw [applyD4Tour_mul, revBool_mul, applyD4Tour_revBool_comm]

@[simp] theorem d4xc2_smul_def (g : D4xC2) (t : ClosedTour) :
    g • t = applyD4Tour g.1 (revBool g.2 t) := rfl

/-- The full symmetry group has order 16. -/
@[simp] theorem card_D4xC2 : Fintype.card D4xC2 = 16 := by
  rw [Fintype.card_prod, D4.card_D4, C2.card_C2]

/-! ## Orbit-cardinality divisibility -/

/-- The full symmetry orbit of a tour: the image of the 16-element group under
    `· • t`. -/
noncomputable def fullOrbit (t : ClosedTour) : Finset ClosedTour :=
  (Finset.univ : Finset D4xC2).image (fun g => g • t)

/-- Every tour lies in its own full orbit (witness: the group identity). -/
theorem tour_mem_fullOrbit_self (t : ClosedTour) : t ∈ fullOrbit t := by
  simp only [fullOrbit, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨1, one_smul _ t⟩

/-- The `Finset`-valued full orbit coincides with Mathlib's `MulAction.orbit`. -/
theorem fullOrbit_eq_orbit_toFinset (t : ClosedTour)
    [Fintype (MulAction.orbit D4xC2 t)] :
    fullOrbit t = (MulAction.orbit D4xC2 t).toFinset := by
  ext u
  rw [Set.mem_toFinset, MulAction.mem_orbit_iff]
  constructor
  · intro hu
    simp only [fullOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨g, hg⟩ := hu
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    simp only [fullOrbit, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨g, hg⟩

/-- **Sharp order-16 orbit divisibility (headline).** Every orbit of the full
    symmetry group has cardinality *dividing* `|D4 × C2| = 16`, by the
    orbit-stabilizer theorem. This strictly enlarges `d4Orbit_card_dvd_eight`
    by the independent reversal factor. -/
theorem fullOrbit_card_dvd_sixteen (t : ClosedTour) : (fullOrbit t).card ∣ 16 := by
  classical
  haveI : Fintype (MulAction.orbit D4xC2 t) := Set.fintypeRange (fun g : D4xC2 => g • t)
  calc (fullOrbit t).card
      = Fintype.card (MulAction.orbit D4xC2 t) := by
        rw [fullOrbit_eq_orbit_toFinset, Set.toFinset_card]
    _ ∣ Fintype.card D4xC2 :=
        ⟨Fintype.card (MulAction.stabilizer D4xC2 t),
          (MulAction.card_orbit_mul_card_stabilizer_eq_card_group D4xC2 t).symm⟩
    _ = 16 := card_D4xC2

/-- **Block-size enumeration.** Combining `fullOrbit_card_dvd_sixteen` with
    nonemptiness, every full orbit has cardinality exactly one of
    `1, 2, 4, 8, 16` — the divisor lattice of 16. -/
theorem fullOrbit_card_eq (t : ClosedTour) :
    (fullOrbit t).card = 1 ∨ (fullOrbit t).card = 2 ∨ (fullOrbit t).card = 4 ∨
      (fullOrbit t).card = 8 ∨ (fullOrbit t).card = 16 := by
  have hd : (fullOrbit t).card ∣ 16 := fullOrbit_card_dvd_sixteen t
  have hpos : 1 ≤ (fullOrbit t).card :=
    Finset.card_pos.mpr ⟨t, tour_mem_fullOrbit_self t⟩
  have hle : (fullOrbit t).card ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  set n := (fullOrbit t).card with hn
  clear_value n
  interval_cases n <;> revert hd <;> decide

end KnightsTourOblique
