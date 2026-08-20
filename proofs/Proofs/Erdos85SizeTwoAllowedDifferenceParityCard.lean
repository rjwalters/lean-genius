import Proofs.Erdos85ZModProjectionFiber
import Proofs.Erdos85SizeTwoEigenlineCyclicQuotient

/-!
# Parity classes of the allowed cyclic differences

Node: BinarySizeTwoCyclicPackingBound beneath outline A.5.3.

Reduction from ZMod q to ZMod 2 has fibers of size q/2.  The allowed
difference type deletes two residues.  When those holes have different
mod-two images, it deletes exactly one point from each projection fiber.
-/

namespace Erdos85

noncomputable section

private theorem zmodTwo_eq_left_iff_ne_right
    (x y z : ZMod 2) (hxy : x ≠ y) :
    z = x ↔ z ≠ y := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [ne_eq, eq_comm]

/-- Every projection class of the two-hole allowed-difference type has
cardinality q/2−1 when the holes lie in opposite mod-two classes. -/
theorem sizeTwoAllowedDifference_projection_card
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (a : ZMod q)
    (hholes :
      ZMod.castHom h2q (ZMod 2) a ≠
        ZMod.castHom h2q (ZMod 2) (-1 - a))
    (z : ZMod 2) :
    ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
      fun u => ZMod.castHom h2q (ZMod 2) u.1 = z).card = q / 2 - 1 := by
  classical
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  let b : ZMod q := -1 - a
  let S : Finset (ZMod q) := projectionFiber φ z
  let U : Finset (sizeTwoAllowedDifference q a) :=
    (Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
      fun u => φ u.1 = z
  have himage :
      U.image (fun u : sizeTwoAllowedDifference q a => u.1) =
        (S.erase a).erase b := by
    ext x
    simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, S, projectionFiber, Finset.mem_erase]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, u.2.1, hu⟩
      simpa [b] using u.2.2
    · intro hx
      refine ⟨⟨x, hx.2.1, ?_⟩, hx.2.2, rfl⟩
      simpa [b] using hx.1
  have hcardImage : U.card = ((S.erase a).erase b).card := by
    rw [← himage, Finset.card_image_iff.mpr]
    exact Subtype.val_injective.injOn
  have hfiber : S.card = q / 2 := by
    simpa [S, φ] using card_projectionFiber_zmod_castHom h2q z
  have hsplit : (a ∈ S ∧ b ∉ S) ∨ (a ∉ S ∧ b ∈ S) := by
    have hab :
        φ a = z ↔ φ b ≠ z := by
      simpa [eq_comm] using
        (zmodTwo_eq_left_iff_ne_right (φ a) (φ b) z hholes)
    by_cases ha : a ∈ S
    · left
      constructor
      · exact ha
      · intro hb
        have haz : φ a = z := by simpa [S, projectionFiber] using ha
        have hbz : φ b = z := by simpa [S, projectionFiber] using hb
        exact (hab.mp haz) hbz
    · right
      constructor
      · exact ha
      · have hbnz : φ b ≠ z → False := by
          intro hbnz
          have haz : φ a = z := (hab.mpr hbnz)
          exact ha (by simpa [S, projectionFiber] using haz)
        have hbz : φ b = z := not_not.mp hbnz
        simpa [S, projectionFiber] using hbz
  change U.card = q / 2 - 1
  rw [hcardImage]
  rcases hsplit with h | h
  · have hbErase : b ∉ S.erase a := by simp [h.2]
    rw [Finset.erase_eq_of_notMem hbErase,
      Finset.card_erase_of_mem h.1, hfiber]
  · rw [Finset.erase_eq_of_notMem h.1,
      Finset.card_erase_of_mem h.2, hfiber]

/-- The zero and nonzero mod-two classes of allowed differences are both
balanced after deleting opposite-parity holes. -/
theorem sizeTwoAllowedDifference_binaryParity_cards
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (a : ZMod q)
    (hholes :
      ZMod.castHom h2q (ZMod 2) a ≠
        ZMod.castHom h2q (ZMod 2) (-1 - a)) :
    ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
      (fun u => ZMod.castHom h2q (ZMod 2) u.1 = 0)).card = q / 2 - 1 ∧
    ((Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
      (fun u => ZMod.castHom h2q (ZMod 2) u.1 ≠ 0)).card = q / 2 - 1 := by
  constructor
  · exact sizeTwoAllowedDifference_projection_card h2q a hholes 0
  · rw [show ((Finset.univ : Finset
        (sizeTwoAllowedDifference q a)).filter
          (fun u => ZMod.castHom h2q (ZMod 2) u.1 ≠ 0)) =
        (Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
          (fun u => ZMod.castHom h2q (ZMod 2) u.1 = 1) by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (zmodTwo_eq_left_iff_ne_right 1 0
        (ZMod.castHom h2q (ZMod 2) u.1) (by decide)).symm]
    exact sizeTwoAllowedDifference_projection_card h2q a hholes 1

end

end Erdos85

#print axioms Erdos85.sizeTwoAllowedDifference_projection_card
#print axioms Erdos85.sizeTwoAllowedDifference_binaryParity_cards
