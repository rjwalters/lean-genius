/-
  Equidistribution of squares and non-squares in an arbitrary finite field.

  This is the finite-field generalization of the parent's mod-`p` count.  Let
  `F` be a finite field of odd order `q = |F|` (equivalently `ringChar F ≠ 2`),
  and let `χ = quadraticChar F` be its quadratic character: `χ 0 = 0`, `χ a = 1`
  exactly when `a ≠ 0` is a square, and `χ a = -1` exactly when `a` is a
  non-square.  Mathlib's `quadraticChar_sum_zero` records the orthogonality
  fact that the full character sum vanishes:

      ∑ a : F, χ a = 0.

  The parent file (`QuadraticGaussSumSquareOQ02`) extracted the counting
  consequence over `ZMod p`.  Here we answer the parent's open question: the
  *same* vanishing-sum / quadraticity mechanism works verbatim over any finite
  field `F` of odd characteristic, and we phrase the conclusion directly in
  terms of `IsSquare` rather than the character-value filters:

      #{ a : F | a ≠ 0 ∧ IsSquare a }  =  (q - 1) / 2,
      #{ a : F | ¬ IsSquare a }        =  (q - 1) / 2.

  The argument is a pure sign count.  Because `χ` is quadratic it takes only the
  values `0, 1, -1`, so

      ∑ a, χ a  =  #{a : χ a = 1}  −  #{a : χ a = -1}.

  The left side is `0`, giving `#{χ = 1} = #{χ = -1}`.  Separately `χ a = 0 ↔
  a = 0`, so the two classes exhaust the `q - 1` nonzero elements; together this
  pins each count at `(q-1)/2`.  Finally `quadraticChar_one_iff_isSquare` and
  `quadraticChar_neg_one_iff_not_isSquare` translate the character-value filters
  into the `IsSquare` description.

  This generalizes the parent over `ZMod p` (the prime case is `F = ZMod p`) and
  is logically independent of the algebraic square identity
  `g² = (-1)^((q-1)/2)·…` on the Gauss-sum side.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace QuadraticGaussSumSquareOQ02OQ01

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character of a finite field `F` of odd characteristic has a
vanishing total sum: `∑ a, χ a = 0`.  This is `quadraticChar_sum_zero`. -/
theorem quadraticChar_sum_eq_zero (hF : ringChar F ≠ 2) :
    ∑ a : F, quadraticChar F a = 0 :=
  quadraticChar_sum_zero hF

/-- The squares filter: nonzero quadratic residues are exactly `{a : χ a = 1}`. -/
def residues (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  univ.filter (fun a => quadraticChar F a = 1)

/-- The non-residues filter: non-squares are exactly `{a : χ a = -1}`. -/
def nonresidues (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  univ.filter (fun a => quadraticChar F a = -1)

/-- The character sum splits as `#residues − #nonresidues`, because the quadratic
character takes only the values `0, 1, -1`. -/
theorem sum_eq_card_sub_card :
    (∑ a : F, quadraticChar F a)
      = (residues F).card - (nonresidues F).card := by
  have hval : ∀ a : F,
      (quadraticChar F a : ℤ)
        = (if quadraticChar F a = 1 then (1 : ℤ) else 0)
          - (if quadraticChar F a = -1 then (1 : ℤ) else 0) := by
    intro a
    rcases quadraticChar_isQuadratic F a with h | h | h <;> rw [h] <;> simp
  calc
    (∑ a : F, quadraticChar F a)
        = ∑ a : F,
            ((if quadraticChar F a = 1 then (1 : ℤ) else 0)
              - (if quadraticChar F a = -1 then (1 : ℤ) else 0)) :=
          Finset.sum_congr rfl (fun a _ => hval a)
    _ = (∑ a : F, if quadraticChar F a = 1 then (1 : ℤ) else 0)
          - (∑ a : F, if quadraticChar F a = -1 then (1 : ℤ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = (residues F).card - (nonresidues F).card := by
          rw [Finset.sum_boole, Finset.sum_boole]; rfl

/-- **Equidistribution.** The number of quadratic residues equals the number of
non-residues in any finite field of odd characteristic. -/
theorem card_residues_eq_card_nonresidues (hF : ringChar F ≠ 2) :
    (residues F).card = (nonresidues F).card := by
  have h := sum_eq_card_sub_card (F := F)
  rw [quadraticChar_sum_eq_zero hF] at h
  have : ((residues F).card : ℤ) = (nonresidues F).card := by linarith
  exact_mod_cast this

/-- The residues and non-residues together exhaust the `q - 1` nonzero elements. -/
theorem card_residues_add_card_nonresidues :
    (residues F).card + (nonresidues F).card = Fintype.card F - 1 := by
  classical
  -- the two classes are disjoint (`χ a` cannot be both `1` and `-1`)
  have hdisj : Disjoint (residues F) (nonresidues F) := by
    rw [residues, nonresidues, Finset.disjoint_filter]
    intro a _ h1 h2
    rw [h1] at h2
    exact (by decide : ¬ (1 : ℤ) = -1) h2
  -- their union is exactly the set of nonzero elements
  have hunion : residues F ∪ nonresidues F = univ.filter (fun a : F => a ≠ 0) := by
    rw [residues, nonresidues, ← Finset.filter_or]
    apply Finset.filter_congr
    intro a _
    constructor
    · rintro (h | h) hz
      · rw [(quadraticChar_eq_zero_iff.mpr hz)] at h; exact (by decide : ¬ (0 : ℤ) = 1) h
      · rw [(quadraticChar_eq_zero_iff.mpr hz)] at h; exact (by decide : ¬ (0 : ℤ) = -1) h
    · intro hz
      rcases quadraticChar_isQuadratic F a with h | h | h
      · exact absurd (quadraticChar_eq_zero_iff.mp h) hz
      · exact Or.inl h
      · exact Or.inr h
  -- count the nonzero elements: `q - 1`
  have hcard_nonzero : (univ.filter (fun a : F => a ≠ 0)).card = Fintype.card F - 1 := by
    have : (univ.filter (fun a : F => a ≠ 0)) = univ.erase (0 : F) := by
      ext a; simp [Finset.mem_erase]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard_nonzero]

/-- **Count of quadratic residues.** In a finite field `F` of odd order `q`,
exactly `(q-1)/2` of the elements are nonzero squares (as character values). -/
theorem card_residues_eq (hF : ringChar F ≠ 2) :
    (residues F).card = (Fintype.card F - 1) / 2 := by
  have heq := card_residues_eq_card_nonresidues (F := F) hF
  have hsum := card_residues_add_card_nonresidues (F := F)
  rw [← heq] at hsum
  omega

/-- **Count of non-residues.** Symmetrically, exactly `(q-1)/2` elements are
non-squares (as character values). -/
theorem card_nonresidues_eq (hF : ringChar F ≠ 2) :
    (nonresidues F).card = (Fintype.card F - 1) / 2 := by
  rw [← card_residues_eq_card_nonresidues (F := F) hF]
  exact card_residues_eq (F := F) hF

/-! ### `IsSquare`-phrased counts

The character-value filters translate into the natural predicates: `χ a = 1` for
a nonzero `a` means `IsSquare a`, and `χ a = -1` means `¬ IsSquare a`.  These give
the reader-facing form of the equidistribution theorem. -/

/-- The residue filter is exactly the set of nonzero squares. -/
theorem residues_eq_filter_isSquare :
    residues F = univ.filter (fun a : F => a ≠ 0 ∧ IsSquare a) := by
  rw [residues]
  apply Finset.filter_congr
  intro a _
  constructor
  · intro h
    have ha : a ≠ 0 := by
      rintro rfl; rw [quadraticChar_zero] at h; exact (by decide : ¬ (0 : ℤ) = 1) h
    exact ⟨ha, (quadraticChar_one_iff_isSquare ha).mp h⟩
  · rintro ⟨ha, hsq⟩
    exact (quadraticChar_one_iff_isSquare ha).mpr hsq

/-- The non-residue filter is exactly the set of non-squares (`0` is a square, so
it is automatically excluded). -/
theorem nonresidues_eq_filter_not_isSquare :
    nonresidues F = univ.filter (fun a : F => ¬ IsSquare a) := by
  rw [nonresidues]
  apply Finset.filter_congr
  intro a _
  exact ⟨fun h => quadraticChar_neg_one_iff_not_isSquare.mp h,
         fun h => quadraticChar_neg_one_iff_not_isSquare.mpr h⟩

/-- **Main theorem (nonzero squares).** In a finite field of odd order `q`, the
number of nonzero squares is exactly `(q-1)/2`. -/
theorem card_nonzero_isSquare_eq (hF : ringChar F ≠ 2) :
    (univ.filter (fun a : F => a ≠ 0 ∧ IsSquare a)).card = (Fintype.card F - 1) / 2 := by
  rw [← residues_eq_filter_isSquare]
  exact card_residues_eq hF

/-- **Main theorem (non-squares).** In a finite field of odd order `q`, the number
of non-squares is exactly `(q-1)/2`. -/
theorem card_not_isSquare_eq (hF : ringChar F ≠ 2) :
    (univ.filter (fun a : F => ¬ IsSquare a)).card = (Fintype.card F - 1) / 2 := by
  rw [← nonresidues_eq_filter_not_isSquare]
  exact card_nonresidues_eq hF

/-- **Equidistribution, `IsSquare` form.** The nonzero squares and the non-squares
are equinumerous. -/
theorem card_nonzero_isSquare_eq_card_not_isSquare (hF : ringChar F ≠ 2) :
    (univ.filter (fun a : F => a ≠ 0 ∧ IsSquare a)).card
      = (univ.filter (fun a : F => ¬ IsSquare a)).card := by
  rw [card_nonzero_isSquare_eq hF, card_not_isSquare_eq hF]

end QuadraticGaussSumSquareOQ02OQ01
