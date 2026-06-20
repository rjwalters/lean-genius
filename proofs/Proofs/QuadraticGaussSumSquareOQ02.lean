/-
  Equidistribution of quadratic residues and non-residues mod an odd prime.

  For an odd prime `p`, let `χ = quadraticChar (ZMod p)` be the quadratic
  (Legendre) character: `χ 0 = 0`, `χ a = 1` when `a ≠ 0` is a square, and
  `χ a = -1` when `a` is a non-square.  Mathlib's `quadraticChar_sum_zero`
  records the orthogonality fact that the full character sum vanishes:

      ∑ a : ZMod p, χ a = 0.

  This file extracts the elementary *counting* consequence:  the nonzero
  squares (quadratic residues) and the non-squares (non-residues) are
  **equinumerous**, each class containing exactly `(p-1)/2` elements.

  The argument is a pure sign count.  Since `χ` is quadratic it takes only the
  values `0, 1, -1`, so

      ∑ a, χ a  =  #{a : χ a = 1}  −  #{a : χ a = -1}.

  The left side is `0` by `quadraticChar_sum_zero`, giving
  `#{χ = 1} = #{χ = -1}`.  Separately `χ a = 0 ↔ a = 0`, so the two classes
  exhaust the `p - 1` nonzero elements; together this pins each count at
  `(p-1)/2`.

  This is logically independent of the parent's square identity
  `g² = (-1)^((p-1)/2)·p` — it is the orthogonality/Parseval side of the
  Gauss-sum story rather than the algebraic-square side.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace QuadraticGaussSumSquareOQ02

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic character of `ZMod p` (`p` odd) has a vanishing total sum:
`∑ a, χ a = 0`.  This is `quadraticChar_sum_zero` specialised to `ZMod p`,
with the characteristic hypothesis discharged from `p ≠ 2`. -/
theorem quadraticChar_sum_eq_zero (hp : p ≠ 2) :
    ∑ a : ZMod p, quadraticChar (ZMod p) a = 0 := by
  refine quadraticChar_sum_zero ?_
  rw [ZMod.ringChar_zmod_n]
  exact hp

/-- The squares filter: nonzero quadratic residues are exactly `{a : χ a = 1}`. -/
private def residues (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.filter (fun a => quadraticChar (ZMod p) a = 1)

/-- The non-residues filter: non-squares are exactly `{a : χ a = -1}`. -/
private def nonresidues (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.filter (fun a => quadraticChar (ZMod p) a = -1)

/-- The character sum splits as `#residues − #nonresidues`, because the quadratic
character takes only the values `0, 1, -1`. -/
theorem sum_eq_card_sub_card :
    (∑ a : ZMod p, quadraticChar (ZMod p) a)
      = (residues p).card - (nonresidues p).card := by
  have hval : ∀ a : ZMod p,
      (quadraticChar (ZMod p) a : ℤ)
        = (if quadraticChar (ZMod p) a = 1 then (1 : ℤ) else 0)
          - (if quadraticChar (ZMod p) a = -1 then (1 : ℤ) else 0) := by
    intro a
    rcases quadraticChar_isQuadratic (ZMod p) a with h | h | h <;> rw [h] <;> simp
  calc
    (∑ a : ZMod p, quadraticChar (ZMod p) a)
        = ∑ a : ZMod p,
            ((if quadraticChar (ZMod p) a = 1 then (1 : ℤ) else 0)
              - (if quadraticChar (ZMod p) a = -1 then (1 : ℤ) else 0)) :=
          Finset.sum_congr rfl (fun a _ => hval a)
    _ = (∑ a : ZMod p, if quadraticChar (ZMod p) a = 1 then (1 : ℤ) else 0)
          - (∑ a : ZMod p, if quadraticChar (ZMod p) a = -1 then (1 : ℤ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = (residues p).card - (nonresidues p).card := by
          rw [Finset.sum_boole, Finset.sum_boole]; rfl

/-- **Equidistribution.** The number of quadratic residues equals the number of
non-residues mod an odd prime `p`. -/
theorem card_residues_eq_card_nonresidues (hp : p ≠ 2) :
    (residues p).card = (nonresidues p).card := by
  have h := sum_eq_card_sub_card (p := p)
  rw [quadraticChar_sum_eq_zero hp] at h
  have : ((residues p).card : ℤ) = (nonresidues p).card := by linarith
  exact_mod_cast this

/-- The residues and non-residues together exhaust the `p - 1` nonzero elements. -/
theorem card_residues_add_card_nonresidues :
    (residues p).card + (nonresidues p).card = p - 1 := by
  classical
  -- the two classes are disjoint (`χ a` cannot be both `1` and `-1`)
  have hdisj : Disjoint (residues p) (nonresidues p) := by
    rw [residues, nonresidues, Finset.disjoint_filter]
    intro a _ h1 h2
    rw [h1] at h2
    exact (by decide : ¬ (1 : ℤ) = -1) h2
  -- their union is exactly the set of nonzero elements
  have hunion : residues p ∪ nonresidues p = univ.filter (fun a : ZMod p => a ≠ 0) := by
    rw [residues, nonresidues, ← Finset.filter_or]
    apply Finset.filter_congr
    intro a _
    constructor
    · rintro (h | h) hz
      · rw [(quadraticChar_eq_zero_iff.mpr hz)] at h; exact (by decide : ¬ (0 : ℤ) = 1) h
      · rw [(quadraticChar_eq_zero_iff.mpr hz)] at h; exact (by decide : ¬ (0 : ℤ) = -1) h
    · intro hz
      rcases quadraticChar_isQuadratic (ZMod p) a with h | h | h
      · exact absurd (quadraticChar_eq_zero_iff.mp h) hz
      · exact Or.inl h
      · exact Or.inr h
  -- count the nonzero elements: `p - 1`
  have hcard_nonzero : (univ.filter (fun a : ZMod p => a ≠ 0)).card = p - 1 := by
    have : (univ.filter (fun a : ZMod p => a ≠ 0)) = univ.erase (0 : ZMod p) := by
      ext a; simp [Finset.mem_erase]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard_nonzero]

/-- **Count of quadratic residues.** For an odd prime `p`, exactly `(p-1)/2` of
the elements of `ZMod p` are nonzero squares. -/
theorem card_residues_eq (hp : p ≠ 2) :
    (residues p).card = (p - 1) / 2 := by
  have heq := card_residues_eq_card_nonresidues (p := p) hp
  have hsum := card_residues_add_card_nonresidues (p := p)
  rw [← heq] at hsum
  omega

/-- **Count of non-residues.** Symmetrically, exactly `(p-1)/2` elements are
non-squares. -/
theorem card_nonresidues_eq (hp : p ≠ 2) :
    (nonresidues p).card = (p - 1) / 2 := by
  rw [← card_residues_eq_card_nonresidues (p := p) hp]
  exact card_residues_eq (p := p) hp

end QuadraticGaussSumSquareOQ02
