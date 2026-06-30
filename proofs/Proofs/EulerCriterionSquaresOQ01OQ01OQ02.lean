/-
  Sum of the nonzero quadratic residues vanishes: for an odd prime `p > 3`,

      ∑_{x ≠ 0, x a square} x = 0   in   ZMod p.

  The nonzero quadratic residues form a multiplicative subgroup of the field
  `ZMod p`: a product of two squares is a square. Hence multiplication by a
  fixed nonzero square `t` permutes the residue set among itself, so the total
  sum `S = ∑ x` is unchanged when every term is scaled by `t`:

      t · S = ∑ x (t·x) = ∑ x x = S,   i.e.   (t − 1) · S = 0.

  Taking the explicit witness `t = 4 = 2²` (a nonzero square, and `≠ 1` once
  `p > 3`), the factor `t − 1 = 3` is nonzero in the field, so `S = 0`.

  This is the additive companion to the parent's *counting* result
  (`euler-criterion-squares-oq-01-oq-01`, there are `(p−1)/2` residues): the
  same multiplicative closure that fixes the cardinality also forces the sum to
  vanish. It is genuinely distinct from Mathlib's `quadraticChar_sum_zero`,
  which sums the *character values* `±1`, not the residue elements themselves.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Finset

namespace EulerCriterionSquaresOQ01OQ01OQ02

variable (p : ℕ) [Fact p.Prime]

/-- The finite set of nonzero quadratic residues in `ZMod p`. -/
def residues : Finset (ZMod p) :=
  Finset.univ.filter (fun x : ZMod p => x ≠ 0 ∧ IsSquare x)

@[simp] theorem mem_residues {x : ZMod p} :
    x ∈ residues p ↔ x ≠ 0 ∧ IsSquare x := by
  simp [residues]

/-- `4 = 2²` is a square in any commutative ring. -/
theorem isSquare_four : IsSquare (4 : ZMod p) := ⟨2, by norm_num⟩

/-- For `p > 3`, the field element `2` is nonzero (`p ∤ 2`). -/
theorem two_ne_zero (hp : 3 < p) : (2 : ZMod p) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  simpa using h

/-- For `p > 3`, the field element `4 = 2·2` is nonzero (`p ∤ 4`). -/
theorem four_ne_zero (hp : 3 < p) : (4 : ZMod p) ≠ 0 := by
  have h4 : (4 : ZMod p) = 2 * 2 := by norm_num
  rw [h4]
  exact mul_ne_zero (two_ne_zero p hp) (two_ne_zero p hp)

/-- For `p > 3`, the field element `3 = 4 − 1` is nonzero (`p ∤ 3`). -/
theorem three_ne_zero (hp : 3 < p) : (3 : ZMod p) ≠ 0 := by
  have h : ((3 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 3]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  simpa using h

/-- **Closure under scaling.** Multiplying a nonzero residue by `4` (a nonzero
square) lands back in the residue set. -/
theorem mul_four_mem_residues (hp : 3 < p) {x : ZMod p}
    (hx : x ∈ residues p) : (4 : ZMod p) * x ∈ residues p := by
  rw [mem_residues] at hx ⊢
  obtain ⟨hx0, hxsq⟩ := hx
  exact ⟨mul_ne_zero (four_ne_zero p hp) hx0, (isSquare_four p).mul hxsq⟩

/-- Scaling by `4` is a bijection of the residue set onto itself, hence the
image finset is the set itself. -/
theorem image_mul_four (hp : 3 < p) :
    (residues p).image (fun x => (4 : ZMod p) * x) = residues p := by
  have hinj : Function.Injective (fun x : ZMod p => (4 : ZMod p) * x) :=
    fun a b h => mul_left_cancel₀ (four_ne_zero p hp) h
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact mul_four_mem_residues p hp hx
  · exact le_of_eq (Finset.card_image_of_injective _ hinj).symm

/-- **The sum is fixed by scaling.** `4 · S = S` where `S` is the residue sum. -/
theorem four_mul_sum_eq_sum (hp : 3 < p) :
    (4 : ZMod p) * ∑ x ∈ residues p, x = ∑ x ∈ residues p, x := by
  have hinj : ∀ x ∈ residues p, ∀ y ∈ residues p,
      (4 : ZMod p) * x = 4 * y → x = y :=
    fun x _ y _ h => mul_left_cancel₀ (four_ne_zero p hp) h
  calc
    (4 : ZMod p) * ∑ x ∈ residues p, x
        = ∑ x ∈ residues p, (4 : ZMod p) * x := by rw [Finset.mul_sum]
    _ = ∑ x ∈ (residues p).image (fun x => (4 : ZMod p) * x), x := by
          rw [Finset.sum_image hinj]
    _ = ∑ x ∈ residues p, x := by rw [image_mul_four p hp]

/-- **Main theorem.** For an odd prime `p > 3`, the sum of the nonzero
quadratic residues in `ZMod p` is zero. -/
theorem sum_quadratic_residues_eq_zero (hp : 3 < p) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0 ∧ IsSquare x), x = 0 := by
  have hfix := four_mul_sum_eq_sum p hp
  have h3 : (3 : ZMod p) * ∑ x ∈ residues p, x = 0 := by linear_combination hfix
  have : ∑ x ∈ residues p, x = 0 :=
    (mul_eq_zero.mp h3).resolve_left (three_ne_zero p hp)
  simpa [residues] using this

/-! ### Concrete checks at small primes -/

/-- Mod `5` the nonzero residues are `{1, 4}` with sum `5 ≡ 0`. -/
theorem sum_residues_mod_five :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod 5 => x ≠ 0 ∧ IsSquare x), x = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact sum_quadratic_residues_eq_zero 5 (by norm_num)

/-- Mod `7` the nonzero residues are `{1, 2, 4}` with sum `7 ≡ 0`. -/
theorem sum_residues_mod_seven :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod 7 => x ≠ 0 ∧ IsSquare x), x = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact sum_quadratic_residues_eq_zero 7 (by norm_num)

/-- Mod `11` the nonzero residues are `{1, 3, 4, 5, 9}` with sum `22 ≡ 0`. -/
theorem sum_residues_mod_eleven :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod 11 => x ≠ 0 ∧ IsSquare x), x = 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact sum_quadratic_residues_eq_zero 11 (by norm_num)

end EulerCriterionSquaresOQ01OQ01OQ02
