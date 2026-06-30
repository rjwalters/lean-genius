/-
  Counting quadratic residues: an odd prime `p` has exactly `(p − 1)/2`
  nonzero quadratic residues.

  The classical count follows from the *squaring map* on the unit group.
  The endomorphism `sq : (ZMod p)ˣ →* (ZMod p)ˣ`, `u ↦ u²`, is a group
  homomorphism (the units of a commutative ring form a commutative group).
  Its kernel is the set of square roots of `1`, namely `{1, −1}` — two
  *distinct* elements precisely because `p` is odd — so the first
  isomorphism theorem gives

      |image of sq| = |(ZMod p)ˣ| / |ker sq| = (p − 1) / 2.

  The image of `sq` is exactly the set of nonzero quadratic residues, so
  there are `(p − 1)/2` of them.

  This complements `EulerCriterionSquaresOQ01`: Euler's criterion identifies
  the residues as the `+1`-values of `a ↦ a^((p−1)/2)`; here we instead count
  them directly from the `2`-to-`1` squaring map and its kernel.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open ZMod

namespace EulerCriterionSquaresOQ01OQ01

variable (p : ℕ) [Fact p.Prime] [Fact (2 < p)]

/-- The squaring endomorphism `u ↦ u²` of the unit group `(ZMod p)ˣ`. -/
def sqHom : (ZMod p)ˣ →* (ZMod p)ˣ := powMonoidHom 2

omit [Fact (2 < p)] in
@[simp] theorem sqHom_apply (u : (ZMod p)ˣ) : sqHom p u = u ^ 2 := rfl

/-- `1 ≠ −1` in `(ZMod p)ˣ` for an odd prime: otherwise `1 = −1` in `ZMod p`,
forcing `p ∣ 2`. -/
theorem one_ne_neg_one_units : (1 : (ZMod p)ˣ) ≠ -1 := by
  intro h
  have hz : (1 : ZMod p) = -1 := by
    have := congrArg Units.val h; simpa using this
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hz
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have : 2 < p := Fact.out
  omega

omit [Fact (2 < p)] in
/-- A unit lies in the kernel of squaring iff it is `±1`. -/
theorem mem_sqHom_ker {u : (ZMod p)ˣ} : u ∈ (sqHom p).ker ↔ u = 1 ∨ u = -1 := by
  rw [MonoidHom.mem_ker, sqHom_apply]
  constructor
  · intro h
    have hv : (↑u : ZMod p) ^ 2 = 1 := by
      have := congrArg Units.val h
      simpa [Units.val_pow_eq_pow_val] using this
    rcases sq_eq_one_iff.mp hv with h1 | h1
    · exact Or.inl (Units.val_eq_one.mp h1)
    · refine Or.inr ?_
      apply Units.ext
      rw [h1]; simp
  · rintro (rfl | rfl)
    · exact one_pow 2
    · apply Units.ext; push_cast; ring

/-- The kernel of squaring is `{1, −1}`, hence has cardinality `2`. -/
theorem card_sqHom_ker : Nat.card (sqHom p).ker = 2 := by
  have hset : ((sqHom p).ker : Set (ZMod p)ˣ) = {1, -1} := by
    ext u
    rw [SetLike.mem_coe, mem_sqHom_ker]
    simp [Set.mem_insert_iff]
  have heq : Nat.card (sqHom p).ker = ((sqHom p).ker : Set (ZMod p)ˣ).ncard := rfl
  rw [heq, hset, Set.ncard_pair (one_ne_neg_one_units p)]

/-- **Quadratic-residue count (units form).** The squaring map's image — the
quadratic residues among the units — has cardinality `(p − 1)/2`. -/
theorem card_sqHom_range : Nat.card (sqHom p).range = (p - 1) / 2 := by
  have hcard : Nat.card (sqHom p).ker * Nat.card (sqHom p).range = Nat.card (ZMod p)ˣ := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have hu : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [card_sqHom_ker, hu] at hcard
  omega

omit [Fact (2 < p)] in
/-- A nonzero residue characterisation: for a unit `u`, the field element `↑u`
is a square iff `u` is a square in the unit group (i.e. lies in the image of
the squaring map). -/
theorem isSquare_coe_iff_mem_range {u : (ZMod p)ˣ} :
    IsSquare (↑u : ZMod p) ↔ u ∈ (sqHom p).range := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hr
      exact u.ne_zero hr
    obtain ⟨w, rfl⟩ := (isUnit_iff_ne_zero.mpr hr0)
    refine ⟨w, ?_⟩
    apply Units.ext
    rw [sqHom_apply, Units.val_pow_eq_pow_val]
    rw [hr]; ring
  · rintro ⟨v, rfl⟩
    exact ⟨↑v, by rw [sqHom_apply, Units.val_pow_eq_pow_val]; ring⟩

/-- **Quadratic-residue count.** An odd prime `p` has exactly `(p − 1)/2`
nonzero quadratic residues in `ZMod p`. -/
theorem card_nonzero_quadratic_residues :
    Nat.card {a : ZMod p // a ≠ 0 ∧ IsSquare a} = (p - 1) / 2 := by
  rw [← card_sqHom_range p]
  refine Nat.card_congr (Equiv.symm ?_)
  refine (Equiv.subtypeEquivRight (fun u => (isSquare_coe_iff_mem_range p).symm)).trans ?_
  refine (@Equiv.subtypeEquiv (ZMod p)ˣ {a : ZMod p // a ≠ 0}
      (fun u => IsSquare (↑u : ZMod p)) (fun x => IsSquare (x : ZMod p))
      unitsEquivNeZero (fun u => Iff.rfl)).trans ?_
  exact Equiv.subtypeSubtypeEquivSubtypeInter (· ≠ (0 : ZMod p)) IsSquare

/-! ### Concrete check modulo 7 -/

/-- Mod `7` there are `(7−1)/2 = 3` nonzero quadratic residues, namely
`{1, 2, 4}` (the squares `1², 2², 3²`). -/
theorem card_residues_mod_seven :
    Nat.card {a : ZMod 7 // a ≠ 0 ∧ IsSquare a} = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (2 < 7) := ⟨by norm_num⟩
  exact card_nonzero_quadratic_residues 7

end EulerCriterionSquaresOQ01OQ01
