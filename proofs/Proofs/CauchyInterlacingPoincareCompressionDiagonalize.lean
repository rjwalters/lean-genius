import Mathlib
import Proofs.CauchyInterlacingPoincareCompression

/-
# Diagonalizability transfer and the minpoly degree formula across a reducing pair

Parent: `Proofs.CauchyInterlacingPoincareCompression`, whose capstone
`minpoly_eq_lcm_compress_of_reducing` proves that on a reducing subspace `H`
(both `H` and `Hᗮ` are `T`-invariant) the ambient minimal polynomial is the
least common multiple of the two block minimal polynomials:

  `minpoly T = lcm (minpoly (compress T H)) (minpoly (compress T Hᗮ))`.

This file reads two structural consequences off that `lcm` identity.

* **Diagonalizability transfer.**  Over a field a linear operator is
  diagonalizable exactly when its minimal polynomial is squarefree (semisimple /
  separable).  Since `minpoly T = lcm a b`, and squarefreeness is compatible with
  the `lcm`, `T` is diagonalizable **iff both compression blocks are**:

    `Squarefree (minpoly T)
       ↔ Squarefree (minpoly (compress T H)) ∧ Squarefree (minpoly (compress T Hᗮ))`.

  The forward direction is divisor-monotonicity of `Squarefree` (each block
  minpoly divides `lcm`); the reverse is the general fact that the `lcm` of two
  squarefree elements of a normalized-GCD unique factorization monoid is again
  squarefree (`squarefree_lcm`, proved here from the `normalizedFactors` calculus:
  the factor multiset of an `lcm` is dominated by the *union* of the block factor
  multisets, and a `union` of `Nodup` multisets is `Nodup`).

* **Degree formula.**  The degree shadow of `minpoly T = lcm a b`, via the
  `lcm`/`gcd` duality `gcd a b · lcm a b ~ a · b`
  (`gcd_mul_lcm`):

    `deg (minpoly T) + deg (gcd a b) = deg a + deg b`,   equivalently
    `deg (minpoly T) = deg a + deg b − deg (gcd a b)`,

  where `a = minpoly (compress T H)`, `b = minpoly (compress T Hᗮ)`.  This is the
  exact (with-gcd-correction) sharpening of the degree *bracket*
  `natDegree_minpoly_compress_le_of_reducing` / `natDegree_minpoly_le_add_compress_of_reducing`
  recorded in the parent file: the ambient minpoly degree sits between the block
  maximum and the block sum, and the deficit from the sum is precisely
  `deg (gcd a b)`.

Everything is symmetry-free (no self-adjointness of `T`), matching the parent
file, and `0`-axiom / `0`-sorry.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open Polynomial UniqueFactorizationMonoid

namespace CauchyInterlacing.PoincareCompression

open CauchyInterlacing.Compression

/-! ## A general fact: the lcm of two squarefree elements is squarefree

Stated for an arbitrary normalized-GCD unique factorization monoid (which the
polynomial ring `𝕜[X]` over a field is).  The proof works entirely in the
`normalizedFactors` calculus: an `lcm` divides the product of the *union* of the
two factor multisets, so its factor multiset is `≤` that union, and a `union` of
two `Nodup` multisets is `Nodup`. -/

/-- **The lcm of two squarefree elements is squarefree.**

In a normalized-GCD unique factorization monoid, if `p` and `q` are squarefree
then so is `lcm p q`.  (Divisor-monotonicity gives the easier converse
`Squarefree (lcm p q) → Squarefree p ∧ Squarefree q`; this is the substantive
direction.)

Proof: let `s := normalizedFactors p ∪ normalizedFactors q` (multiset union, i.e.
*max* multiplicities) and `m := s.prod`.  Every element of `s` is a normalized
irreducible, so `normalizedFactors m = s`.  Both `p` and `q` divide `m`
(`normalizedFactors p ≤ s` and `normalizedFactors q ≤ s`), hence `lcm p q ∣ m`,
so `normalizedFactors (lcm p q) ≤ s`.  Squarefreeness of `p` and `q` says
`normalizedFactors p` and `normalizedFactors q` are `Nodup`, whence `s` is `Nodup`
(`nodup_union`), and any sub-multiset of a `Nodup` multiset is `Nodup`.  Therefore
`normalizedFactors (lcm p q)` is `Nodup`, i.e. `lcm p q` is squarefree. -/
theorem squarefree_lcm {α : Type*} [CancelCommMonoidWithZero α] [Nontrivial α]
    [NormalizedGCDMonoid α] [UniqueFactorizationMonoid α] {p q : α}
    (hp : Squarefree p) (hq : Squarefree q) : Squarefree (lcm p q) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := hq.ne_zero
  have hl0 : lcm p q ≠ 0 := by rw [Ne, lcm_eq_zero_iff]; push_neg; exact ⟨hp0, hq0⟩
  set s : Multiset α := normalizedFactors p ∪ normalizedFactors q with hs_def
  -- Every element of `s` is a (normalized) irreducible.
  have hirr : ∀ a ∈ s, Irreducible a := by
    intro a ha
    rw [hs_def, Multiset.mem_union] at ha
    rcases ha with h | h
    · exact irreducible_of_normalized_factor a h
    · exact irreducible_of_normalized_factor a h
  have hm0 : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => (hirr 0 h).ne_zero rfl)
  -- `normalizedFactors (s.prod) = s`, since `s` is a multiset of normalized irreducibles.
  have hnfm : normalizedFactors s.prod = s := by
    rw [normalizedFactors_prod_eq s hirr]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id s)
    intro a ha
    rw [hs_def, Multiset.mem_union] at ha
    rcases ha with h | h
    · exact (normalize_normalized_factor a h).trans (id_eq a).symm
    · exact (normalize_normalized_factor a h).trans (id_eq a).symm
  -- `p ∣ s.prod` and `q ∣ s.prod`, hence `lcm p q ∣ s.prod`.
  have hpm : p ∣ s.prod := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hp0 hm0, hnfm, hs_def]
    exact Multiset.le_union_left
  have hqm : q ∣ s.prod := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hq0 hm0, hnfm, hs_def]
    exact Multiset.le_union_right
  have hlm : lcm p q ∣ s.prod := lcm_dvd hpm hqm
  -- `s` is `Nodup` because it is a union of the `Nodup` factor multisets of `p`, `q`.
  have hnd : s.Nodup := by
    rw [hs_def]
    exact Multiset.nodup_union.mpr
      ⟨(squarefree_iff_nodup_normalizedFactors hp0).mp hp,
       (squarefree_iff_nodup_normalizedFactors hq0).mp hq⟩
  -- `normalizedFactors (lcm p q) ≤ s`, a sub-multiset of a `Nodup` multiset.
  have hle : normalizedFactors (lcm p q) ≤ s := by
    rw [← hnfm]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hl0 hm0).mp hlm
  exact (squarefree_iff_nodup_normalizedFactors hl0).mpr (Multiset.nodup_of_le hle hnd)

section Reducing

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **Diagonalizability transfer across a reducing pair.**

If `H` reduces `T` (both `H` and `Hᗮ` are `T`-invariant), then `T` has squarefree
minimal polynomial — over a field, the algebraic form of "diagonalizable /
semisimple" — **iff both orthogonal compression blocks do**:

  `Squarefree (minpoly T)
     ↔ Squarefree (minpoly (compress T H)) ∧ Squarefree (minpoly (compress T Hᗮ))`.

Immediate from the capstone `minpoly_eq_lcm_compress_of_reducing`
(`minpoly T = lcm a b`): the forward direction is divisor-monotonicity of
`Squarefree` (each block minpoly divides the lcm), the reverse is `squarefree_lcm`
(the lcm of squarefree polynomials is squarefree).  Symmetry-free. -/
theorem squarefree_minpoly_iff_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    Squarefree (minpoly 𝕜 T) ↔
      Squarefree (minpoly 𝕜 (compress T H)) ∧
        Squarefree (minpoly 𝕜 (compress T Hᗮ)) := by
  rw [minpoly_eq_lcm_compress_of_reducing H hH hHp]
  constructor
  · intro hsf
    exact ⟨hsf.squarefree_of_dvd (dvd_lcm_left _ _),
           hsf.squarefree_of_dvd (dvd_lcm_right _ _)⟩
  · rintro ⟨hp, hq⟩
    exact squarefree_lcm hp hq

/-- **Minpoly degree balance across a reducing pair (additive form).**

If `H` reduces `T`, the ambient minpoly degree plus the degree of the gcd of the
two block minpolys equals the sum of the block minpoly degrees:

  `deg (minpoly T) + deg (gcd a b) = deg a + deg b`,

where `a = minpoly (compress T H)`, `b = minpoly (compress T Hᗮ)`.  From the
capstone `minpoly T = lcm a b` and the `lcm`/`gcd` duality
`gcd a b · lcm a b ~ a · b` (`gcd_mul_lcm`): degrees add over products of nonzero
polynomials, and associated polynomials have equal degree.  Symmetry-free. -/
theorem natDegree_minpoly_add_gcd_eq_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (minpoly 𝕜 T).natDegree
        + (gcd (minpoly 𝕜 (compress T H)) (minpoly 𝕜 (compress T Hᗮ))).natDegree
      = (minpoly 𝕜 (compress T H)).natDegree
        + (minpoly 𝕜 (compress T Hᗮ)).natDegree := by
  set a := minpoly 𝕜 (compress T H) with ha_def
  set b := minpoly 𝕜 (compress T Hᗮ) with hb_def
  have haint : IsIntegral 𝕜 (compress T H) :=
    have : Algebra.IsIntegral 𝕜 (Module.End 𝕜 (↥H)) := Algebra.IsIntegral.of_finite 𝕜 _
    Algebra.IsIntegral.isIntegral (compress T H)
  have hbint : IsIntegral 𝕜 (compress T Hᗮ) :=
    have : Algebra.IsIntegral 𝕜 (Module.End 𝕜 (↥Hᗮ)) := Algebra.IsIntegral.of_finite 𝕜 _
    Algebra.IsIntegral.isIntegral (compress T Hᗮ)
  have ha0 : a ≠ 0 := (minpoly.monic haint).ne_zero
  have hb0 : b ≠ 0 := (minpoly.monic hbint).ne_zero
  have hgcd0 : gcd a b ≠ 0 := fun h => ha0 ((gcd_eq_zero_iff a b).mp h).1
  have hlcm0 : lcm a b ≠ 0 := fun h => ((lcm_eq_zero_iff a b).mp h).elim ha0 hb0
  have hassoc : Associated (gcd a b * lcm a b) (a * b) := gcd_mul_lcm a b
  have hdeg : (gcd a b * lcm a b).natDegree = (a * b).natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
  rw [natDegree_mul hgcd0 hlcm0, natDegree_mul ha0 hb0] at hdeg
  have hcap : minpoly 𝕜 T = lcm a b := minpoly_eq_lcm_compress_of_reducing H hH hHp
  rw [hcap]
  omega

/-- **Minpoly degree formula across a reducing pair (subtraction form).**

The `deg (lcm) = deg a + deg b − deg (gcd)` reading of the balance identity
`natDegree_minpoly_add_gcd_eq_of_reducing`:

  `deg (minpoly T) = deg a + deg b − deg (gcd a b)`,

with `a = minpoly (compress T H)`, `b = minpoly (compress T Hᗮ)`.  This is the
exact value of `deg (minpoly T)` inside the bracket
`max (deg a) (deg b) ≤ deg (minpoly T) ≤ deg a + deg b` of the parent file, the
deficit from the sum being precisely `deg (gcd a b)`.  Symmetry-free. -/
theorem natDegree_minpoly_eq_add_sub_gcd_of_reducing {T : V →ₗ[𝕜] V} (H : Submodule 𝕜 V)
    (hH : ∀ y ∈ H, T y ∈ H) (hHp : ∀ y ∈ Hᗮ, T y ∈ Hᗮ) :
    (minpoly 𝕜 T).natDegree
      = (minpoly 𝕜 (compress T H)).natDegree
          + (minpoly 𝕜 (compress T Hᗮ)).natDegree
        - (gcd (minpoly 𝕜 (compress T H)) (minpoly 𝕜 (compress T Hᗮ))).natDegree := by
  have h := natDegree_minpoly_add_gcd_eq_of_reducing H hH hHp
  omega

end Reducing

end CauchyInterlacing.PoincareCompression
