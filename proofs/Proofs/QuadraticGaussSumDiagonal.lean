/-
  The diagonal representation of the quadratic Gauss sum.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, the quadratic Gauss sum is

      gaussSum (chiC p) ψ = ∑ x, χ(x) · ψ(x),

  where `χ = quadraticChar (ZMod p)` (the Legendre symbol).  The parent file
  `QuadraticGaussSumSquare` works with this character-weighted form, and the
  follow-up files reduce Gauss's hard sign theorem to a single positivity
  `0 < Re g` (resp. `0 < Im g`), proved by hand only for the base cases `p = 3, 5`.

  What this file contributes is the classical **diagonal representation**

      gaussSum (chiC p) ψ = ∑ k, ψ(k²)        (ψ primitive),

  i.e. the Gauss sum equals the *unweighted* sum of `ψ` over the perfect squares
  (with multiplicity).  This is the universal starting point of every classical
  proof of the sign theorem:

    * with the standard character `ψ(x) = ζ_p^x` it becomes `g = ∑ ζ_p^{k²}`,
      the form Gauss, Schur, Dirichlet and Kronecker all evaluate;
    * it immediately recovers the small-prime evaluations as plain finite sums
      `∑ ζ^{k²}` with no Legendre-symbol bookkeeping;
    * it reframes the open crux `0 < Re g` as the positivity of a sum of
      cosines `∑ cos(2π k²/p)`.

  Mathlib (v4.26.x) has the square identity `gaussSum_sq` and the square-root
  count `quadraticChar_card_sqrts`, but no diagonal/`k²` form of the Gauss sum.

  The proof is elementary fibre counting: grouping `∑ k, ψ(k²)` by the value
  `t = k²` turns the multiplicity of `t` into `#{k : k² = t} = χ(t) + 1`
  (`quadraticChar_card_sqrts`), so

      ∑ k, ψ(k²) = ∑ t, (χ(t) + 1) · ψ(t) = gaussSum (chiC p) ψ + ∑ t, ψ(t),

  and the trailing sum vanishes because `ψ` is nontrivial
  (`AddChar.sum_eq_zero_of_ne_one`).

  Sorry-free and axiom-free (ordinary `propext`/`Classical.choice`/`Quot.sound`).
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare

open scoped BigOperators
open Finset QuadraticGaussSumSquare

namespace QuadraticGaussSumDiagonal

variable {p : ℕ} [Fact p.Prime]

/-- The number of square roots of `t` in `ZMod p`, viewed in `ℂ`, equals
`chiC p t + 1`.  This is `quadraticChar_card_sqrts` transported to `ℂ` through the
ring hom `ℤ → ℂ` defining `chiC`. -/
theorem card_sqrts_cast (hp : p ≠ 2) (t : ZMod p) :
    ((univ.filter (fun x : ZMod p => x ^ 2 = t)).card : ℂ) = chiC p t + 1 := by
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp
  -- Mathlib: `#{x | x^2 = t}.toFinset = quadraticChar (ZMod p) t + 1`  (in ℤ)
  have hZ : ((univ.filter (fun x : ZMod p => x ^ 2 = t)).card : ℤ)
      = quadraticChar (ZMod p) t + 1 := by
    rw [← Set.toFinset_setOf]
    exact_mod_cast quadraticChar_card_sqrts hp2 t
  have hC : ((univ.filter (fun x : ZMod p => x ^ 2 = t)).card : ℂ)
      = ((quadraticChar (ZMod p) t : ℤ) : ℂ) + 1 := by exact_mod_cast hZ
  rw [hC, chiC, MulChar.ringHomComp_apply]
  simp

/-- **Diagonal representation of the quadratic Gauss sum.**  For an odd prime `p`
and a *primitive* additive character `ψ : ZMod p → ℂ`, the Gauss sum of the
Legendre-symbol character equals the unweighted sum of `ψ` over squares:

    gaussSum (chiC p) ψ = ∑ k, ψ(k²).

Every classical proof of Gauss's sign theorem starts here. -/
theorem gaussSum_chiC_eq_sum_sq (hp : p ≠ 2)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ = ∑ k : ZMod p, ψ (k ^ 2) := by
  have hψ1 : ψ ≠ 1 := by
    have h := hψ (a := (1 : ZMod p)) one_ne_zero
    rwa [AddChar.mulShift_one] at h
  simp only [gaussSum]
  -- goal: ∑ a, chiC p a * ψ a = ∑ k, ψ (k ^ 2)
  symm
  calc ∑ k : ZMod p, ψ (k ^ 2)
      = ∑ t : ZMod p, ∑ k ∈ univ.filter (fun k => k ^ 2 = t), ψ (k ^ 2) :=
        (Finset.sum_fiberwise_of_maps_to (fun k _ => Finset.mem_univ _) _).symm
    _ = ∑ t : ZMod p, ∑ _k ∈ univ.filter (fun k => k ^ 2 = t), ψ t := by
        refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k hk => ?_))
        rw [Finset.mem_filter] at hk
        rw [hk.2]
    _ = ∑ t : ZMod p, (univ.filter (fun k => k ^ 2 = t)).card • ψ t := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_const]
    _ = ∑ t : ZMod p, ((univ.filter (fun k => k ^ 2 = t)).card : ℂ) * ψ t := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [nsmul_eq_mul]
    _ = ∑ t : ZMod p, (chiC p t + 1) * ψ t := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [card_sqrts_cast hp t]
    _ = (∑ t : ZMod p, chiC p t * ψ t) + ∑ t : ZMod p, ψ t := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        ring
    _ = ∑ t : ZMod p, chiC p t * ψ t := by
        rw [AddChar.sum_eq_zero_of_ne_one hψ1, add_zero]

end QuadraticGaussSumDiagonal
