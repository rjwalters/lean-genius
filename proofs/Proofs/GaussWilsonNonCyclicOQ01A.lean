import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# Gauss–Wilson Non-Cyclic OQ-01 — Phase A: Product Reduces to 2-Torsion

This file delivers **Phase A** of the three-phase decomposition of
`gauss-wilson-non-cyclic-oq-01`, in isolation from the parent
`GaussWilsonNonCyclic.lean`.

**Main theorem.** In any finite commutative group `G`, the product over
`Finset.univ` equals the product over the 2-torsion subset
`{x : G | x ^ 2 = 1}`:

  ∏ x : G, x = ∏ x ∈ univ.filter (·^2 = 1), x

**Proof.** Split `univ` into 2-torsion and non-2-torsion; the latter
product is 1 via `Finset.prod_involution` with involution `x ↦ x⁻¹`.

A copy of this lemma already exists in `WilsonsTheoremOQ04OQ02.lean`
under the name `prod_eq_prod_involutions`; we re-state it here in the
OQ-01 namespace so the S3 (Phase B + Phase C) workflow can depend on
it without pulling in the entire Wilson development.
-/

namespace GaussWilsonNonCyclicOQ01

open Finset

/-- For any finite commutative group, the product of all elements equals
    the product of the 2-torsion subset `{x : G | x^2 = 1}`.

    Proof: pair each non-self-inverse element with its inverse via
    `Finset.prod_involution`. The pairing is fixed-point-free outside
    the 2-torsion, so the non-2-torsion product collapses to `1`. -/
theorem prod_univ_eq_prod_two_torsion (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ (univ : Finset G).filter (fun x => x ^ 2 = 1), x := by
  -- Split univ = (2-torsion) ⊎ (non-2-torsion)
  have hsplit : ∏ x : G, x =
      (∏ x ∈ univ.filter (fun x : G => x ^ 2 = 1), x) *
      (∏ x ∈ univ.filter (fun x : G => ¬x ^ 2 = 1), x) :=
    (prod_filter_mul_prod_filter_not univ (fun x : G => x ^ 2 = 1) id).symm
  -- Non-2-torsion product collapses to 1 via the inverse involution
  have hrest : ∏ x ∈ univ.filter (fun x : G => ¬x ^ 2 = 1), x = 1 := by
    apply Finset.prod_involution (fun x _ => x⁻¹)
    · -- pairing: x * x⁻¹ = 1
      intros a _; exact mul_inv_cancel a
    · -- fixed-point-free: x = x⁻¹ would force x^2 = 1
      intro a ha _
      simp only [mem_filter, mem_univ, true_and] at ha
      intro heq
      exact ha (by
        have h := mul_inv_cancel a
        rw [heq] at h
        rwa [← sq] at h)
    · -- involution: (x⁻¹)⁻¹ = x
      intros a _; exact inv_inv a
    · -- closure: x⁻¹ also has (x⁻¹)^2 ≠ 1 when x^2 ≠ 1
      intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      simp only [mem_filter, mem_univ, true_and]
      rwa [inv_pow, inv_eq_one]
  rw [hsplit, hrest, mul_one]

end GaussWilsonNonCyclicOQ01
