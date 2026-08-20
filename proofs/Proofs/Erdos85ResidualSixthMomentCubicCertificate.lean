import Proofs.Erdos85ResidualSixthMomentHankel

/-! # A strict sixth-moment certificate using the cubic moment -/

namespace Erdos85

noncomputable section

open Polynomial

/-- A degree-six sum-of-squares certificate which strengthens the basic
Hankel bound when the cubic moment is known.  The constants are chosen by
projecting `x³` onto the span of `1,x` under the h305 moment functional. -/
theorem multiset_h305_sixthMoment_cubic_certificate
    (s : Multiset ℝ) (u : ℝ)
    (hcard : s.card = 32)
    (hone : (s.map fun x => x).sum = -8)
    (htwo : (s.map fun x => x ^ 2).sum = 224)
    (hthree : (s.map fun x => x ^ 3).sum = u)
    (hfour : (s.map fun x => x ^ 4).sum = 1792) :
    24864 * (u + 64) ^ 2 ≤
      788544 * ((s.map fun x => x ^ 6).sum - 14336) := by
  let P : ℝ → ℝ := fun x =>
    888 * x ^ 3 - (u + 7168) * x - 28 * (u + 64)
  have hn : 0 ≤ (s.map fun x => P x ^ 2).sum := by
    apply Multiset.sum_nonneg
    intro z hz
    obtain ⟨x, _hx, rfl⟩ := Multiset.mem_map.mp hz
    exact sq_nonneg (P x)
  have hexpand :
      (s.map fun x => P x ^ 2).sum =
        788544 * (s.map fun x => x ^ 6).sum +
        (-1776 * u - 12730368) * (s.map fun x => x ^ 4).sum +
        (-49728 * u - 3182592) * (s.map fun x => x ^ 3).sum +
        (u ^ 2 + 14336 * u + 51380224) *
          (s.map fun x => x ^ 2).sum +
        (56 * u ^ 2 + 404992 * u + 25690112) *
          (s.map fun x => x).sum +
        (s.card : ℝ) * (784 * u ^ 2 + 100352 * u + 3211264) := by
    clear hcard hone htwo hthree hfour hn
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Nat.cast_add, Nat.cast_one]
        rw [ih]
        dsimp [P]
        ring
  rw [hexpand, hone, htwo, hthree, hfour, hcard] at hn
  norm_num at hn ⊢
  nlinarith

/-- Root-power-sum form of the cubic certificate. -/
theorem h305_realResidual_sixthMoment_cubic_certificate
    (p : ℝ[X]) (u : ℝ) (hsplit : p.Splits)
    (hdegree : p.natDegree = 32)
    (hone : realRootPowerSum p 1 = -8)
    (htwo : realRootPowerSum p 2 = 224)
    (hthree : realRootPowerSum p 3 = u)
    (hfour : realRootPowerSum p 4 = 1792) :
    24864 * (u + 64) ^ 2 ≤
      788544 * (realRootPowerSum p 6 - 14336) := by
  apply multiset_h305_sixthMoment_cubic_certificate p.roots u
  · rw [← hsplit.natDegree_eq_card_roots, hdegree]
  · simpa [realRootPowerSum] using hone
  · simpa [realRootPowerSum] using htwo
  · simpa [realRootPowerSum] using hthree
  · simpa [realRootPowerSum] using hfour

/-- The cubic moment of a graph is `6T`; after subtracting the centered-shore
moment it is `6T-224`.  This can never equal the equality value `-64`, so the
sixth-moment inequality is strict. -/
theorem h305_realResidual_sixthMoment_strict_of_triangleMoment
    (p : ℝ[X]) (T : ℤ) (hsplit : p.Splits)
    (hdegree : p.natDegree = 32)
    (hone : realRootPowerSum p 1 = -8)
    (htwo : realRootPowerSum p 2 = 224)
    (hthree : realRootPowerSum p 3 = ((6 * T - 224 : ℤ) : ℝ))
    (hfour : realRootPowerSum p 4 = 1792) :
    14336 < realRootPowerSum p 6 := by
  let u : ℝ := ((6 * T - 224 : ℤ) : ℝ)
  have hu : u + 64 ≠ 0 := by
    intro h
    dsimp [u] at h
    have hz : 6 * T - 224 + 64 = 0 := by
      exact_mod_cast h
    omega
  have hsquare : 0 < (u + 64) ^ 2 := sq_pos_of_ne_zero hu
  have hcert := h305_realResidual_sixthMoment_cubic_certificate
    p u hsplit hdegree hone htwo (by simpa [u] using hthree) hfour
  nlinarith

end


end Erdos85

#print axioms Erdos85.multiset_h305_sixthMoment_cubic_certificate
#print axioms Erdos85.h305_realResidual_sixthMoment_cubic_certificate
#print axioms Erdos85.h305_realResidual_sixthMoment_strict_of_triangleMoment
