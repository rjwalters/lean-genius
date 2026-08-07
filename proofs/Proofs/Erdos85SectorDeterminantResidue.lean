import Proofs.Erdos85QuotientSectorModP
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The sector determinant residue obstruction

Taking determinants in the finite-field Moore equation
`Qₚ² ≡ (d-3)·I (mod p)` of the `p`-divisible sector quotient block gives

  `(det Qₚ)² = (d-3)^{|Sₚ|}`  in `𝔽ₚ`.

When the sector count `|Sₚ|` is **odd**, this forces `d - 3` to be a
square modulo `p`.  Contrapositively: at any prime whose residue `d - 3`
is a quadratic nonresidue, the number of `p`-divisible defect components
is necessarily **even** — the determinant obstruction that couples the
count parity demanded by the mixed parity terminal to the quadratic
character of `d - 3`, in exact alignment with the square/nonsquare
frequency dichotomy.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `p`-divisible sector quotient block over `𝔽ₚ`. -/
def sectorQuotientModP (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (p : ℕ) :
    Matrix {c : (secondOrderDefectGraph G).ConnectedComponent //
        p ∣ c.supp.ncard}
      {c : (secondOrderDefectGraph G).ConnectedComponent //
        p ∣ c.supp.ncard} (ZMod p) :=
  fun s e ↦ (componentQuotientMatrix G (secondOrderDefectGraph G)
    s.1 e.1 : ZMod p)

/-- The finite-field Moore equation for the sector block, in matrix
form. -/
theorem sectorQuotientModP_sq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) :
    sectorQuotientModP G p * sectorQuotientModP G p =
      ((d : ZMod p) - 3) •
        (1 : Matrix {c : (secondOrderDefectGraph G).ConnectedComponent //
            p ∣ c.supp.ncard}
          {c : (secondOrderDefectGraph G).ConnectedComponent //
            p ∣ c.supp.ncard} (ZMod p)) := by
  classical
  ext s e
  rw [Matrix.mul_apply]
  have hsum : ∑ c : {c : (secondOrderDefectGraph G).ConnectedComponent //
      p ∣ c.supp.ncard}, sectorQuotientModP G p s c *
        sectorQuotientModP G p c e =
      ((∑ c ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) s.1 c *
          componentQuotientMatrix G (secondOrderDefectGraph G) c e.1 :
            ℕ) : ZMod p) := by
    have hterm : ∀ c : {c : (secondOrderDefectGraph G).ConnectedComponent //
        p ∣ c.supp.ncard},
        sectorQuotientModP G p s c * sectorQuotientModP G p c e =
          ((componentQuotientMatrix G (secondOrderDefectGraph G) s.1 c.1 *
            componentQuotientMatrix G (secondOrderDefectGraph G) c.1 e.1 :
              ℕ) : ZMod p) := by
      intro c
      rw [sectorQuotientModP, sectorQuotientModP, Nat.cast_mul]
    rw [Nat.cast_sum, Finset.sum_congr rfl fun c _ ↦ hterm c]
    exact (Finset.sum_subtype
      (p := fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)
      (Finset.univ.filter fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard)
      (fun c ↦ by
        rw [Finset.mem_filter]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ c, h⟩⟩)
      (fun c ↦ ((componentQuotientMatrix G (secondOrderDefectGraph G)
          s.1 c *
        componentQuotientMatrix G (secondOrderDefectGraph G) c e.1 :
          ℕ) : ZMod p))).symm
  rw [hsum]
  have hmod := pDivisible_componentQuotient_sector_sq_modEq
    G hfree hd heven hmin hcard hp s.1 e.1 s.2 e.2
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  rw [hmod]
  have hse : (s.1 = e.1) = (s = e) := by
    apply propext
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  by_cases h : s = e
  · subst h
    simp only [if_true, mul_one, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul]
    rw [Nat.cast_sub (by omega : 3 ≤ d)]
    norm_num
  · have hne : s.1 ≠ e.1 := fun hh ↦ h (Subtype.ext hh)
    rw [if_neg hne]
    simp only [mul_zero, Nat.cast_zero, Matrix.smul_apply,
      Matrix.one_apply_ne h, smul_eq_mul, mul_zero]

/-- **The determinant residue obstruction.**  If the number of
`p`-divisible defect components is odd, then `d - 3` is a square
modulo `p`. -/
theorem isSquare_d_sub_three_of_odd_sectorCard
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hcount : Odd (Fintype.card
      {c : (secondOrderDefectGraph G).ConnectedComponent //
        p ∣ c.supp.ncard})) :
    IsSquare ((d : ZMod p) - 3) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq := sectorQuotientModP_sq G hfree hd heven hmin hcard hp
  have hdet := congrArg Matrix.det hsq
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  obtain ⟨k, hk⟩ := hcount
  set x := Matrix.det (sectorQuotientModP G p) with hx
  set a := (d : ZMod p) - 3 with ha
  by_cases ha0 : a = 0
  · exact ⟨0, by rw [ha0, mul_zero]⟩
  · have hxx : x * x = a ^ (2 * k) * a := by
      rw [hdet, hk, ← pow_succ]
    have hka : a ^ k ≠ 0 := pow_ne_zero k ha0
    refine ⟨x * (a ^ k)⁻¹, ?_⟩
    rw [show (x * (a ^ k)⁻¹) * (x * (a ^ k)⁻¹) =
      (x * x) * ((a ^ k) * (a ^ k))⁻¹ by rw [mul_inv]; ring]
    rw [hxx, show a ^ (2 * k) = a ^ k * a ^ k by rw [two_mul, pow_add],
      mul_comm (a ^ k * a ^ k) a, mul_assoc,
      mul_inv_cancel₀ (mul_ne_zero hka hka), mul_one]

end

end Erdos85
