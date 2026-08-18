import Proofs.Erdos85PositiveExcessDeterminant
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Two-adic parity interface for the defect determinant

This file begins the Smith/valuation obstruction.  Its first lemma isolates
the elementary arithmetic core after denominators have been cleared: an odd
multiple of a square has even two-adic valuation, even when presented as a
rational square with an odd denominator.
-/

namespace Erdos85

/-- Reduction modulo two detects parity of an integral determinant.  This is
the first (one invariant-factor) layer of the Smith obstruction. -/
theorem map_zmodTwo_det_eq_zero_iff_even
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℤ) :
    (B.map (Int.castRingHom (ZMod 2))).det = 0 ↔ Even B.det := by
  have hmap : (B.map (Int.castRingHom (ZMod 2))).det =
      (Int.castRingHom (ZMod 2)) B.det := by
    simpa using (RingHom.map_det (Int.castRingHom (ZMod 2)) B).symm
  rw [hmap]
  change (B.det : ZMod 2) = 0 ↔ Even B.det
  exact ZMod.intCast_eq_zero_iff_even

/-- If a nonzero integer has even two-adic valuation and is itself even, its
valuation is at least two.  Thus the determinant is divisible by four. -/
theorem four_dvd_of_even_padicValNat_two_of_even
    {b : ℕ} (hb : b ≠ 0) (hval : Even (padicValNat 2 b)) (hbeven : Even b) :
    4 ∣ b := by
  have htwo : 2 ∣ b := even_iff_two_dvd.mp hbeven
  have hone : 1 ≤ padicValNat 2 b :=
    one_le_padicValNat_of_dvd hb htwo
  obtain ⟨k, hk⟩ := hval
  have htwoVal : 2 ≤ padicValNat 2 b := by omega
  have hpow : 2 ^ 2 ∣ b :=
    (padicValNat_dvd_iff_le hb).mpr htwoVal
  norm_num at hpow ⊢
  exact hpow

/-- A singular reduction modulo two upgrades an even valuation constraint to
divisibility by four.  This is the graph-independent interface needed by the
defect-kernel program. -/
theorem four_dvd_det_natAbs_of_modTwo_singular_of_even_padicVal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℤ)
    (hdet : B.det ≠ 0)
    (hval : Even (padicValNat 2 B.det.natAbs))
    (hsing : (B.map (Int.castRingHom (ZMod 2))).det = 0) :
    4 ∣ B.det.natAbs := by
  apply four_dvd_of_even_padicValNat_two_of_even
    (Int.natAbs_ne_zero.mpr hdet) hval
  have hevenInt : Even B.det :=
    (map_zmodTwo_det_eq_zero_iff_even B).mp hsing
  exact Int.natAbs_even.mpr hevenInt

/-- If the rows indexed by `S` are entrywise even, each contributes a factor
of two to the determinant.  This is the elementary endpoint of Gaussian
elimination over `ZMod 2`: after lifting the row operations integrally, a
nullity-`k` reduction exposes `k` such rows. -/
theorem pow_card_dvd_det_natAbs_of_even_rows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (S : Finset ι)
    (hrows : ∀ i ∈ S, ∀ j, Even (M i j)) :
    2 ^ S.card ∣ M.det.natAbs := by
  classical
  let C : Matrix ι ι ℤ := fun i j =>
    if hi : i ∈ S then Classical.choose (hrows i hi j) else M i j
  let r : ι → ℤ := fun i => if i ∈ S then 2 else 1
  have hfactor : M = Matrix.diagonal r * C := by
    ext i j
    by_cases hi : i ∈ S
    · have hs := Classical.choose_spec (hrows i hi j)
      simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.diagonal, r, C, hi]
        omega
      · intro b _ hbi
        simp [Matrix.diagonal, hbi, Ne.symm hbi]
      · simp
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.diagonal, r, C, hi]
      · intro b _ hbi
        simp [Matrix.diagonal, hbi, Ne.symm hbi]
      · simp
  have hrprod : ∏ i, r i = (2 : ℤ) ^ S.card := by
    simp [r, Finset.prod_ite_mem_eq, Finset.prod_const]
  have hdet : M.det = (2 : ℤ) ^ S.card * C.det := by
    rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, hrprod]
  have hdvdInt : (2 : ℤ) ^ S.card ∣ M.det := ⟨C.det, hdet⟩
  simpa using Int.natAbs_dvd_natAbs.mpr hdvdInt

/-- Unimodular integral row operations do not change the absolute
determinant.  Hence exposing `S.card` even rows after such operations proves
the expected `2 ^ S.card` determinant divisibility. -/
theorem pow_card_dvd_det_natAbs_of_unimodular_even_rows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B U : Matrix ι ι ℤ) (S : Finset ι)
    (hU : IsUnit U.det)
    (hrows : ∀ i ∈ S, ∀ j, Even ((U * B) i j)) :
    2 ^ S.card ∣ B.det.natAbs := by
  have hdiv := pow_card_dvd_det_natAbs_of_even_rows (U * B) S hrows
  have hUabs : U.det.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hU
  simpa [Matrix.det_mul, Int.natAbs_mul, hUabs] using hdiv

/-- Two-sided version suited to Gaussian diagonal reduction: unimodular row
and column operations preserve the absolute determinant. -/
theorem pow_card_dvd_det_natAbs_of_two_sided_unimodular_even_rows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B U W : Matrix ι ι ℤ) (S : Finset ι)
    (hU : IsUnit U.det) (hW : IsUnit W.det)
    (hrows : ∀ i ∈ S, ∀ j, Even ((U * B * W) i j)) :
    2 ^ S.card ∣ B.det.natAbs := by
  have hdiv := pow_card_dvd_det_natAbs_of_even_rows (U * B * W) S hrows
  have hUabs : U.det.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hU
  have hWabs : W.det.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hW
  simpa [Matrix.det_mul, Int.natAbs_mul, hUabs, hWabs] using hdiv

/-- If `b n² = c m²` with `c,n` odd, then `v₂(b)` is even.  This is the
cleared-denominator form needed for an integer equal to an odd rational
square multiple. -/
theorem even_padicValNat_two_of_mul_sq_eq_odd_mul_sq
    {b c m n : ℕ} (hb : b ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hcOdd : Odd c) (hnOdd : Odd n)
    (h : b * n ^ 2 = c * m ^ 2) :
    Even (padicValNat 2 b) := by
  have hcNot : ¬2 ∣ c := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hcOdd) (even_iff_two_dvd.mpr htwo)
  have hnNot : ¬2 ∣ n := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hnOdd) (even_iff_two_dvd.mpr htwo)
  have hcval : padicValNat 2 c = 0 :=
    padicValNat.eq_zero_of_not_dvd hcNot
  have hnval : padicValNat 2 n = 0 :=
    padicValNat.eq_zero_of_not_dvd hnNot
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul hb (pow_ne_zero 2 hn),
    padicValNat.mul hc (pow_ne_zero 2 hm),
    padicValNat.pow, padicValNat.pow, hcval, hnval] at hv
  refine ⟨padicValNat 2 m, ?_⟩
  omega

/-- Rational-square form: an integer which is an odd integer times a
rational square has even two-adic valuation.  Working directly with
`padicValRat` avoids any denominator bookkeeping. -/
theorem even_padicValNat_two_of_eq_odd_mul_rat_sq
    {b c : ℕ} (hb : b ≠ 0) (hc : c ≠ 0) (hcOdd : Odd c)
    (q : ℚ) (hq : q ≠ 0)
    (h : (b : ℚ) = (c : ℚ) * q ^ 2) :
    Even (padicValNat 2 b) := by
  have hcNot : ¬2 ∣ c := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hcOdd) (even_iff_two_dvd.mpr htwo)
  have hcval : padicValNat 2 c = 0 :=
    padicValNat.eq_zero_of_not_dvd hcNot
  have hv := congrArg (padicValRat 2) h
  rw [padicValRat.of_nat,
    padicValRat.mul (show (c : ℚ) ≠ 0 by exact_mod_cast hc)
      (pow_ne_zero 2 hq),
    padicValRat.of_nat, padicValRat.pow, hcval] at hv
  rw [even_iff_two_dvd]
  have hdivZ : (2 : ℤ) ∣ (padicValNat 2 b : ℤ) := by
    refine ⟨padicValRat 2 q, ?_⟩
    omega
  exact_mod_cast hdivZ

/-- Integer-valued version, with positivity recovered from the positive odd
factor and the nonzero rational square. -/
theorem even_padicValNat_two_natAbs_of_int_eq_odd_mul_rat_sq
    {z : ℤ} {c : ℕ} (hcPos : 0 < c) (hcOdd : Odd c)
    (q : ℚ) (hq : q ≠ 0)
    (h : (z : ℚ) = (c : ℚ) * q ^ 2) :
    Even (padicValNat 2 z.natAbs) := by
  have hzq : 0 < (z : ℚ) := by
    rw [h]
    exact mul_pos (by positivity) (sq_pos_of_ne_zero hq)
  have hz : 0 < z := by exact_mod_cast hzq
  have habs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz.le
  have habsQ := congrArg (fun t : ℤ => (t : ℚ)) habs
  apply even_padicValNat_two_of_eq_odd_mul_rat_sq
    (Int.natAbs_ne_zero.mpr hz.ne') (by omega) hcOdd q hq
  calc
    (z.natAbs : ℚ) = (z : ℚ) := by exact habsQ
    _ = (c : ℚ) * q ^ 2 := h

/-- **Graph-facing two-adic parity.**  Whenever the principal factor
`d-e-3` is odd, the integral positive-excess defect resolvent has even
two-adic determinant valuation. -/
theorem positiveExcess_defect_resolvent_padicVal_two_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hodd : Odd (d - e - 3)) :
    let B : Matrix V V ℤ :=
      (d - 1 : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ
    Even (padicValNat 2 B.det.natAbs) := by
  dsimp only
  let Bz : Matrix V V ℤ :=
    (d - 1 : ℤ) • (1 : Matrix V V ℤ) -
      (secondOrderDefectGraph G).adjMatrix ℤ
  let Bq : Matrix V V ℚ :=
    (d - 1 : ℚ) • (1 : Matrix V V ℚ) -
      (secondOrderDefectGraph G).adjMatrix ℚ
  obtain ⟨q, hqeq⟩ := positiveExcess_defect_resolvent_is_square_mul
    G hfree hd he hreg hcard
  have hmap : Bz.map (Int.castRingHom ℚ) = Bq := by
    ext x y
    simp only [Bz, Bq, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply,
      smul_eq_mul, map_sub, map_mul, Int.coe_castRingHom]
    split_ifs <;> push_cast <;> ring
  have hcast : (Bz.det : ℚ) = Bq.det := by
    rw [Int.cast_det]
    simpa only [Int.coe_castRingHom] using congrArg Matrix.det hmap
  have hcPos : 0 < d - e - 3 := by omega
  have hdet : Bq.det ≠ 0 :=
    positiveExcess_scalar_sub_defect_det_ne_zero
      G hfree hd he hreg hcard
  have hq : q ≠ 0 := by
    intro hq0
    rw [hq0, zero_pow (by decide), mul_zero] at hqeq
    exact hdet hqeq
  apply even_padicValNat_two_natAbs_of_int_eq_odd_mul_rat_sq
    hcPos hodd q hq
  rw [hcast, hqeq]
  congr 1
  push_cast [Nat.cast_sub (by omega : e ≤ d),
    Nat.cast_sub (by omega : 3 ≤ d - e)]
  rfl

/-- **Graph-facing Smith base case.**  In the odd-principal-factor strata,
any nonzero vector in the mod-two kernel of the defect resolvent forces its
integral determinant to be divisible by four.  Thus a future computation of
this determinant modulo four immediately closes the stratum. -/
theorem positiveExcess_defect_resolvent_four_dvd_of_modTwo_singular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hodd : Odd (d - e - 3))
    (hsing :
      let B : Matrix V V ℤ :=
        (d - 1 : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ
      (B.map (Int.castRingHom (ZMod 2))).det = 0) :
    let B : Matrix V V ℤ :=
      (d - 1 : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ
    4 ∣ B.det.natAbs := by
  dsimp only at hsing ⊢
  let Bz : Matrix V V ℤ :=
    (d - 1 : ℤ) • (1 : Matrix V V ℤ) -
      (secondOrderDefectGraph G).adjMatrix ℤ
  let Bq : Matrix V V ℚ :=
    (d - 1 : ℚ) • (1 : Matrix V V ℚ) -
      (secondOrderDefectGraph G).adjMatrix ℚ
  have hmap : Bz.map (Int.castRingHom ℚ) = Bq := by
    ext x y
    simp only [Bz, Bq, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply,
      smul_eq_mul, Int.coe_castRingHom]
    split_ifs <;> push_cast <;> ring
  have hcast : (Bz.det : ℚ) = Bq.det := by
    rw [Int.cast_det]
    simpa only [Int.coe_castRingHom] using congrArg Matrix.det hmap
  have hdetZ : Bz.det ≠ 0 := by
    intro hz
    have hdetQ := positiveExcess_scalar_sub_defect_det_ne_zero
      G hfree hd he hreg hcard
    apply hdetQ
    rw [← hcast, hz]
    norm_num
  apply four_dvd_det_natAbs_of_modTwo_singular_of_even_padicVal Bz hdetZ
  · exact positiveExcess_defect_resolvent_padicVal_two_even
      G hfree hd he hreg hcard hodd
  · exact hsing

end Erdos85
