import Proofs.Erdos85OrbitFactorExtraction

/-!
# Root-multiplicity stripping: the nonprincipal factor stays asymmetric

The characteristic polynomial of the adjacency matrix of a `d`-regular graph
is monic, has `d` as a root, and has vanishing next-to-leading coefficient
(the trace is zero).  The principal root `d` may be repeated (disconnected
graphs).  Stripping the FULL `(X - d)`-multiplicity `k` leaves a monic
cofactor `q0` with `q0(d) ≠ 0` whose next-to-leading coefficient is
`k·d ≠ 0`.  Hence `q0` is not sign-stable, and the asymmetric irreducible
factor extracted from `q0` by `Erdos85OrbitFactorExtraction` additionally
avoids the principal root `d`.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- Stripping the full `(X - d)`-multiplicity from a trace-zero monic
polynomial with nonzero root `d` leaves a monic cofactor `q0` avoiding the
root `d` whose next-to-leading coefficient is exactly `k·d`. -/
theorem Polynomial.exists_strip_rootMultiplicity (g : Polynomial ℚ) (hg : g.Monic)
    (d : ℚ) (hd : d ≠ 0) (hroot : g.eval d = 0) (htrace : g.nextCoeff = 0) :
    ∃ (k : ℕ) (q0 : Polynomial ℚ), 0 < k ∧
      g = (Polynomial.X - Polynomial.C d) ^ k * q0 ∧ q0.Monic ∧
      q0.eval d ≠ 0 ∧ q0.nextCoeff = k * d := by
  have hg0 : g ≠ 0 := hg.ne_zero
  set k := rootMultiplicity d g with hk
  have hkpos : 0 < k := (rootMultiplicity_pos hg0).mpr hroot
  set q0 := g /ₘ (X - C d) ^ k with hq0def
  have hfact : (X - C d) ^ k * q0 = g :=
    pow_mul_divByMonic_rootMultiplicity_eq g d
  have hpowmonic : ((X - C d) ^ k).Monic := (monic_X_sub_C d).pow k
  have hq0monic : q0.Monic := hpowmonic.of_mul_monic_left (by rwa [hfact])
  have hq0eval : q0.eval d ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero d hg0
  refine ⟨k, q0, hkpos, hfact.symm, hq0monic, hq0eval, ?_⟩
  have hmul : g.nextCoeff = ((X - C d) ^ k).nextCoeff + q0.nextCoeff := by
    conv_lhs => rw [← hfact]
    exact hpowmonic.nextCoeff_mul hq0monic
  rw [htrace, (monic_X_sub_C d).nextCoeff_pow, nextCoeff_X_sub_C,
    nsmul_eq_mul] at hmul
  rw [eq_neg_of_add_eq_zero_right hmul.symm, mul_neg, neg_neg]

/-- Even past a repeated principal root, the trace-zero condition forces an
asymmetric irreducible factor, and that factor avoids the principal root:
strip the full `(X - d)`-multiplicity, observe the cofactor has
next-to-leading coefficient `k·d ≠ 0` so it is not sign-stable, and extract
its asymmetric irreducible factor. -/
theorem Polynomial.exists_asymmetric_factor_avoiding_root (g : Polynomial ℚ) (hg : g.Monic)
    (d : ℚ) (hd : d ≠ 0) (hroot : g.eval d = 0) (htrace : g.nextCoeff = 0)
    (hdeg : rootMultiplicity d g < g.natDegree) :
    ∃ f : Polynomial ℚ, Irreducible f ∧ f.Monic ∧ f ∣ g ∧
      Polynomial.signedReflection f ≠ f ∧ f.eval d ≠ 0 := by
  obtain ⟨k, q0, hkpos, hfact, hq0monic, hq0eval, hnext⟩ :=
    Polynomial.exists_strip_rootMultiplicity g hg d hd hroot htrace
  have hg0 : g ≠ 0 := hg.ne_zero
  have hq0ne : q0 ≠ 0 := hq0monic.ne_zero
  -- `k` is at most the root multiplicity of `d` in `g`.
  have hkle : k ≤ rootMultiplicity d g := by
    rw [le_rootMultiplicity_iff hg0]
    exact ⟨q0, hfact⟩
  -- Degree bookkeeping: `g.natDegree = k + q0.natDegree`, so `q0` has
  -- positive degree.
  have hdegpow : ((X - C d) ^ k).natDegree = k := by
    rw [(monic_X_sub_C d).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdegs : g.natDegree = k + q0.natDegree := by
    rw [hfact, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero d)) hq0ne, hdegpow]
  have hq0deg : 0 < q0.natDegree := by omega
  -- The cofactor has nonzero next-to-leading coefficient, hence is not
  -- sign-stable.
  have hknz : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have hnextne : q0.nextCoeff ≠ 0 := by
    rw [hnext]
    exact mul_ne_zero hknz hd
  have hnot : q0.comp (-(X : Polynomial ℚ)) ≠ (-1 : ℚ) ^ q0.natDegree • q0 := by
    intro hsign
    have hz := Erdos85.Polynomial.coeff_natDegree_sub_one_eq_zero_of_signStable
      q0 hq0deg hsign
    rw [← nextCoeff_of_natDegree_pos hq0deg] at hz
    exact hnextne hz
  -- Extract the asymmetric irreducible factor of the cofactor.
  obtain ⟨f, hfirr, hfmonic, hfdvd, hfrefl⟩ :=
    Polynomial.exists_irreducible_dvd_not_reflection_fixed_of_not_signStable
      q0 hq0monic hnot
  have hq0dvd : q0 ∣ g := ⟨(X - C d) ^ k, by rw [hfact, mul_comm]⟩
  refine ⟨f, hfirr, hfmonic, hfdvd.trans hq0dvd, hfrefl, ?_⟩
  -- The factor avoids the root `d` because the cofactor does.
  intro hfeval
  obtain ⟨c, hc⟩ := hfdvd
  apply hq0eval
  rw [hc, eval_mul, hfeval, zero_mul]

end

end Erdos85
