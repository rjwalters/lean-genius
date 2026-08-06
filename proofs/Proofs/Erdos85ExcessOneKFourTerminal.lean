import Proofs.Erdos85RationalPrimaryTraceSplit
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85PositiveExcessOneK4Rigidity
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85PrincipalIndicatorTrace

/-!
# The `K₄` spectral terminal at excess one

At odd excess one the service/chord pincer forces the second-order defect
graph `D` into disjoint `K₄` components, equivalently the matrix identity
`D² = 2D + 3I`.  This file runs the resulting three-sector trace system to
a contradiction for every odd degree `d ≥ 5`.

Writing `A` for the adjacency operator, the defect operator splits the
space into the eigensectors `U₀ = ker (D - 3)` and `W = ker (D + 1)`.  On
`W` the square identity `A² = (d-1)·1 + J - D` gives `A² = d`, while on
`U₀` it gives `A² = (d-4) + J`; the principal line spanned by the all-ones
vector is the unique `A`-eigenline in `U₀` at eigenvalue `d`, and on its
trace complement `A² = d-4`.

The two moment identities `tr A = 0` and `tr (AD) = n` (each `D`-edge that
is also a `G`-edge is a triangle-free matching edge, one per vertex) force

* `tr (A|_{U₀}) = n/4` and `tr (A|_W) = -n/4`.

If `d - 4` is not a square, the `U₀`-trace collapses to the principal
contribution `d`, so `n = 4d`, i.e. `(d-1)(d-4) = 0`, impossible for
`d ≥ 5`.  If `d - 4` is a square then `d` is not (their difference is
four), the `W`-trace vanishes, and `n = 0`, again impossible.  Hence no
`C₄`-free `d`-regular graph on `d(d-1) + 4` vertices exists for odd
`d ≥ 5`.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-! ## Small helpers -/

/-- Membership in the linear sector `ker (T - μ)` unpacks to the
eigenvector equation. -/
theorem apply_eq_smul_of_mem_ker_X_sub_C
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (T : E →ₗ[ℚ] E) (μ : ℚ) {v : E}
    (hv : v ∈ LinearMap.ker (Polynomial.aeval T (X - C μ))) :
    T v = μ • v := by
  rw [LinearMap.mem_ker, aeval_X_sub_C_eq] at hv
  simpa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] using hv

/-- Subsingleton-safe form of the nonsquare quadratic trace theorem. -/
theorem trace_eq_zero_of_sq_eq_nonsquare_nat'
    {F : Type*} [AddCommGroup F] [Module ℚ F] [FiniteDimensional ℚ F]
    (f : F →ₗ[ℚ] F) (c : ℕ) (hc : ¬ IsSquare c)
    (hf : f * f = (c : ℚ) • LinearMap.id) :
    LinearMap.trace ℚ F f = 0 := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · rw [Subsingleton.elim f (0 : F →ₗ[ℚ] F)]
    exact map_zero _
  · exact LinearMap.trace_eq_zero_of_sq_eq_nonsquare_nat f c hc hf

/-- On the linear sector of a commuting operator, multiplying on the left
by that operator scales the restriction by the sector eigenvalue. -/
theorem kerAevalRestrict_mul_linear
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (hcommST : (S * T) * T = T * (S * T)) (μ : ℚ) :
    kerAevalRestrict (S * T) T hcommST (X - C μ) =
      μ • kerAevalRestrict S T hcomm (X - C μ) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have hTv : T (v : E) = μ • (v : E) :=
    apply_eq_smul_of_mem_ker_X_sub_C T μ v.2
  simp only [kerAevalRestrict_coe, LinearMap.smul_apply, SetLike.val_smul,
    Module.End.mul_apply]
  rw [hTv, map_smul]

/-- Two squares cannot differ by four beyond `4 = 2² - 0²`: for `d ≥ 5`,
if `d - 4` is a square then `d` is not. -/
theorem not_isSquare_of_isSquare_sub_four {d : ℕ} (hd : 5 ≤ d)
    (h4 : IsSquare (d - 4)) : ¬ IsSquare d := by
  rintro ⟨q, hq⟩
  obtain ⟨s, hs⟩ := h4
  have hd4 : d = s * s + 4 := (Nat.sub_eq_iff_eq_add (by omega : 4 ≤ d)).mp hs
  have hq2 : s * s + 4 = q * q := by rw [← hd4, hq]
  have hq3 : 3 ≤ q := by
    by_contra hcon
    push_neg at hcon
    have h2 : q ≤ 2 := by omega
    have hle : q * q ≤ 4 := by
      calc q * q ≤ 2 * 2 := Nat.mul_le_mul h2 h2
        _ = 4 := rfl
    have hle' : d ≤ 4 := by rw [hq]; exact hle
    omega
  have hslt : s + 1 ≤ q := by
    rcases Nat.lt_or_ge s q with h | h
    · exact h
    · exfalso
      have hle : q * q ≤ s * s := Nat.mul_le_mul h h
      linarith
  have hkey : (s + 1) * (s + 1) ≤ q * q := Nat.mul_le_mul hslt hslt
  have h2s : 2 * s ≤ 3 := by nlinarith
  have hs1 : s ≤ 1 := by omega
  interval_cases s
  · norm_num at hd4
    omega
  · norm_num at hq2
    have h9 : 9 ≤ q * q := by
      calc (9 : ℕ) = 3 * 3 := rfl
        _ ≤ q * q := Nat.mul_le_mul hq3 hq3
    linarith

/-! ## The principal sector -/

/-- **Principal sector trace pin.**  Suppose `B` satisfies
`B² = (d-4)·id + J₀` with `B·J₀ = d·J₀`, the rank-one operator `J₀` has
range inside the line of a nonzero vector `e` fixed by `B` up to the
scalar `d`, and `d - 4` is not a square.  Then the trace of `B` is
exactly the principal contribution `d`: the sector `ker (B - d)` is the
line of `e`, and the complementary sector square `d - 4` kills its
trace. -/
theorem principal_sector_trace_of_nonsquare
    {F : Type*} [AddCommGroup F] [Module ℚ F] [FiniteDimensional ℚ F]
    (B JF : F →ₗ[ℚ] F) (eF : F) {d n : ℕ}
    (hd : 5 ≤ d)
    (hnq : (n : ℚ) = (d : ℚ) * (d : ℚ) - (d : ℚ) + 4)
    (hne : eF ≠ 0)
    (hBB : B * B = ((d : ℚ) - 4) • LinearMap.id + JF)
    (hBJ : B * JF = (d : ℚ) • JF)
    (hJrange : ∀ x : F, ∃ c : ℚ, JF x = c • eF)
    (hBe : B eF = (d : ℚ) • eF)
    (hns : ¬ IsSquare (d - 4)) :
    LinearMap.trace ℚ F B = (d : ℚ) := by
  classical
  have hdq : (5 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hJFeq : B * B - ((d : ℚ) - 4) • LinearMap.id = JF := by
    rw [hBB]
    abel
  have hannB : Polynomial.aeval B
      ((X - C (d : ℚ)) * (X ^ 2 - C ((d : ℚ) - 4))) = 0 := by
    rw [map_mul, aeval_X_sub_C_eq, map_sub, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Module.algebraMap_end_eq_smul_id, pow_two, hJFeq,
      sub_mul, smul_mul_assoc, one_mul, hBJ, sub_self]
  have hcop : IsCoprime (X - C (d : ℚ)) (X ^ 2 - C ((d : ℚ) - 4)) := by
    rw [(Polynomial.irreducible_X_sub_C (d : ℚ)).coprime_iff_not_dvd,
      Polynomial.dvd_iff_isRoot]
    intro hroot
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hroot
    nlinarith [sq_nonneg ((d : ℚ) - 5)]
  have hsplit := trace_eq_add_trace_restrict_ker_aeval B B rfl hcop hannB
  -- the sector `ker (B - d)` is exactly the line of `eF`
  have heP : eF ∈ LinearMap.ker (Polynomial.aeval B (X - C (d : ℚ))) := by
    rw [LinearMap.mem_ker, aeval_X_sub_C_eq]
    simp [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hBe]
  have hPle : LinearMap.ker (Polynomial.aeval B (X - C (d : ℚ))) ≤
      Submodule.span ℚ {eF} := by
    intro v hv
    have hBv : B v = (d : ℚ) • v :=
      apply_eq_smul_of_mem_ker_X_sub_C B (d : ℚ) hv
    have hJv : JF v = (n : ℚ) • v := by
      have hBBv := LinearMap.congr_fun hBB v
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hBBv
      have hB2 : B (B v) = ((d : ℚ) * (d : ℚ)) • v := by
        rw [hBv, map_smul, hBv, smul_smul]
      have h2 : ((d : ℚ) * (d : ℚ)) • v - ((d : ℚ) - 4) • v = JF v := by
        rw [← hB2, hBBv]
        abel
      have h3 : (n : ℚ) • v = ((d : ℚ) * (d : ℚ)) • v - ((d : ℚ) - 4) • v := by
        rw [hnq]
        module
      rw [h3, h2]
    obtain ⟨c, hc⟩ := hJrange v
    have hnne : (n : ℚ) ≠ 0 := by
      rw [hnq]
      nlinarith [sq_nonneg ((d : ℚ) - 5)]
    have hveq : v = ((n : ℚ)⁻¹ * c) • eF := by
      have h4 : (n : ℚ) • v = c • eF := by rw [← hJv, hc]
      calc v = (n : ℚ)⁻¹ • ((n : ℚ) • v) := by
            rw [smul_smul, inv_mul_cancel₀ hnne, one_smul]
        _ = (n : ℚ)⁻¹ • (c • eF) := by rw [h4]
        _ = ((n : ℚ)⁻¹ * c) • eF := by rw [smul_smul]
    rw [Submodule.mem_span_singleton]
    exact ⟨(n : ℚ)⁻¹ * c, hveq.symm⟩
  have hPeq : LinearMap.ker (Polynomial.aeval B (X - C (d : ℚ))) =
      Submodule.span ℚ {eF} :=
    le_antisymm hPle ((Submodule.span_singleton_le_iff_mem _ _).mpr heP)
  have hfinP : Module.finrank ℚ
      (LinearMap.ker (Polynomial.aeval B (X - C (d : ℚ)))) = 1 := by
    rw [hPeq]
    exact finrank_span_singleton hne
  have hBP : kerAevalRestrict B B rfl (X - C (d : ℚ)) =
      (d : ℚ) • LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp only [kerAevalRestrict_coe, LinearMap.smul_apply, LinearMap.id_apply,
      SetLike.val_smul]
    exact apply_eq_smul_of_mem_ker_X_sub_C B (d : ℚ) v.2
  have htrP : LinearMap.trace ℚ _
      (kerAevalRestrict B B rfl (X - C (d : ℚ))) = (d : ℚ) := by
    rw [hBP, map_smul, LinearMap.trace_id, hfinP]
    simp
  -- the complementary sector squares to the nonsquare `d - 4`
  have hc4 : ((d - 4 : ℕ) : ℚ) = (d : ℚ) - 4 :=
    Nat.cast_sub (by omega : 4 ≤ d)
  have hQsq : kerAevalRestrict B B rfl (X ^ 2 - C ((d : ℚ) - 4)) *
      kerAevalRestrict B B rfl (X ^ 2 - C ((d : ℚ) - 4)) =
      ((d - 4 : ℕ) : ℚ) • LinearMap.id := by
    rw [hc4]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hmap : Polynomial.aeval B (X ^ 2 - C ((d : ℚ) - 4)) =
        B * B - ((d : ℚ) - 4) • LinearMap.id := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Module.algebraMap_end_eq_smul_id, pow_two]
    have hv0 :=
      (LinearMap.congr_fun hmap.symm (v : F)).trans (LinearMap.mem_ker.mp v.2)
    have hv' : B (B (v : F)) = ((d : ℚ) - 4) • (v : F) := by
      have h := hv0
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Module.End.mul_apply] at h
      rw [sub_eq_zero] at h
      exact h
    simp only [Module.End.mul_apply, kerAevalRestrict_coe, LinearMap.smul_apply,
      LinearMap.id_apply, SetLike.val_smul]
    exact hv'
  have htQ0 : LinearMap.trace ℚ _
      (kerAevalRestrict B B rfl (X ^ 2 - C ((d : ℚ) - 4))) = 0 :=
    trace_eq_zero_of_sq_eq_nonsquare_nat' _ (d - 4) hns hQsq
  rw [htrP, htQ0, add_zero] at hsplit
  exact hsplit

/-! ## The abstract spectral kill -/

/-- **Abstract `K₄` spectral kill.**  A rational operator system
consisting of an adjacency operator `S` (trace zero, row sum `d`), a
commuting defect operator `T` with the `K₄` polynomial `T² = 2T + 3`,
the square identity `S² = (d-1)·1 + J - T`, a rank-one all-ones operator
`J` with `J·T = 3J`, and the mixed moment `tr (S·T) = n` is
contradictory whenever `d ≥ 5` and `n = d(d-1) + 4`. -/
theorem kfour_defect_operator_kill
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T J : E →ₗ[ℚ] E) (e : E) {d n : ℕ}
    (hd : 5 ≤ d) (hn : n = d * (d - 1) + 4)
    (hcomm : S * T = T * S)
    (hTT : T * T = (2 : ℚ) • T + (3 : ℚ) • LinearMap.id)
    (hSS : S * S = ((d : ℚ) - 1) • (1 : E →ₗ[ℚ] E) + J - T)
    (hJT : J * T = (3 : ℚ) • J)
    (he : e ≠ 0)
    (hJrange : ∀ x : E, ∃ c : ℚ, J x = c • e)
    (hSe : S e = (d : ℚ) • e)
    (hTe : T e = (3 : ℚ) • e)
    (htrS : LinearMap.trace ℚ E S = 0)
    (htrST : LinearMap.trace ℚ E (S * T) = (n : ℚ)) : False := by
  classical
  have hdq : (5 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
  have hnq : (n : ℚ) = (d : ℚ) * (d : ℚ) - (d : ℚ) + 4 := by
    rw [hn]
    push_cast [Nat.cast_sub (show 1 ≤ d by omega)]
    ring
  -- the defect operator is annihilated by `(X - 3)(X + 1)`
  have hann : Polynomial.aeval T ((X - C (3 : ℚ)) * (X - C (-1 : ℚ))) = 0 := by
    rw [map_mul, aeval_X_sub_C_eq, aeval_X_sub_C_eq]
    apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun hTT v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hv
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.zero_apply, map_sub, map_smul, hv]
    module
  have hcop1 : IsCoprime (X - C (3 : ℚ)) (X - C (-1 : ℚ)) := by
    rw [(Polynomial.irreducible_X_sub_C (3 : ℚ)).coprime_iff_not_dvd,
      Polynomial.dvd_iff_isRoot]
    norm_num [Polynomial.IsRoot.def]
  have hcommST : (S * T) * T = T * (S * T) :=
    LinearMap.ext fun v => LinearMap.congr_fun hcomm (T v)
  -- the two-sector trace system
  have hsplitS := trace_eq_add_trace_restrict_ker_aeval S T hcomm hcop1 hann
  have hsplitST :=
    trace_eq_add_trace_restrict_ker_aeval (S * T) T hcommST hcop1 hann
  rw [htrS] at hsplitS
  rw [htrST, kerAevalRestrict_mul_linear S T hcomm hcommST (3 : ℚ),
    kerAevalRestrict_mul_linear S T hcomm hcommST (-1 : ℚ),
    map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hsplitST
  by_cases hsq4 : IsSquare (d - 4)
  · -- `d - 4` square: then `d` is nonsquare and the `W`-sector trace dies
    have hdns : ¬ IsSquare d := not_isSquare_of_isSquare_sub_four hd hsq4
    have hSWsq := kerAevalRestrict_X_sub_C_sq S T J hcomm hSS hJT
      (show (-1 : ℚ) ≠ (3 : ℚ) by norm_num)
    have hval : ((d : ℚ) - 1) - (-1) = ((d : ℕ) : ℚ) := by push_cast; ring
    rw [hval] at hSWsq
    have hw0 : LinearMap.trace ℚ _
        (kerAevalRestrict S T hcomm (X - C (-1 : ℚ))) = 0 :=
      trace_eq_zero_of_sq_eq_nonsquare_nat' _ d hdns hSWsq
    have hn0 : (n : ℚ) = 0 := by linarith
    rw [hnq] at hn0
    nlinarith [sq_nonneg ((d : ℚ) - 5)]
  · -- `d - 4` nonsquare: the principal sector pins `tr (A|_{U₀}) = d`
    have heU0 : e ∈ LinearMap.ker (Polynomial.aeval T (X - C (3 : ℚ))) := by
      rw [LinearMap.mem_ker, aeval_X_sub_C_eq]
      simp [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hTe]
    have hJmem : ∀ x : E,
        J x ∈ LinearMap.ker (Polynomial.aeval T (X - C (3 : ℚ))) := by
      intro x
      obtain ⟨c, hc⟩ := hJrange x
      rw [hc]
      exact Submodule.smul_mem _ c heU0
    have hBB : kerAevalRestrict S T hcomm (X - C (3 : ℚ)) *
        kerAevalRestrict S T hcomm (X - C (3 : ℚ)) =
        ((d : ℚ) - 4) • LinearMap.id +
          J.restrict (fun x _ => hJmem x) := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have hTv : T (v : E) = (3 : ℚ) • (v : E) :=
        apply_eq_smul_of_mem_ker_X_sub_C T 3 v.2
      have hSSv := LinearMap.congr_fun hSS (v : E)
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply] at hSSv
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, kerAevalRestrict_coe, Submodule.coe_add,
        SetLike.val_smul, LinearMap.restrict_apply]
      rw [hSSv, hTv]
      module
    have hBJ : kerAevalRestrict S T hcomm (X - C (3 : ℚ)) *
        J.restrict (fun x _ => hJmem x) =
        (d : ℚ) • J.restrict (fun x _ => hJmem x) := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      obtain ⟨c, hc⟩ := hJrange (v : E)
      simp only [Module.End.mul_apply, LinearMap.smul_apply, kerAevalRestrict_coe,
        SetLike.val_smul, LinearMap.restrict_apply]
      rw [hc, map_smul, hSe, smul_smul, smul_smul, mul_comm]
    have hJrangeF : ∀ x : LinearMap.ker (Polynomial.aeval T (X - C (3 : ℚ))),
        ∃ c : ℚ, J.restrict (fun x _ => hJmem x) x =
          c • (⟨e, heU0⟩ : LinearMap.ker (Polynomial.aeval T (X - C (3 : ℚ)))) := by
      intro x
      obtain ⟨c, hc⟩ := hJrange (x : E)
      refine ⟨c, Subtype.ext ?_⟩
      simpa [LinearMap.restrict_apply, SetLike.val_smul] using hc
    have hBe : kerAevalRestrict S T hcomm (X - C (3 : ℚ)) ⟨e, heU0⟩ =
        (d : ℚ) • (⟨e, heU0⟩ :
          LinearMap.ker (Polynomial.aeval T (X - C (3 : ℚ)))) := by
      apply Subtype.ext
      simpa [kerAevalRestrict_coe, SetLike.val_smul] using hSe
    have hne : (⟨e, heU0⟩ :
        LinearMap.ker (Polynomial.aeval T (X - C (3 : ℚ)))) ≠ 0 := by
      intro h
      exact he (congrArg Subtype.val h)
    have htrB := principal_sector_trace_of_nonsquare
      (kerAevalRestrict S T hcomm (X - C (3 : ℚ)))
      (J.restrict (fun x _ => hJmem x)) ⟨e, heU0⟩ hd hnq hne hBB hBJ
      hJrangeF hBe hsq4
    have hnd : (n : ℚ) = 4 * (d : ℚ) := by linarith
    rw [hnq] at hnd
    nlinarith [sq_nonneg ((d : ℚ) - 5)]

/-! ## The graph-facing terminal -/

open SimpleGraph

/-- **Excess-one `K₄` spectral terminal.**  There is no `C₄`-free
`d`-regular graph on `d(d-1) + 4` vertices for odd `d ≥ 5`: the pincer
`K₄` polynomial of the second-order defect operator feeds the abstract
spectral kill. -/
theorem excessOne_KFour_defect_spectral_kill
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 5 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) : False := by
  classical
  have hd4 : 4 ≤ d := by omega
  have hcard' : Fintype.card V = d * (d - 1) + 3 + 1 := by omega
  have hregD : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
    intro x
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) hcard' x
  -- integer-level identities
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hDDZ : (secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ =
      (2 : ℤ) • (secondOrderDefectGraph G).adjMatrix ℤ +
        (3 : ℤ) • (1 : Matrix V V ℤ) :=
    secondOrderDefect_adjMatrix_sq_eq_two_mul_add_three_of_odd_excessOne
      G hfree hd4 hodd hreg hcard
  have hJDZ := onesMatrix_mul_adjMatrix_of_regular
    (secondOrderDefectGraph G) 3 hregD
  -- rational transports
  have hsqQ : G.adjMatrix ℚ * G.adjMatrix ℚ =
      ((d : ℚ) - 1) • (1 : Matrix V V ℚ) +
        Matrix.of (fun _ _ => (1 : ℚ)) -
          (secondOrderDefectGraph G).adjMatrix ℚ := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsqZ
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply, FriendshipTheoremOQ01.onesMatrix]
      using hc
  have hDDQ : (secondOrderDefectGraph G).adjMatrix ℚ *
      (secondOrderDefectGraph G).adjMatrix ℚ =
      (2 : ℚ) • (secondOrderDefectGraph G).adjMatrix ℚ +
        (3 : ℚ) • (1 : Matrix V V ℚ) := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hDDZ
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply] using hc
  have hJDQ : (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ) *
      (secondOrderDefectGraph G).adjMatrix ℚ =
      (3 : ℚ) • (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ) := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hJDZ
    simp only [Matrix.mul_apply, Matrix.smul_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
    push_cast at hc
    simpa [SimpleGraph.adjMatrix_apply, FriendshipTheoremOQ01.onesMatrix]
      using hc
  -- moment identities
  have hTFdeg : ∀ x : V, (triangleFreeEdgeGraph G).degree x = 1 :=
    triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
      G hfree hd4 hodd hreg hcard
  have htrADZ : Matrix.trace (G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) = (Fintype.card V : ℤ) := by
    rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees]
    simp [hTFdeg]
  have htrADQ : Matrix.trace (G.adjMatrix ℚ *
      (secondOrderDefectGraph G).adjMatrix ℚ) = (Fintype.card V : ℚ) := by
    have hcast : Matrix.trace (G.adjMatrix ℚ *
        (secondOrderDefectGraph G).adjMatrix ℚ) =
        ((Matrix.trace (G.adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ) : ℤ) : ℚ) := by
      rw [Matrix.trace, Matrix.trace]
      push_cast
      apply Finset.sum_congr rfl
      intro x _
      simp only [Matrix.diag_apply, Matrix.mul_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro z _
      by_cases hxz : G.Adj x z <;>
        by_cases hzx : (secondOrderDefectGraph G).Adj z x <;>
          simp [SimpleGraph.adjMatrix_apply, hxz, hzx]
    rw [hcast, htrADZ]
    norm_cast
  -- endomorphism-level data
  have hmulE : ∀ M N : Matrix V V ℚ,
      Matrix.toLin' M * Matrix.toLin' N = Matrix.toLin' (M * N) := fun M N => by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul]
  have hcommE : Matrix.toLin' (G.adjMatrix ℚ) *
      Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) =
      Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) *
        Matrix.toLin' (G.adjMatrix ℚ) := by
    rw [hmulE, hmulE, adjMatrix_comm_secondOrderDefect_of_regular_rat
      G hfree hreg]
  have hTTE : Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) *
      Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) =
      (2 : ℚ) • Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) +
        (3 : ℚ) • LinearMap.id := by
    rw [hmulE, hDDQ, map_add, map_smul, map_smul, Matrix.toLin'_one]
  have hSSE : Matrix.toLin' (G.adjMatrix ℚ) * Matrix.toLin' (G.adjMatrix ℚ) =
      ((d : ℚ) - 1) • (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) +
        Matrix.toLin' (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ) -
          Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) := by
    rw [hmulE, hsqQ, map_sub, map_add, map_smul, Matrix.toLin'_one,
      Module.End.one_eq_id]
  have hJTE : Matrix.toLin' (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ) *
      Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) =
      (3 : ℚ) • Matrix.toLin' (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ) := by
    rw [hmulE, hJDQ, map_smul]
  have hVne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    positivity
  have he : (fun _ => (1 : ℚ)) ≠ (0 : V → ℚ) := by
    obtain ⟨x⟩ := hVne
    intro h
    exact one_ne_zero (congrFun h x)
  have hJrange : ∀ x : V → ℚ, ∃ c : ℚ,
      Matrix.toLin' (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ) x =
        c • (fun _ => (1 : ℚ)) := by
    intro x
    refine ⟨∑ y : V, x y, ?_⟩
    ext v
    rw [Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct]
  have hSe : Matrix.toLin' (G.adjMatrix ℚ) (fun _ => (1 : ℚ)) =
      (d : ℚ) • (fun _ => (1 : ℚ)) := by
    ext x
    rw [Matrix.toLin'_apply, SimpleGraph.adjMatrix_mulVec_apply]
    simp [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hreg x]
  have hTe : Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)
      (fun _ => (1 : ℚ)) = (3 : ℚ) • (fun _ => (1 : ℚ)) := by
    ext x
    rw [Matrix.toLin'_apply, SimpleGraph.adjMatrix_mulVec_apply]
    simp [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hregD x]
  have htrSE : LinearMap.trace ℚ (V → ℚ) (Matrix.toLin' (G.adjMatrix ℚ)) = 0 := by
    rw [trace_toLin'_eq_matrix_trace]
    exact SimpleGraph.trace_adjMatrix (α := ℚ) G
  have htrSTE : LinearMap.trace ℚ (V → ℚ)
      (Matrix.toLin' (G.adjMatrix ℚ) *
        Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) =
      ((Fintype.card V : ℕ) : ℚ) := by
    rw [hmulE, trace_toLin'_eq_matrix_trace, htrADQ]
  exact kfour_defect_operator_kill
    (Matrix.toLin' (G.adjMatrix ℚ))
    (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
    (Matrix.toLin' (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix V V ℚ))
    (fun _ => (1 : ℚ)) hd hcard hcommE hTTE hSSE hJTE he hJrange hSe hTe
    htrSE htrSTE

end

end Erdos85
