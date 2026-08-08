import Proofs.Erdos85ReverseBlockSpectralVanishing

/-!
# The orientation-marked mixed trace formula

The mixed frequency-projector trace formula generalizes beyond odd
component lengths: mark each `p`-divisible component with an orientation.
Components whose diagonal block satisfies the *forward* translation
relation contribute their anchored zero-row Fourier weights exactly as in
the odd case; components satisfying the *reverse* relation contribute
nothing at all (`Erdos85ReverseBlockSpectralVanishing`).  The resulting
identity

`trace (M · P) = 2 Σ_{p ∣ ℓc, forward} Σ_t M⟨c,0⟩⟨c,t⟩ ζ^t`

is denominator-free and needs no parity hypothesis on any length.  The
graph-side orientation dichotomy (every even C4-free defect block is
forward- or reverse-oriented) discharges the marking hypothesis.
-/

namespace Erdos85

noncomputable section

open Matrix

variable {K : Type*} [Field K] {C : Type*} [Fintype C] [DecidableEq C]
  {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ}

/-- Trace against a circulant as a double entry sum. -/
theorem trace_mul_circulant_eq_double_sum {r : ℕ} [NeZero r]
    (B : Matrix (ZMod r) (ZMod r) K) (g : ZMod r → K) :
    Matrix.trace (B * Matrix.circulant g) =
      ∑ x : ZMod r, ∑ k : ZMod r, B x k * g (k - x) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.circulant_apply]

/-- **Oriented mixed trace against the projector.**  Only the
forward-oriented divisible components contribute, each through its own
diagonal-anchor Fourier sum; reverse-oriented components — of any
length — are spectrally invisible. -/
theorem trace_mul_mixedFreqProjector_oriented [CharZero K]
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K}
    (o : C → Prop) [DecidablePred o]
    (hfwd : ∀ c : C, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y + 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (hrevo : ∀ c : C, p ∣ ℓ c → ¬ o c → ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y - 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (hsymm : M.IsSymm) {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1) :
    Matrix.trace (M * mixedFreqProjector p ζ ℓ) =
      2 * ∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c ∧ o c,
        ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t := by
  classical
  have hentry : ∀ (c : C) (i : ZMod (ℓ c)),
      (M * mixedFreqProjector p ζ ℓ) ⟨c, i⟩ ⟨c, i⟩ =
        if p ∣ ℓ c then
          ((ℓ c : K))⁻¹ * ∑ k : ZMod (ℓ c),
            M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
        else 0 := by
    intro c i
    rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single c]
    · by_cases hdvd : p ∣ ℓ c
      · rw [if_pos hdvd, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [mixedFreqProjector, Matrix.blockDiagonal'_apply_eq,
          if_pos hdvd, Matrix.smul_apply, Matrix.circulant_apply,
          smul_eq_mul]
        ring
      · rw [if_neg hdvd]
        apply Finset.sum_eq_zero
        intro k _
        rw [mixedFreqProjector, Matrix.blockDiagonal'_apply_eq,
          if_neg hdvd]
        simp
    · intro e _ hne
      apply Finset.sum_eq_zero
      intro k _
      rw [mixedFreqProjector, Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have htrace : Matrix.trace (M * mixedFreqProjector p ζ ℓ) =
      ∑ c : C, if p ∣ ℓ c then
        ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
      else 0 := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_congr rfl fun i _ ↦ hentry c i]
    by_cases hdvd : p ∣ ℓ c
    · simp only [if_pos hdvd, ← Finset.mul_sum]
    · simp [hdvd]
  rw [htrace]
  have hζr : ∀ c : C, p ∣ ℓ c → ζ ^ (ℓ c) = 1 := by
    intro c hdvd
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, hζp, one_pow]
  have hblockFwd : ∀ c : C, p ∣ ℓ c → o c →
      ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i) =
        2 * ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t := by
    intro c hdvd hoc
    have hn0 : ((ℓ c : K)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (ℓ c))
    have hre : ∀ i : ZMod (ℓ c),
        ∑ k : ZMod (ℓ c), M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i) =
          ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * freqPairKernel ζ t := by
      intro i
      refine Fintype.sum_equiv (Equiv.subRight i) _ _ fun k ↦ ?_
      rw [Equiv.subRight_apply,
        mixed_diag_block_apply_eq_zero_row (hfwd c hdvd hoc) i k]
    rw [Finset.sum_congr rfl fun i _ ↦ hre i, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, inv_mul_cancel_left₀ hn0]
    have hcollect : ∀ t : ZMod (ℓ c),
        M ⟨c, 0⟩ ⟨c, t⟩ * freqPairKernel ζ t =
          M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t +
            M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ (-t) := by
      intro t
      rw [freqPairKernel, mul_add]
    rw [Finset.sum_congr rfl fun t _ ↦ hcollect t, Finset.sum_add_distrib]
    have heven : ∀ t : ZMod (ℓ c),
        M ⟨c, 0⟩ ⟨c, -t⟩ = M ⟨c, 0⟩ ⟨c, t⟩ := by
      intro t
      have h1 : M ⟨c, t⟩ ⟨c, 0⟩ = M ⟨c, 0⟩ ⟨c, -t⟩ := by
        rw [mixed_diag_block_apply_eq_zero_row (hfwd c hdvd hoc) t 0,
          zero_sub]
      have h2 : M ⟨c, t⟩ ⟨c, 0⟩ = M ⟨c, 0⟩ ⟨c, t⟩ :=
        hsymm.apply ⟨c, 0⟩ ⟨c, t⟩
      rw [← h1, h2]
    have hneg : ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ (-t) =
        ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t := by
      have hswap : ∑ t : ZMod (ℓ c),
          M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ (-t) =
          ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, -t⟩ * cyclePow ζ t := by
        refine Fintype.sum_equiv (Equiv.neg (ZMod (ℓ c))) _ _ fun t ↦ ?_
        rw [Equiv.neg_apply, neg_neg]
      rw [hswap]
      exact Finset.sum_congr rfl fun t _ ↦ by rw [heven t]
    rw [hneg, two_mul]
  have hblockRev : ∀ c : C, p ∣ ℓ c → ¬ o c →
      ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i) = 0 := by
    intro c hdvd hoc
    have hB := trace_mul_circulant_freqPairKernel_eq_zero_of_reverse
      (Matrix.of fun x y : ZMod (ℓ c) ↦ M ⟨c, x⟩ ⟨c, y⟩)
      (fun x y ↦ hrevo c hdvd hoc x y) (hζr c hdvd) hζsq
    rw [trace_mul_circulant_eq_double_sum] at hB
    simp only [Matrix.of_apply] at hB
    rw [hB, mul_zero]
  have hstep : ∀ c : C,
      (if p ∣ ℓ c then
        ((ℓ c : K))⁻¹ * ∑ i : ZMod (ℓ c), ∑ k : ZMod (ℓ c),
          M ⟨c, i⟩ ⟨c, k⟩ * freqPairKernel ζ (k - i)
      else 0) =
        if p ∣ ℓ c ∧ o c then
          2 * ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t
        else 0 := by
    intro c
    by_cases hdvd : p ∣ ℓ c
    · by_cases hoc : o c
      · rw [if_pos hdvd, if_pos ⟨hdvd, hoc⟩, hblockFwd c hdvd hoc]
      · rw [if_pos hdvd, if_neg (fun h ↦ hoc h.2), hblockRev c hdvd hoc]
    · rw [if_neg hdvd, if_neg (fun h ↦ hdvd h.1)]
  rw [Finset.sum_congr rfl fun c _ ↦ hstep c, ← Finset.sum_filter,
    Finset.mul_sum]

/-- **The oriented mixed frequency-pair trace identity.**  The trace of
the restricted operator on the mixed `μ = ζ + ζ⁻¹` eigenspace equals
twice the prime Fourier transform of the anchor weights of the
*forward-oriented* divisible components; reverse-oriented components of
any length are invisible.  This is the odd-length-free replacement for
`trace_defectEigenspaceRestrict_mixed`. -/
theorem trace_defectEigenspaceRestrict_mixed_oriented [CharZero K]
    {M : Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K}
    (hcomm : M * mixedDefectMatrix K ℓ = mixedDefectMatrix K ℓ * M)
    (o : C → Prop) [DecidablePred o]
    (hfwd : ∀ c : C, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y + 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (hrevo : ∀ c : C, p ∣ ℓ c → ¬ o c → ∀ x y : ZMod (ℓ c),
      M ⟨c, x + 1⟩ ⟨c, y - 1⟩ = M ⟨c, x⟩ ⟨c, y⟩)
    (hsymm : M.IsSymm)
    (hp : p.Prime) (hp2 : 2 < p) [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    LinearMap.trace K
        (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)) =
      2 * ∑ s : ZMod p,
        (∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c ∧ o c,
          ∑ t ∈ Finset.univ.filter
            (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s),
            M ⟨c, 0⟩ ⟨c, t⟩) * ζ ^ s.val := by
  classical
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  set P := mixedFreqProjector p ζ ℓ with hP
  set N := P * (M * P) with hN
  have hforall : ∀ x : (Σ c : C, ZMod (ℓ c)) → K, Matrix.toLin' N x ∈
      defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹) := by
    intro x
    rw [Matrix.toLin'_apply, hN, ← Matrix.mulVec_mulVec]
    exact mixedFreqProjector_mulVec_mem hζp _
  have hrestrict :
      (Matrix.toLin' N).restrict (fun x _ ↦ hforall x) =
        defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹) := by
    refine LinearMap.ext fun v ↦ Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, defectEigenspaceRestrict_coe,
      Matrix.toLin'_apply, hN, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec,
      mixedFreqProjector_mulVec_of_mem hp hp2 hζ v.2,
      mixedFreqProjector_mulVec_of_mem hp hp2 hζ
        (mulVec_mem_defectEigenspace hcomm v.2)]
  have htr := LinearMap.trace_restrict_eq_of_forall_mem
    (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))
    (Matrix.toLin' N) hforall (fun x _ ↦ hforall x)
  rw [hrestrict] at htr
  rw [htr, Matrix.trace_toLin'_eq, hN, hP, Matrix.trace_mul_comm,
    Matrix.mul_assoc, mixedFreqProjector_mul_self hζp hζsq,
    trace_mul_mixedFreqProjector_oriented o hfwd hrevo hsymm hζp hζsq]
  congr 1
  have hfiber : ∀ c : C, p ∣ ℓ c →
      ∑ t : ZMod (ℓ c), M ⟨c, 0⟩ ⟨c, t⟩ * cyclePow ζ t =
        ∑ s : ZMod p,
          (∑ t ∈ Finset.univ.filter
            (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s),
            M ⟨c, 0⟩ ⟨c, t⟩) * ζ ^ s.val := by
    intro c hdvd
    haveI : NeZero (ℓ c) := inferInstance
    rw [sum_mul_cyclePow_eq_fiberwise hdvd hζp
      (fun t ↦ M ⟨c, 0⟩ ⟨c, t⟩)]
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    apply Finset.sum_congr ?_ fun t _ ↦ rfl
    apply Finset.filter_congr
    intro t _
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  rw [Finset.sum_congr rfl fun c hc ↦
    hfiber c ((Finset.mem_filter.mp hc).2).1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]

end

end Erdos85
