import Proofs.Erdos85CycleCoverPairMass
import Proofs.Erdos85ZModProjectionFiber

/-!
# Fiber counts for cyclic-cover displacements

This is the arithmetic input for the residual mixed-cycle cover blocks.
When `r ∣ n`, `p ∣ n`, and the prime `p` does not divide `r`, the multiples
of `r` in `ZMod n` are equidistributed across the mod-`p` fibers.
-/

namespace Erdos85

noncomputable section

/-- The quotient length remains divisible by `p` when `p ∣ n` but `p ∤ r`. -/
theorem prime_dvd_lengthQuotient
    {p r n : ℕ} (hp : Nat.Prime p) (hrn : r ∣ n)
    (hpn : p ∣ n) (hpr : ¬p ∣ r) :
    p ∣ n / r := by
  have hprod : p ∣ r * (n / r) := by
    rwa [Nat.mul_div_cancel' hrn]
  exact (hp.dvd_mul.mp hprod).resolve_left hpr

/-- **Residual cover-fiber count.**  Multiples of the source length `r`
inside `ZMod n` occur exactly `(n/r)/p` times in every fiber of reduction
modulo `p`, provided `p` is prime and does not divide `r`. -/
theorem card_filter_sourceLength_dvd_val
    {p r n : ℕ} [NeZero p] [NeZero r] [NeZero n]
    (hp : Nat.Prime p) (hrn : r ∣ n) (hpn : p ∣ n)
    (hpr : ¬p ∣ r) (t : ZMod p) :
    (Finset.univ.filter fun δ : ZMod n ↦
      ZMod.castHom hpn (ZMod p) δ = t ∧ r ∣ δ.val).card =
      (n / r) / p := by
  classical
  let k := n / r
  have hnk : r * k = n := by
    exact Nat.mul_div_cancel' hrn
  have hkpos : 0 < k := by
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    nlinarith
  letI : NeZero k := ⟨Nat.ne_of_gt hkpos⟩
  have hpk : p ∣ k := prime_dvd_lengthQuotient hp hrn hpn hpr
  have hunit : IsUnit ((r : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (hp.coprime_iff_not_dvd.mpr hpr).symm
  obtain ⟨ur, hur⟩ := hunit
  let q : ZMod k →+* ZMod p := ZMod.castHom hpk (ZMod p)
  let target : ZMod p := (ur⁻¹ : ZMod p) * t
  have hsourceCard :
      (Finset.univ.filter fun j : ZMod k ↦
        ((r : ℕ) : ZMod p) * q j = t).card = k / p := by
    have heq : (Finset.univ.filter fun j : ZMod k ↦
        ((r : ℕ) : ZMod p) * q j = t) = projectionFiber q target := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        projectionFiber, target, q]
      rw [← hur]
      constructor
      · intro h
        calc
          q j = (ur⁻¹ : ZMod p) * ((ur : ZMod p) * q j) := by simp
          _ = (ur⁻¹ : ZMod p) * t := by rw [h]
      · intro h
        rw [h, ← mul_assoc]
        simp
    rw [heq, card_projectionFiber_zmod_castHom hpk target]
  rw [← hsourceCard]
  symm
  apply Finset.card_bij
    (fun j _ ↦ ((r * j.val : ℕ) : ZMod n))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    constructor
    · have hjq : q j = ((j.val : ℕ) : ZMod p) := by
        calc
          q j = q ((j.val : ℕ) : ZMod k) :=
            congrArg q (ZMod.natCast_zmod_val j).symm
          _ = ((j.val : ℕ) : ZMod p) := map_natCast q j.val
      calc
        (ZMod.castHom hpn (ZMod p)) ((r * j.val : ℕ) : ZMod n) =
            ((r * j.val : ℕ) : ZMod p) := map_natCast _ _
        _ = ((r : ℕ) : ZMod p) * ((j.val : ℕ) : ZMod p) :=
          Nat.cast_mul r j.val
        _ = ((r : ℕ) : ZMod p) * q j :=
          congrArg (fun z : ZMod p ↦ ((r : ℕ) : ZMod p) * z) hjq.symm
        _ = t := hj
    · have hjlt : r * j.val < n := by
        rw [← hnk]
        exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt j)
          (Nat.pos_of_ne_zero (NeZero.ne r))
      rw [ZMod.val_cast_of_lt hjlt]
      exact dvd_mul_right r j.val
  · intro j₁ hj₁ j₂ hj₂ heq
    apply ZMod.val_injective
    have h₁lt : r * j₁.val < n := by
      rw [← hnk]
      exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt j₁)
        (Nat.pos_of_ne_zero (NeZero.ne r))
    have h₂lt : r * j₂.val < n := by
      rw [← hnk]
      exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt j₂)
        (Nat.pos_of_ne_zero (NeZero.ne r))
    have hv := congrArg ZMod.val heq
    rw [ZMod.val_cast_of_lt h₁lt, ZMod.val_cast_of_lt h₂lt] at hv
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne r)) hv
  · intro δ hδ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
    obtain ⟨hcast, hdvd⟩ := hδ
    let j : ZMod k := ((δ.val / r : ℕ) : ZMod k)
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    have hjNatLt : δ.val / r < k := by
      rw [Nat.div_lt_iff_lt_mul hrpos, mul_comm k r, hnk]
      exact ZMod.val_lt δ
    have hjval : j.val = δ.val / r := by
      exact ZMod.val_cast_of_lt hjNatLt
    have hmul : r * j.val = δ.val := by
      rw [hjval, Nat.mul_div_cancel' hdvd]
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← ZMod.natCast_zmod_val δ] at hcast
      have hjq : q j = ((j.val : ℕ) : ZMod p) := by
        calc
          q j = q ((j.val : ℕ) : ZMod k) :=
            congrArg q (ZMod.natCast_zmod_val j).symm
          _ = ((j.val : ℕ) : ZMod p) := map_natCast q j.val
      have hcast' : ((δ.val : ℕ) : ZMod p) = t := by
        simpa only [map_natCast] using hcast
      rw [hjq, ← Nat.cast_mul, hmul]
      exact hcast'
    · rw [← ZMod.natCast_zmod_val δ, ← hmul]

end

end Erdos85
