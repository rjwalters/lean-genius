import Proofs.Erdos85MixedAnchorBlockExact
import Proofs.Erdos85CoverFiberCount
import Proofs.Erdos85MixedAdmissibleFiberParity

/-!
# Admissible fiber parity for residual cyclic covers
-/

namespace Erdos85

noncomputable section

/-- Multiples of `r` in `ZMod n` are parametrized by `ZMod (n / r)`. -/
theorem card_filter_sourceLength_dvd_val_all
    {r n : ℕ} [NeZero r] [NeZero n] (hrn : r ∣ n) :
    (Finset.univ.filter fun δ : ZMod n ↦ r ∣ δ.val).card = n / r := by
  classical
  let k := n / r
  have hnk : r * k = n := Nat.mul_div_cancel' hrn
  have hkpos : 0 < k := by
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    nlinarith
  letI : NeZero k := ⟨Nat.ne_of_gt hkpos⟩
  change (Finset.univ.filter fun δ : ZMod n ↦ r ∣ δ.val).card = k
  rw [← ZMod.card k]
  symm
  apply Finset.card_bij (fun j _ ↦ ((r * j.val : ℕ) : ZMod n))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hjlt : r * j.val < n := by
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
    let j : ZMod k := ((δ.val / r : ℕ) : ZMod k)
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    have hjNatLt : δ.val / r < k := by
      rw [Nat.div_lt_iff_lt_mul hrpos, mul_comm k r, hnk]
      exact ZMod.val_lt δ
    have hjval : j.val = δ.val / r := ZMod.val_cast_of_lt hjNatLt
    have hmul : r * j.val = δ.val := by
      rw [hjval, Nat.mul_div_cancel' hδ]
    refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [← ZMod.natCast_zmod_val δ, ← hmul]

/-- If both cycle lengths are odd, the nonzero multiples of the source
length in the target cycle form an even set. -/
theorem even_admissible_sourceLength_dvd
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr3 : 3 ≤ r) (hrn : r ∣ n) (hrOdd : Odd r) (hnOdd : Odd n) :
    Even ((admissibleDifferences n).filter (fun δ ↦ r ∣ δ.val)).card := by
  have hfull : Finset.univ.filter (fun δ : ZMod n ↦ r ∣ δ.val) =
      insert 0 ((admissibleDifferences n).filter (fun δ ↦ r ∣ δ.val)) := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hdvd
      by_cases h0 : δ = 0
      · exact Or.inl h0
      · have hzero := castHom_eq_zero_of_sourceLength_dvd_val
          (p := r) (r := r) (n := n) (dvd_refl r) hrn δ hdvd
        have hr1 : (1 : ZMod r) ≠ 0 := by
          intro h
          have := ZMod.one_eq_zero_iff.mp h
          omega
        have h1 : δ ≠ 1 := by
          intro h
          rw [h, map_one] at hzero
          exact hr1 hzero
        have hm1 : δ ≠ -1 := by
          intro h
          rw [h, map_neg, map_one] at hzero
          exact (neg_ne_zero.mpr hr1) hzero
        exact Or.inr ⟨(mem_admissibleDifferences_iff δ).mpr
          ⟨h0, h1, hm1⟩, hdvd⟩
    · rintro (rfl | ⟨hadm, hdvd⟩)
      · simp
      · exact hdvd
  have hzeroNot : (0 : ZMod n) ∉
      (admissibleDifferences n).filter (fun δ ↦ r ∣ δ.val) := by
    simp [mem_admissibleDifferences_iff]
  have hcard := congrArg Finset.card hfull
  rw [Finset.card_insert_of_notMem hzeroNot,
    card_filter_sourceLength_dvd_val_all hrn] at hcard
  have hqOdd := odd_div_of_odd_of_dvd hnOdd hrOdd hrn
  obtain ⟨k, hk⟩ := hqOdd
  exact ⟨k, by omega⟩

/-- A displacement selected by source-length divisibility cannot equal
`±1` when the source length is at least three. -/
theorem sourceLength_dvd_val_ne_one_negOne
    {r n : ℕ} [NeZero r] [NeZero n] (hr3 : 3 ≤ r) (hrn : r ∣ n)
    (δ : ZMod n) (hδ : r ∣ δ.val) : δ ≠ 1 ∧ δ ≠ -1 := by
  have hzero := castHom_eq_zero_of_sourceLength_dvd_val
    (p := r) (r := r) (n := n) (dvd_refl r) hrn δ hδ
  have hr1 : (1 : ZMod r) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  constructor
  · intro h
    rw [h, map_one] at hzero
    exact hr1 hzero
  · intro h
    rw [h, map_neg, map_one] at hzero
    exact (neg_ne_zero.mpr hr1) hzero

/-- In a nonzero mod-`p` fiber, imposing admissibility removes no multiple
of the source length. -/
theorem filter_admissible_sourceLength_dvd_eq_full_of_ne_zero
    {p r n : ℕ} [NeZero p] [NeZero r] [NeZero n]
    (hr3 : 3 ≤ r) (hrn : r ∣ n) (hpn : p ∣ n)
    (t : ZMod p) (ht : t ≠ 0) :
    (admissibleDifferences n).filter (fun δ ↦
      ZMod.castHom hpn (ZMod p) δ = t ∧ r ∣ δ.val) =
    Finset.univ.filter (fun δ : ZMod n ↦
      ZMod.castHom hpn (ZMod p) δ = t ∧ r ∣ δ.val) := by
  ext δ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro h
    rcases h with ⟨hcast, hdvd⟩
    have hpair : ZMod.castHom hpn (ZMod p) δ = t ∧ r ∣ δ.val :=
      ⟨hcast, hdvd⟩
    refine ⟨(mem_admissibleDifferences_iff δ).mpr ⟨?_, ?_, ?_⟩, hpair⟩
    · intro h0
      subst δ
      exact ht (by simpa using hcast.symm)
    · exact (sourceLength_dvd_val_ne_one_negOne hr3 hrn δ hdvd).1
    · exact (sourceLength_dvd_val_ne_one_negOne hr3 hrn δ hdvd).2

/-- In the zero fiber, the full multiple set is obtained from the admissible
set by inserting the single excluded displacement `0`. -/
theorem full_zeroFiber_eq_insert_zero_admissible
    {p r n : ℕ} [NeZero p] [NeZero r] [NeZero n]
    (hr3 : 3 ≤ r) (hrn : r ∣ n) (hpn : p ∣ n) :
    Finset.univ.filter (fun δ : ZMod n ↦
      ZMod.castHom hpn (ZMod p) δ = 0 ∧ r ∣ δ.val) =
    insert 0 ((admissibleDifferences n).filter (fun δ ↦
      ZMod.castHom hpn (ZMod p) δ = 0 ∧ r ∣ δ.val)) := by
  ext δ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · intro h
    rcases h with ⟨hcast, hdvd⟩
    have hpair : ZMod.castHom hpn (ZMod p) δ = 0 ∧ r ∣ δ.val :=
      ⟨hcast, hdvd⟩
    by_cases h0 : δ = 0
    · exact Or.inl h0
    · exact Or.inr ⟨(mem_admissibleDifferences_iff δ).mpr
        ⟨h0, (sourceLength_dvd_val_ne_one_negOne hr3 hrn δ hdvd).1,
          (sourceLength_dvd_val_ne_one_negOne hr3 hrn δ hdvd).2⟩, hpair⟩
  · rintro (rfl | ⟨hadm, hcast, hdvd⟩)
    · simp
    · exact ⟨hcast, hdvd⟩

/-- Residual cover fibers have the required parity: odd away from zero and
even at zero. -/
theorem residual_cover_admissibleFiber_parity
    {p r n : ℕ} [NeZero p] [NeZero r] [NeZero n]
    (hp : Nat.Prime p) (hr3 : 3 ≤ r) (hrn : r ∣ n)
    (hpn : p ∣ n) (hpr : ¬p ∣ r) (hnOdd : Odd n) (t : ZMod p) :
    (t ≠ 0 → Odd ((admissibleDifferences n).filter (fun δ ↦
      ZMod.castHom hpn (ZMod p) δ = t ∧ r ∣ δ.val)).card) ∧
    (t = 0 → Even ((admissibleDifferences n).filter (fun δ ↦
      ZMod.castHom hpn (ZMod p) δ = t ∧ r ∣ δ.val)).card) := by
  have hqOdd : Odd ((n / r) / p) := by
    have hrOdd : Odd r := by
      have hprod : Odd (r * (n / r)) := by
        rw [Nat.mul_div_cancel' hrn]
        exact hnOdd
      exact (Nat.odd_mul.mp hprod).1
    have hnrOdd := odd_div_of_odd_of_dvd hnOdd hrOdd hrn
    exact odd_div_of_odd_of_dvd hnrOdd
      (hp.odd_of_ne_two (by
        intro h
        subst p
        exact (Nat.not_even_iff_odd.mpr hnOdd) ⟨n / 2, by omega⟩))
      (prime_dvd_lengthQuotient hp hrn hpn hpr)
  constructor
  · intro ht
    rw [filter_admissible_sourceLength_dvd_eq_full_of_ne_zero
      hr3 hrn hpn t ht,
      card_filter_sourceLength_dvd_val hp hrn hpn hpr t]
    exact hqOdd
  · intro ht
    subst t
    have hfull := full_zeroFiber_eq_insert_zero_admissible hr3 hrn hpn
    have hzeroNot : (0 : ZMod n) ∉
        (admissibleDifferences n).filter (fun δ ↦
          ZMod.castHom hpn (ZMod p) δ = 0 ∧ r ∣ δ.val) := by
      simp [mem_admissibleDifferences_iff]
    have hcard := congrArg Finset.card hfull
    rw [Finset.card_insert_of_notMem hzeroNot,
      card_filter_sourceLength_dvd_val hp hrn hpn hpr 0] at hcard
    obtain ⟨k, hk⟩ := hqOdd
    refine ⟨k, by omega⟩

end

end Erdos85
