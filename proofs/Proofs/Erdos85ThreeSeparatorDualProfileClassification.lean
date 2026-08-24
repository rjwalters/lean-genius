import Proofs.Erdos85ThreeSeparatorResidueFrontier

/-!
# The dual three-separator profile

This isolates the integer rigidity behind profile (B2) in the
three-separator analysis.  The quadratic excess `t(t+1)` is a nonnegative
even integer.  If its total is two, exactly one coordinate has nonzero
excess: it is either `1` or `-2`; every other coordinate is `0` or `-1`.
-/

namespace Erdos85

private theorem sum_eq_neg_card_filter_of_zero_or_neg_one
    {V : Type*} [DecidableEq V] (S : Finset V) (t : V → ℤ)
    (h : ∀ v ∈ S, t v = 0 ∨ t v = -1) :
    ∑ v ∈ S, t v = -(((S.filter fun v => t v = -1).card : ℕ) : ℤ) := by
  calc
    ∑ v ∈ S, t v = ∑ v ∈ S, if t v = -1 then (-1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rcases h v hv with hv0 | hv1
      · simp [hv0]
      · simp [hv1]
    _ = -(((S.filter fun v => t v = -1).card : ℕ) : ℤ) := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
        nsmul_eq_mul, add_zero]
      ring

/-- If an integral profile has total consecutive-product excess two, then it
has exactly one exceptional coordinate.  This is the arithmetic core of the
two B2 profiles; the separate linear sum determines the size of the `-1`
level set. -/
theorem exists_unique_exceptional_of_sum_mul_succ_eq_two
    {V : Type*} [DecidableEq V] (S : Finset V) (t : V → ℤ)
    (hexcess : ∑ v ∈ S, t v * (t v + 1) = 2) :
    ∃ c ∈ S,
      (t c = 1 ∨ t c = -2) ∧
      ∀ v ∈ S, v ≠ c → t v = 0 ∨ t v = -1 := by
  let f : V → ℤ := fun v => t v * (t v + 1)
  have hf_nonneg (v : V) : 0 ≤ f v := by
    dsimp [f]
    by_cases h : 0 ≤ t v
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hf_cases (v : V) (hv : v ∈ S) : f v = 0 ∨ f v = 2 := by
    have hle : f v ≤ ∑ w ∈ S, f w := by
      exact Finset.single_le_sum (fun w hw => hf_nonneg w) hv
    have hsum : ∑ w ∈ S, f w = 2 := by simpa [f] using hexcess
    have heven : 2 ∣ f v := by
      exact Int.two_dvd_mul_add_one (t v)
    obtain ⟨k, hk⟩ := heven
    have hn := hf_nonneg v
    omega
  have hc : ∃ c ∈ S, f c = 2 := by
    by_contra h
    push_neg at h
    have hz : ∀ v ∈ S, f v = 0 := by
      intro v hv
      rcases hf_cases v hv with hv0 | hv2
      · exact hv0
      · exact False.elim (h v hv hv2)
    have : ∑ v ∈ S, f v = 0 := by
      exact Finset.sum_eq_zero fun v hv => hz v hv
    have hsum : ∑ v ∈ S, f v = 2 := by simpa [f] using hexcess
    omega
  obtain ⟨c, hcS, hfc⟩ := hc
  refine ⟨c, hcS, ?_, ?_⟩
  · dsimp [f] at hfc
    have hfactor : (t c - 1) * (t c + 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · left; omega
    · right; omega
  · intro v hvS hvc
    have hsum : ∑ w ∈ S, f w = 2 := by simpa [f] using hexcess
    have herase_nonneg : 0 ≤ ∑ w ∈ S.erase c, f w := by
      exact Finset.sum_nonneg fun w _ => hf_nonneg w
    have herase_zero : ∑ w ∈ S.erase c, f w = 0 := by
      rw [← Finset.sum_erase_add _ _ hcS] at hsum
      omega
    have hfv0 : f v = 0 := by
      have hvErase : v ∈ S.erase c := Finset.mem_erase.mpr ⟨hvc, hvS⟩
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun w _ => hf_nonneg w)).mp herase_zero
      exact hall v hvErase
    dsimp [f] at hfv0
    rcases mul_eq_zero.mp hfv0 with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

/-- Adding the linear moment to the excess-two classification gives the two
exact B2 histogram sizes.  In the `-2` case, adjoining the exceptional point
to the `-1` level set produces the `(q-1)`-set in the negative-spike profile;
in the `1` case the `-1` level set itself has size `q+1`. -/
theorem dual_profile_histogram_cases
    {V : Type*} [DecidableEq V] (S : Finset V) (t : V → ℤ) (q : ℤ)
    (hlinear : ∑ v ∈ S, t v = -q)
    (hexcess : ∑ v ∈ S, t v * (t v + 1) = 2) :
    ∃ c ∈ S,
      (t c = -2 ∧
          (((S.erase c).filter fun v => t v = -1).card : ℤ) = q - 2) ∨
      (t c = 1 ∧
          (((S.erase c).filter fun v => t v = -1).card : ℤ) = q + 1) := by
  obtain ⟨c, hcS, hc, hrest⟩ :=
    exists_unique_exceptional_of_sum_mul_succ_eq_two S t hexcess
  have hrest' : ∀ v ∈ S.erase c, t v = 0 ∨ t v = -1 := by
    intro v hv
    exact hrest v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)
  have hsumErase := sum_eq_neg_card_filter_of_zero_or_neg_one (S.erase c) t hrest'
  have hsplit : (∑ v ∈ S.erase c, t v) + t c = -q := by
    rw [Finset.sum_erase_add _ _ hcS]
    exact hlinear
  rcases hc with hc1 | hc2
  · refine ⟨c, hcS, Or.inr ⟨hc1, ?_⟩⟩
    omega
  · refine ⟨c, hcS, Or.inl ⟨hc2, ?_⟩⟩
    omega

#print axioms exists_unique_exceptional_of_sum_mul_succ_eq_two
#print axioms dual_profile_histogram_cases

end Erdos85
