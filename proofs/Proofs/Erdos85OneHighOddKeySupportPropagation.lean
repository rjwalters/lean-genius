import Proofs.Erdos85OneHighMissParityPropagation
import Proofs.Erdos85OneHighExchangedPairParity

/-! # Propagation in the odd exchanged-key support

Even label incidence forces every odd-multiplicity exchanged key to continue
through each of its endpoints along a different odd-multiplicity key.
-/

namespace Erdos85

noncomputable section

/-- At an endpoint of an odd exchanged key, even total weighted incidence
supplies a distinct incident key of odd multiplicity. -/
theorem exists_other_odd_exchangedKey_at_endpoint
    {L : Type*} [Fintype L] [LinearOrder L]
    (m : L × L → Nat) {k : L × L} {l : L}
    (hk : k ∈ exchangedMissPairKeys L)
    (hkl : unorderedKeyIncidence k l = 1)
    (hkodd : Odd (m k))
    (heven : Even
      (∑ q ∈ exchangedMissPairKeys L,
        unorderedKeyIncidence q l * m q)) :
    ∃ q ∈ exchangedMissPairKeys L, q ≠ k ∧
      unorderedKeyIncidence q l = 1 ∧ Odd (m q) := by
  let f : L × L → Nat := fun q => unorderedKeyIncidence q l * m q
  have hkf : Odd (f k) := by
    simpa [f, hkl] using hkodd
  obtain ⟨q, hq, hqk, hqodd⟩ :=
    exists_other_odd_of_even_sum_of_odd_mem
      (exchangedMissPairKeys L) f hk hkf (by simpa [f] using heven)
  have hqinc : unorderedKeyIncidence q l = 1 := by
    unfold unorderedKeyIncidence
    split <;> rename_i hinc
    · rfl
    · have hfq : f q = 0 := by
        simp [f, unorderedKeyIncidence, hinc]
      rw [hfq] at hqodd
      exact (by simpa using hqodd)
  have hqm : Odd (m q) := by
    simpa [f, hqinc] using hqodd
  exact ⟨q, hq, hqk, hqinc, hqm⟩

end

end Erdos85
