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

private theorem orderedKey_eq_of_endpoints_incident
    {L : Type*} [LinearOrder L] {p q : L × L}
    (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hp1 : unorderedKeyIncidence q p.1 = 1)
    (hp2 : unorderedKeyIncidence q p.2 = 1) :
    p = q := by
  have h1 : p.1 = q.1 ∨ p.1 = q.2 := by
    unfold unorderedKeyIncidence at hp1
    split at hp1
    · assumption
    · simp at hp1
  have h2 : p.2 = q.1 ∨ p.2 = q.2 := by
    unfold unorderedKeyIncidence at hp2
    split at hp2
    · assumption
    · simp at hp2
  rcases h1 with h11 | h12 <;> rcases h2 with h21 | h22
  · exact ((ne_of_lt hp) (h11.trans h21.symm)).elim
  · exact Prod.ext h11 h22
  · have hrev : q.2 < q.1 := by simpa [h12, h21] using hp
    exact (lt_asymm hq hrev).elim
  · exact ((ne_of_lt hp) (h12.trans h22.symm)).elim

/-- The odd support has two distinct continuations at every genuine odd key,
one through each endpoint.  This is the minimum-degree-two package used by
finite cycle extraction. -/
theorem exists_two_distinct_odd_exchangedKeys_at_endpoints
    {L : Type*} [Fintype L] [LinearOrder L]
    (m : L × L → Nat) {k : L × L}
    (hk : k ∈ exchangedMissPairKeys L)
    (hkodd : Odd (m k))
    (heven : ∀ l, Even
      (∑ q ∈ exchangedMissPairKeys L,
        unorderedKeyIncidence q l * m q)) :
    ∃ q ∈ exchangedMissPairKeys L,
      ∃ r ∈ exchangedMissPairKeys L,
        q ≠ k ∧ r ≠ k ∧ q ≠ r ∧
        unorderedKeyIncidence q k.1 = 1 ∧
        unorderedKeyIncidence r k.2 = 1 ∧
        Odd (m q) ∧ Odd (m r) := by
  have hklt : k.1 < k.2 := by
    simpa [exchangedMissPairKeys] using hk
  have hk1 : unorderedKeyIncidence k k.1 = 1 := by
    simp [unorderedKeyIncidence]
  have hk2 : unorderedKeyIncidence k k.2 = 1 := by
    simp [unorderedKeyIncidence, ne_of_lt hklt]
  obtain ⟨q, hq, hqk, hq1, hqodd⟩ :=
    exists_other_odd_exchangedKey_at_endpoint m hk hk1 hkodd (heven k.1)
  obtain ⟨r, hr, hrk, hr2, hrodd⟩ :=
    exists_other_odd_exchangedKey_at_endpoint m hk hk2 hkodd (heven k.2)
  have hqr : q ≠ r := by
    intro h
    subst r
    have hqlt : q.1 < q.2 := by
      simpa [exchangedMissPairKeys] using hq
    exact hqk ((orderedKey_eq_of_endpoints_incident hklt hqlt hq1 hr2).symm)
  exact ⟨q, hq, r, hr, hqk, hrk, hqr, hq1, hr2, hqodd, hrodd⟩

end

end Erdos85
