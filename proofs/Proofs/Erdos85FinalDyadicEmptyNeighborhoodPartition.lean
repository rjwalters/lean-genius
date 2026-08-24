import Proofs.Erdos85FinalDyadicFullPairPartition

/-!
# Empty-center neighborhood partition of the negative-high class

Equality `|M| = q|E|`, together with one empty neighbor per negative-high
vertex, forces every empty center to spend its full degree inside `M`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If a bounded finite family attains its maximal possible sum, every term
attains the common bound. -/
theorem eq_bound_of_sum_eq_card_mul
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (q : ℕ)
    (hle : ∀ x ∈ s, f x ≤ q)
    (hsum : ∑ x ∈ s, f x = q * s.card) :
    ∀ x ∈ s, f x = q := by
  intro x hx
  have hrest : (∑ y ∈ s.erase x, f y) ≤ q * (s.erase x).card := by
    calc
      _ ≤ ∑ _y ∈ s.erase x, q := by
        apply Finset.sum_le_sum
        intro y hy
        exact hle y (Finset.mem_of_mem_erase hy)
      _ = _ := by simp [Nat.mul_comm]
  have hsplit := Finset.sum_erase_add s f hx
  rw [hsum] at hsplit
  rw [Finset.card_erase_of_mem hx] at hrest
  have hcardPos : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hmulSplit : q * (s.card - 1) + q = q * s.card := by
    calc
      q * (s.card - 1) + q = q * (s.card - 1) + q * 1 := by rw [Nat.mul_one]
      _ = q * ((s.card - 1) + 1) := (Nat.mul_add _ _ _).symm
      _ = q * s.card := by rw [Nat.sub_add_cancel (by omega : 1 ≤ s.card)]
  by_contra hne
  have hltTerm : f x < q := Nat.lt_of_le_of_ne (hle x hx) hne
  have hlt : (∑ y ∈ s.erase x, f y) + f x <
      q * (s.card - 1) + q :=
    Nat.add_lt_add_of_le_of_lt hrest hltTerm
  rw [hsplit, hmulSplit] at hlt
  exact (Nat.lt_irrefl _ hlt)

/-- Every empty center has all `q` graph neighbors in the negative-high
class. -/
theorem finalDyadic_emptyCenter_neighbor_inter_negativeHigh_card_eq_q
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    ∀ e ∈ emptyLineCenters G S,
      (G.neighborFinset e ∩
        finalDyadicNegativeHighCutCenters G S j r).card = q := by
  let E := emptyLineCenters G S
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hprofile := finalDyadic_negativeHigh_exact_empty_neighbor
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
  have hleft : (∑ v ∈ M, (G.neighborFinset v ∩ E).card) = M.card := by
    calc
      _ = ∑ _v ∈ M, 1 := by
        apply Finset.sum_congr rfl
        exact hprofile
      _ = _ := by simp
  have hcomm := sum_card_neighbor_inter_comm G M E
  have hME := finalDyadic_negativeHigh_card_eq_q_mul_empty
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique
  change M.card = q * E.card at hME
  have hsum : (∑ e ∈ E, (G.neighborFinset e ∩ M).card) = q * E.card := by
    rw [← hME, ← hleft, hcomm]
  have hle : ∀ e ∈ E, (G.neighborFinset e ∩ M).card ≤ q := by
    intro e _
    calc
      (G.neighborFinset e ∩ M).card ≤ (G.neighborFinset e).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  exact eq_bound_of_sum_eq_card_mul E
    (fun e => (G.neighborFinset e ∩ M).card) q hle hsum

/-- Literal neighborhood form: every graph neighbor of an empty center is
negative-high. -/
theorem finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e : V} (he : e ∈ emptyLineCenters G S) :
    G.neighborFinset e ⊆ finalDyadicNegativeHighCutCenters G S j r := by
  have hinter := finalDyadic_emptyCenter_neighbor_inter_negativeHigh_card_eq_q
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
      hsupport hemptyClique e he
  have hdegree : (G.neighborFinset e).card = q := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  have heq : G.neighborFinset e ∩
      finalDyadicNegativeHighCutCenters G S j r = G.neighborFinset e := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    rw [hinter, hdegree]
  intro v hv
  have : v ∈ G.neighborFinset e ∩
      finalDyadicNegativeHighCutCenters G S j r := by
    rw [heq]
    exact hv
  exact (Finset.mem_inter.mp this).2

/-- Membership form of the neighborhood partition: `M` is exactly the union
of the graph neighborhoods of the empty centers. -/
theorem finalDyadic_mem_negativeHigh_iff_exists_empty_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r c : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = c)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (v : V) :
    v ∈ finalDyadicNegativeHighCutCenters G S j r ↔
      ∃ e ∈ emptyLineCenters G S, v ∈ G.neighborFinset e := by
  constructor
  · intro hvM
    have hone := finalDyadic_negativeHigh_exact_empty_neighbor
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hvM
    have hnonempty :
        (G.neighborFinset v ∩ emptyLineCenters G S).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hnonempty
    have heData := Finset.mem_inter.mp he
    exact ⟨e, heData.2, by
      exact (G.mem_neighborFinset e v).mpr
        ((G.mem_neighborFinset v e).mp heData.1).symm⟩
  · rintro ⟨e, heE, hvN⟩
    exact finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique heE hvN

end

end Erdos85

#print axioms Erdos85.eq_bound_of_sum_eq_card_mul
#print axioms
  Erdos85.finalDyadic_emptyCenter_neighbor_inter_negativeHigh_card_eq_q
#print axioms
  Erdos85.finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
#print axioms
  Erdos85.finalDyadic_mem_negativeHigh_iff_exists_empty_neighbor
