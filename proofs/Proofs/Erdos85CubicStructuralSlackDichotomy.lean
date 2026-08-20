import Proofs.Erdos85CubicStructuralExcessActualPopulation
import Proofs.Erdos85CubicRowExcessParity
import Proofs.Erdos85ServiceSixthTraceDivisibility

/-! # Locating the unavoidable cubic sixth-moment slack -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- If forty rows have the structural lower bound four and global spectral
excess is at least 198, then either one of those rows jumps to at least six,
or all forty are sharp and the eight-row complement carries at least 38
units of excess.  In the latter case parity forces a complementary row to
jump to at least six as well. -/
theorem forty_good_rows_spectralSlack_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (N : Finset V) (hNcard : N.card = 40)
    (hgood : ∀ a ∈ N, 4 ≤ cubicRowHistogramExcess G a)
    (htotal : 198 ≤ ∑ a : V, cubicRowHistogramExcess G a) :
    (∃ a ∈ N, 6 ≤ cubicRowHistogramExcess G a) ∨
      ((∀ a ∈ N, cubicRowHistogramExcess G a = 4) ∧
        38 ≤ ∑ a ∈ (Finset.univ \ N), cubicRowHistogramExcess G a ∧
        ∃ a ∈ (Finset.univ \ N), 6 ≤ cubicRowHistogramExcess G a) := by
  classical
  let F := fun a : V ↦ cubicRowHistogramExcess G a
  by_cases hhigh : ∃ a ∈ N, 6 ≤ F a
  · exact Or.inl hhigh
  · right
    have hsharp : ∀ a ∈ N, F a = 4 := by
      intro a ha
      rcases cubicRowHistogramExcess_eq_four_or_ge_six
        G hfree hreg a (hgood a ha) with heq | hsix
      · exact heq
      · exact False.elim (hhigh ⟨a, ha, hsix⟩)
    have hNsum : (∑ a ∈ N, F a) = 160 := by
      calc
        _ = ∑ _a ∈ N, (4 : ℤ) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hsharp a ha
        _ = 160 := by simp [hNcard]
    let M := (Finset.univ : Finset V) \ N
    have hsplit : (∑ a : V, F a) =
        (∑ a ∈ N, F a) + ∑ a ∈ M, F a := by
      have hd : Disjoint N M := Finset.disjoint_sdiff
      have hc : N ∪ M = Finset.univ := by
        rw [Finset.union_sdiff_of_subset (Finset.subset_univ N)]
      rw [← Finset.sum_union hd, hc]
    have hMlower : 38 ≤ ∑ a ∈ M, F a := by
      rw [hsplit, hNsum] at htotal
      omega
    have hMcard : M.card = 8 := by
      dsimp [M]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ N),
        Finset.card_univ, hcard, hNcard]
    have hMhigh : ∃ a ∈ M, 6 ≤ F a := by
      by_contra hnone
      simp only [not_exists, not_and, not_le] at hnone
      have hle : ∑ a ∈ M, F a ≤ 32 := by
        calc
          _ ≤ ∑ _a ∈ M, (4 : ℤ) := by
            apply Finset.sum_le_sum
            intro a ha
            have hn := cubicRowHistogramExcess_nonnegative G hfree hreg a
            rcases even_cubicRowHistogramExcess G hfree hreg a with ⟨k, hk⟩
            have hlt : F a < 6 := hnone a ha
            change 0 ≤ F a at hn
            change F a = k + k at hk
            omega
          _ = 32 := by simp [hMcard]
      omega
    exact ⟨hsharp, by simpa [M] using hMlower, by simpa [M] using hMhigh⟩

/-- The strict sixth-moment hypothesis supplies the total-excess premise of
the forty-row slack dichotomy. -/
theorem forty_good_rows_strictTrace_spectralSlack_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 48)
    (hreg : ∀ x, G.degree x = 6)
    (hstrict : 61248 < Matrix.trace ((G.adjMatrix ℤ) ^ 6))
    (N : Finset V) (hNcard : N.card = 40)
    (hgood : ∀ a ∈ N, 4 ≤ cubicRowHistogramExcess G a) :
    (∃ a ∈ N, 6 ≤ cubicRowHistogramExcess G a) ∨
      ((∀ a ∈ N, cubicRowHistogramExcess G a = 4) ∧
        38 ≤ ∑ a ∈ (Finset.univ \ N), cubicRowHistogramExcess G a ∧
        ∃ a ∈ (Finset.univ \ N), 6 ≤ cubicRowHistogramExcess G a) := by
  apply forty_good_rows_spectralSlack_dichotomy
    G hfree hcard hreg N hNcard hgood
  rw [sum_cubicRowHistogramExcess_eq_histogramExcess]
  exact sixRegular_fortyEight_histogramExcess_ge_198
    G hfree hcard hreg hstrict

end


end Erdos85

#print axioms Erdos85.forty_good_rows_spectralSlack_dichotomy
#print axioms Erdos85.forty_good_rows_strictTrace_spectralSlack_dichotomy
