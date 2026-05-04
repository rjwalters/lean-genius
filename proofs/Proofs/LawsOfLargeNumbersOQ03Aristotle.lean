/-
  Aristotle targets for LawsOfLargeNumbersOQ03
  Routine supporting lemmas for automated proof search.
  See LawsOfLargeNumbersOQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the Birkhoff ergodic theorem (axiom — deep functional analysis)
  - NOT the mean ergodic theorem (axiom — Hilbert space methods)
  - NOT the maximal ergodic lemma (axiom — sunrise lemma)
  - Only the mixing → ergodic implication (theorem sorry, standard argument)
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)

  Included targets (1):
  - mixing_implies_ergodic_ari: IsMixing T μ → Ergodic T μ

  NOT included:
  - birkhoff_ergodic_theorem: axiom (deep, Aristotle skips)
  - birkhoff_ergodic_constant: axiom (deep, Aristotle skips)
  - maximal_ergodic_lemma: axiom (deep, Aristotle skips)
  - vonNeumann_mean_ergodic: axiom (deep, Aristotle skips)
-/
import Mathlib
import Proofs.LawsOfLargeNumbersOQ03

namespace LawsOfLargeNumbersOQ03Aristotle

open LawsOfLargeNumbersOQ03 MeasureTheory MeasurableSpace Filter Topology

/-
## Mixing Implies Ergodic

Proof strategy: Let A be a T-invariant measurable set (T⁻¹A = A, hence T^[n]⁻¹A = A).
By IsMixing, μ(A ∩ T^[n]⁻¹A) → μ(A) * μ(A).
But A is invariant, so T^[n]⁻¹A = A, and A ∩ A = A, so μ(A ∩ T^[n]⁻¹A) = μ(A) constantly.
The limit of a constant sequence μ(A) equals μ(A)² = μ(A) * μ(A).
Thus μ(A) = μ(A)², which means μ(A) * (1 - μ(A)) = 0, so μ(A) = 0 or μ(A) = 1.
Since μ is a probability measure, μ(Set.univ) = 1, so μ(A) ∈ {0, μ Set.univ}.
-/

/-- Mixing implies ergodic: invariant sets have measure 0 or 1.
    Proof: for T-invariant A, IsMixing gives μ(A) = μ(A)², so μ(A) ∈ {0,1}. -/
theorem mixing_implies_ergodic_ari {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hTm : Measurable T)
    [IsProbabilityMeasure μ] (hmix : IsMixing T μ) : Ergodic T μ := by
  refine ⟨hT, fun s hs hinv => ?_⟩
  have haeq : ∀ n, T^[n] ⁻¹' s =ᵐ[μ] s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ, Function.comp_apply]
      exact (hT.quasiMeasurePreserving.preimage_ae_eq ih).trans hinv
  have hconst : ∀ n, μ (s ∩ T^[n] ⁻¹' s) = μ s := fun n =>
    measure_congr (((ae_eq_refl s).inter (haeq n)).trans (Set.inter_self s ▸ ae_eq_refl s))
  have htend_mix := hmix s s hs hs
  have htend_const : Tendsto (fun n => μ (s ∩ T^[n] ⁻¹' s)) atTop (nhds (μ s)) := by
    simp_rw [hconst]; exact tendsto_const_nhds
  have heq : μ s = μ s * μ s := tendsto_nhds_unique htend_const htend_mix
  rcases eq_or_ne (μ s) 0 with hzero | hpos
  · exact Or.inl hzero
  · right
    have hle : μ s ≤ 1 := by
      simpa [IsProbabilityMeasure.measure_univ] using measure_mono (Set.subset_univ s)
    have htop : μ s ≠ ∞ := (lt_of_le_of_lt hle one_lt_top).ne
    have h1 : μ s = 1 := by
      rw [show μ s = μ s * 1 from (mul_one _).symm] at heq
      exact (ENNReal.mul_left_cancel₀ hpos htop heq).symm
    rw [h1, IsProbabilityMeasure.measure_univ]

end LawsOfLargeNumbersOQ03Aristotle
