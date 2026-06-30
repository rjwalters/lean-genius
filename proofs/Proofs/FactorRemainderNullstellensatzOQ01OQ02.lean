/-
  Factor-Remainder Nullstellensatz OQ-01 · OQ-02:
  Necessity of Algebraic Closure — the Nullstellensatz fails over ℝ

  The parent file `FactorRemainderNullstellensatzOQ01` formalizes the *positive*
  Nullstellensatz over an algebraically closed field `k`:

      vanishingIdeal (zeroLocus I) = I.radical          (strong form)
      I ≠ ⊤  →  zeroLocus I is nonempty                  (weak form)

  Its open questions ask whether the `IsAlgClosed` hypothesis can be dropped
  (OQ #2: behaviour over non-algebraically-closed fields; OQ #4: necessity of
  the hypotheses). This file answers that with an explicit **counterexample**.

  Over ℝ the ideal `J = (X² + 1)` in `ℝ[X]` is a proper ideal whose zero locus
  in ℝ is **empty** — the obstruction being the missing root `i ∈ ℂ \ ℝ`. Hence:

    * the weak Nullstellensatz fails: `J ≠ ⊤` yet `zeroLocus ℝ J = ∅`;
    * the strong Nullstellensatz fails: `vanishingIdeal (zeroLocus ℝ J) = ⊤`
      but `J.radical = J ≠ ⊤`.

  The complex number `i` that ℝ lacks is exactly what makes the *same* ideal over
  ℂ have a nonempty zero locus, pinpointing algebraic closure as the precise
  hypothesis that the Nullstellensatz needs.

  Parent: FactorRemainderNullstellensatzOQ01.lean
-/

import Mathlib

namespace FactorRemainderNullstellensatzOQ01OQ02

open MvPolynomial Ideal

noncomputable section

-- ============================================================
-- PART I: The witness ideal (X² + 1) over ℝ
-- ============================================================

/-- The ideal `(X² + 1)` in `ℝ[X]` (one variable). -/
def Jreal : Ideal (MvPolynomial (Fin 1) ℝ) := Ideal.span {X 0 ^ 2 + 1}

/-- Evaluation of the generator at a real point `x` is `x₀² + 1`. -/
theorem aeval_gen_real (x : Fin 1 → ℝ) :
    aeval x (X 0 ^ 2 + 1 : MvPolynomial (Fin 1) ℝ) = (x 0) ^ 2 + 1 := by
  simp

-- ============================================================
-- PART II: Empty zero locus over ℝ
-- ============================================================

/-- **No real common zero.** `X² + 1` has no real root, so the zero locus of
    `Jreal` over ℝ is empty. -/
theorem zeroLocus_real_empty :
    MvPolynomial.zeroLocus ℝ Jreal = (∅ : Set (Fin 1 → ℝ)) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hmem : (X 0 ^ 2 + 1 : MvPolynomial (Fin 1) ℝ) ∈ Jreal :=
    Ideal.subset_span (Set.mem_singleton _)
  have h0 : aeval x (X 0 ^ 2 + 1 : MvPolynomial (Fin 1) ℝ) = 0 :=
    (mem_zeroLocus_iff.mp hx) _ hmem
  rw [aeval_gen_real] at h0
  nlinarith [sq_nonneg (x 0)]

-- ============================================================
-- PART III: The ideal is proper (ℂ supplies the witness)
-- ============================================================

/-- **`Jreal` is a proper ideal.** Mapping through the ℝ-algebra homomorphism
    `ℝ[X] → ℂ`, `X ↦ i`, sends the generator to `i² + 1 = 0`; so `1 ∉ Jreal`
    (otherwise `1 = 0` in ℂ). This is where ℂ enters. -/
theorem Jreal_ne_top : Jreal ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [Jreal, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  apply_fun aeval (fun _ : Fin 1 => Complex.I) at hc
  simp [Complex.I_sq] at hc

-- ============================================================
-- PART IV: Failure of the Nullstellensatz over ℝ
-- ============================================================

/-- **Weak Nullstellensatz fails over ℝ.** `Jreal` is proper, yet its zero
    locus is empty — directly contradicting the weak Nullstellensatz conclusion
    that a proper ideal has a common zero (which holds only over algebraically
    closed fields). -/
theorem weak_nullstellensatz_fails_over_real :
    Jreal ≠ ⊤ ∧ ¬ (MvPolynomial.zeroLocus ℝ Jreal).Nonempty :=
  ⟨Jreal_ne_top, by rw [zeroLocus_real_empty]; exact Set.not_nonempty_empty⟩

/-- **Strong Nullstellensatz fails over ℝ.** `vanishingIdeal (zeroLocus Jreal)`
    collapses to `⊤` (vanishing ideal of `∅`), but `Jreal.radical ≠ ⊤`, so the
    identity `I(V(J)) = √J` breaks without algebraic closure. -/
theorem strong_nullstellensatz_fails_over_real :
    vanishingIdeal ℝ (MvPolynomial.zeroLocus ℝ Jreal) ≠ Jreal.radical := by
  rw [zeroLocus_real_empty, vanishingIdeal_empty]
  intro h
  have : Jreal.radical = ⊤ := h.symm
  rw [Ideal.radical_eq_top] at this
  exact Jreal_ne_top this

-- ============================================================
-- PART V: Positive contrast over ℂ
-- ============================================================

/-- The *same* ideal `(X² + 1)` taken over ℂ. -/
def Jcomplex : Ideal (MvPolynomial (Fin 1) ℂ) := Ideal.span {X 0 ^ 2 + 1}

/-- **Over ℂ the zero locus is nonempty**, witnessed by `x₀ = i`. The very root
    ℝ lacked makes the Nullstellensatz hold over the algebraic closure — so the
    algebraic-closure hypothesis is exactly what is needed, no more, no less. -/
theorem zeroLocus_complex_nonempty :
    (MvPolynomial.zeroLocus ℂ Jcomplex).Nonempty := by
  refine ⟨fun _ => Complex.I, ?_⟩
  rw [mem_zeroLocus_iff]
  intro p hp
  rw [Jcomplex, Ideal.mem_span_singleton] at hp
  obtain ⟨c, rfl⟩ := hp
  simp [Complex.I_sq]

end

end FactorRemainderNullstellensatzOQ01OQ02
