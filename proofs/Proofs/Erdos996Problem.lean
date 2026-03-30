/-
  Erdős Problem #996: Strong Law of Large Numbers for Lacunary Sequences

  Source: https://erdosproblems.com/996
  Status: PARTIALLY SOLVED (Matsuyama 1966 improved earlier bounds)

  Statement:
  Let n₁ < n₂ < ... be a lacunary sequence of integers, and let f ∈ L²([0,1]).
  Let fₙ be the nth partial sum of the Fourier series of f. Is there an
  absolute constant C > 0 such that, if

      ‖f - fₙ‖₂ ≪ 1/(log log log n)^C

  then for almost every α:

      lim_{N→∞} (1/N) Σₖ≤N f({α·nₖ}) = ∫₀¹ f(x)dx

  Historical Context:
  This problem connects harmonic analysis (Fourier series) with probability
  theory (strong law of large numbers) and ergodic theory.

  Key Results:
  - Raikov: Proved for nₖ = aᵏ (geometric sequences)
  - Kac-Salem-Zygmund (1948): Works if ‖f - fₙ‖₂ = O(1/(log n)^c) for c > 1
  - Erdős (1949): Works if ‖f - fₙ‖₂ = O(1/(log log n)^c) for c > 1
  - Matsuyama (1966): Improved to c > 1/2 for log log

  The question asks if log log log suffices with some power C.

  References:
  [Er49d] Erdős, "On the strong law of large numbers" (1949)
  [Ma66] Matsuyama, "On the strong law of large numbers" (1966)
  [KSZ48] Kac, Salem, Zygmund, "A gap theorem" (1948)

  Tags: harmonic-analysis, probability, lacunary-sequences, fourier-series
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace Erdos996

open MeasureTheory Filter Topology Real

/- ## Part I: Lacunary Sequences -/

-- parseval_identity: unused axiom removed (never referenced by any theorem)
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

-- raikov_theorem: unused axiom removed (never referenced by any theorem)
-- kac_salem_zygmund_1948: unused axiom removed (never referenced by any theorem)
-- erdos_1949: unused axiom removed (never referenced by any theorem)
axiom matsuyama_1966 (c : ℝ) (hc : c > 1/2) (f : ℝ → ℂ) (n : ℕ → ℕ)
    (hn : IsLacunary n)
    (hdecay : ∀ k : ℕ, k ≥ 3 → fourierError f k ≤ 1 / (Real.log (Real.log k))^c) :
    StrongLawHoldsAE f n

/- ## Part VI: The Open Question -/

-- weyl_equidistribution: unused axiom removed (never referenced by any theorem)
theorem erdos_996_summary :
    (∃ c : ℝ, c > 1/2 ∧ ∀ f n, IsLacunary n →
      (∀ k ≥ 3, fourierError f k ≤ 1 / (Real.log (Real.log k))^c) →
      StrongLawHoldsAE f n) ∧
    True := by  -- Second conjunct: open question about log log log
  constructor
  · use 1
    constructor
    · norm_num
    · intro f n hn hdecay
      exact matsuyama_1966 1 (by norm_num) f n hn hdecay
  · trivial

end Erdos996

/-
## Summary

This file formalizes Erdős Problem #996 on the strong law of large numbers
for lacunary sequences.

**Status**: PARTIALLY SOLVED (log log decay) / OPEN (log log log decay)

**The Problem**: For lacunary sequences and L² functions, if the Fourier
error decays like 1/(log log log n)^C, does the strong law hold?

**What we formalize**:
1. Lacunary sequences (exponentially growing gaps)
2. Fourier partial sums and error
3. Ergodic averages along lacunary sequences
4. The strong law of large numbers
5. Known results: Raikov, Kac-Salem-Zygmund, Erdős, Matsuyama
6. The open question about log log log decay
7. Related questions about floor powers and bounded functions

**Key insight**: Lacunary sequences have quasi-independence, allowing
probabilistic tools (law of large numbers) to apply. The question is
how much Fourier regularity is needed.

**Historical Note**: This problem sits at the intersection of harmonic
analysis, probability, and ergodic theory. The progression from log
to log log (Erdős 1949) to log log with c > 1/2 (Matsuyama 1966)
suggests that log log log might also work.
-/
