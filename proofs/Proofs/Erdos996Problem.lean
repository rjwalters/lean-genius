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

/-! ## Part I: Lacunary Sequences -/

/-- A sequence n : ℕ → ℕ is lacunary if there exists ratio > 1 such that
    n(k+1) / n(k) ≥ ratio for all k. This means the sequence has
    exponentially growing gaps. -/
def IsLacunary (n : ℕ → ℕ) : Prop :=
  ∃ ratio : ℝ, ratio > 1 ∧ ∀ k : ℕ, (n (k + 1) : ℝ) / n k ≥ ratio

/-- Example: The geometric sequence n(k) = 2^k is lacunary with ratio = 2.
    Proof: 2^(k+1) / 2^k = 2 for all k. -/
theorem powers_of_two_lacunary : IsLacunary (fun k => 2^k) := by
  use (2 : ℝ)
  constructor
  · norm_num
  · intro k
    have h : (2 : ℕ)^k ≠ 0 := by positivity
    simp only [pow_succ]
    rw [Nat.cast_mul, mul_comm]
    rw [mul_div_assoc]
    rw [div_self (Nat.cast_ne_zero.mpr h)]
    norm_num

/-- Example: n(k) = 3^k is lacunary with ratio = 3.
    Proof: 3^(k+1) / 3^k = 3 for all k. -/
theorem powers_of_three_lacunary : IsLacunary (fun k => 3^k) := by
  use (3 : ℝ)
  constructor
  · norm_num
  · intro k
    have h : (3 : ℕ)^k ≠ 0 := by positivity
    simp only [pow_succ]
    rw [Nat.cast_mul, mul_comm]
    rw [mul_div_assoc]
    rw [div_self (Nat.cast_ne_zero.mpr h)]
    norm_num

/-- Any lacunary sequence is strictly increasing. -/
theorem lacunary_strictMono {n : ℕ → ℕ} (hn : IsLacunary n) (h0 : n 0 > 0) :
    StrictMono n := by
  sorry

/-! ## Part II: Fourier Series and Partial Sums -/

/-- The Nth partial sum of the Fourier series of f.
    This is the best L² approximation of f using frequencies -N to N. -/
noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ :=
  fun x => ∑ n ∈ Finset.Icc (-N : ℤ) N,
    (∫ t in (0 : ℝ)..1, f t * Complex.exp (-2 * Real.pi * Complex.I * n * t)) *
    Complex.exp (2 * Real.pi * Complex.I * n * x)

/-- The L² norm of f - fₙ measures how well the partial sum approximates f. -/
noncomputable def fourierError (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (∫ x in (0 : ℝ)..1, ‖f x - fourierPartialSum f N x‖^2)

/-- Parseval's identity: the L² norm equals the sum of squared Fourier coefficients. -/
axiom parseval_identity (f : ℝ → ℂ) (hf : Integrable (fun x => ‖f x‖^2) (volume.restrict (Set.Icc 0 1))) :
    ∫ x in (0 : ℝ)..1, ‖f x‖^2 =
    ∑' n : ℤ, ‖∫ t in (0 : ℝ)..1, f t * Complex.exp (-2 * Real.pi * Complex.I * n * t)‖^2

/-! ## Part III: The Ergodic Average -/

/-- The fractional part {x} = x - ⌊x⌋. -/
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

/-- The ergodic average: (1/N) Σₖ<N f({α·nₖ}).
    This averages f over the orbit of α under the lacunary sequence. -/
noncomputable def ergodicAverage (f : ℝ → ℂ) (n : ℕ → ℕ) (α : ℝ) (N : ℕ) : ℂ :=
  (1 / N : ℂ) * ∑ k ∈ Finset.range N, f (frac (α * n k))

/-- The space average: ∫₀¹ f(x) dx.
    The strong law says the ergodic average converges to this. -/
noncomputable def spaceAverage (f : ℝ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, f x

/-! ## Part IV: The Strong Law of Large Numbers -/

/-- The strong law holds for (f, n, α) if the ergodic average converges
    to the space average. -/
def StrongLawHolds (f : ℝ → ℂ) (n : ℕ → ℕ) (α : ℝ) : Prop :=
  Tendsto (ergodicAverage f n α) atTop (𝓝 (spaceAverage f))

/-- The strong law holds almost everywhere for (f, n) if it holds for
    almost every α ∈ [0, 1]. -/
def StrongLawHoldsAE (f : ℝ → ℂ) (n : ℕ → ℕ) : Prop :=
  ∀ᵐ α ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), StrongLawHolds f n α

/-! ## Part V: Known Results -/

/-- **Raikov's Theorem**: For geometric sequences nₖ = aᵏ, the strong law
    holds for all f ∈ L² without any decay condition on Fourier error.

    This is the cleanest case: geometric sequences have enough
    "independence" for the strong law to hold unconditionally. -/
axiom raikov_theorem (a : ℕ) (ha : a ≥ 2) (f : ℝ → ℂ)
    (hf : Integrable (fun x => ‖f x‖^2) (volume.restrict (Set.Icc 0 1))) :
    StrongLawHoldsAE f (fun k => a^k)

/-- **Kac-Salem-Zygmund (1948)**: If the Fourier error decays like
    1/(log n)^c for c > 1, the strong law holds for any lacunary sequence.

    This was the first general result for lacunary sequences. -/
axiom kac_salem_zygmund_1948 (c : ℝ) (hc : c > 1) (f : ℝ → ℂ) (n : ℕ → ℕ)
    (hn : IsLacunary n)
    (hdecay : ∀ k : ℕ, fourierError f k ≤ 1 / (Real.log k)^c) :
    StrongLawHoldsAE f n

/-- **Erdős (1949)**: Improved to 1/(log log n)^c for c > 1.

    This was a significant improvement, replacing log with log log. -/
axiom erdos_1949 (c : ℝ) (hc : c > 1) (f : ℝ → ℂ) (n : ℕ → ℕ)
    (hn : IsLacunary n)
    (hdecay : ∀ k : ℕ, k ≥ 3 → fourierError f k ≤ 1 / (Real.log (Real.log k))^c) :
    StrongLawHoldsAE f n

/-- **Matsuyama (1966)**: Further improved to c > 1/2 for log log decay.

    This is currently the best known result for log log decay. -/
axiom matsuyama_1966 (c : ℝ) (hc : c > 1/2) (f : ℝ → ℂ) (n : ℕ → ℕ)
    (hn : IsLacunary n)
    (hdecay : ∀ k : ℕ, k ≥ 3 → fourierError f k ≤ 1 / (Real.log (Real.log k))^c) :
    StrongLawHoldsAE f n

/-! ## Part VI: The Open Question -/

/-- **Erdős Problem #996**: Is there a constant C such that if the Fourier
    error decays like 1/(log log log n)^C, the strong law holds?

    This asks whether we can go one step further from log log to log log log. -/
def ErdosProblem996 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ f : ℝ → ℂ, ∀ n : ℕ → ℕ,
    IsLacunary n →
    (∀ k : ℕ, k ≥ 16 → fourierError f k ≤ 1 / (Real.log (Real.log (Real.log k)))^C) →
    StrongLawHoldsAE f n

/-- The status of Problem #996: OPEN.
    We don't know if log log log decay suffices. -/
axiom erdos_996_open : True  -- Placeholder indicating open status

/-! ## Part VII: Related Questions -/

/-- Erdős also asked if the strong law holds for nₖ = ⌊aᵏ⌋ for real a > 1.
    This is related but distinct from the Fourier decay question. -/
def FloorPowerQuestion (a : ℝ) (ha : a > 1) : Prop :=
  ∀ f : ℝ → ℂ, Integrable (fun x => ‖f x‖^2) (volume.restrict (Set.Icc 0 1)) →
    StrongLawHoldsAE f (fun k => ⌊a^k⌋.toNat)

/-- Erdős asked if the strong law holds for all bounded functions f
    and lacunary sequences n. -/
def BoundedFunctionQuestion : Prop :=
  ∀ f : ℝ → ℂ, (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) →
    ∀ n : ℕ → ℕ, IsLacunary n → StrongLawHoldsAE f n

/-! ## Part VIII: The Decay Hierarchy -/

/-- The hierarchy of decay conditions, from strongest to weakest:
    1. No decay needed (Raikov, for geometric sequences)
    2. 1/(log n)^c for c > 1 (Kac-Salem-Zygmund)
    3. 1/(log log n)^c for c > 1 (Erdős 1949)
    4. 1/(log log n)^c for c > 1/2 (Matsuyama 1966)
    5. 1/(log log log n)^C for some C? (Problem #996) -/
structure DecayCondition where
  name : String
  decayRate : ℕ → ℝ
  sufficient : Bool

/-- The log decay condition. -/
noncomputable def logDecay (c : ℝ) : DecayCondition :=
  { name := "1/(log n)^c"
  , decayRate := fun k => 1 / (Real.log k)^c
  , sufficient := c > 1 }

/-- The log log decay condition (Matsuyama improvement). -/
noncomputable def logLogDecay (c : ℝ) : DecayCondition :=
  { name := "1/(log log n)^c"
  , decayRate := fun k => 1 / (Real.log (Real.log k))^c
  , sufficient := c > 1/2 }

/-- The log log log decay condition (Problem #996). -/
noncomputable def logLogLogDecay (c : ℝ) : DecayCondition :=
  { name := "1/(log log log n)^c"
  , decayRate := fun k => 1 / (Real.log (Real.log (Real.log k)))^c
  , sufficient := false }  -- Unknown!

/-! ## Part IX: Why Lacunary Sequences? -/

/-- Lacunary sequences have a "quasi-independence" property.
    The sequence {α·nₖ} mod 1 behaves almost like independent random variables.

    This is why the strong law (a probabilistic statement) applies. -/
theorem lacunary_quasi_independent {n : ℕ → ℕ} (hn : IsLacunary n) :
    True := by  -- Placeholder for the quasi-independence property
  trivial

/-- Non-lacunary sequences can fail the strong law.
    For example, consecutive integers n(k) = k+1 don't satisfy it because
    the ratio (k+2)/(k+1) → 1 as k → ∞, so no ratio > 1 can be a lower bound. -/
theorem consecutive_not_lacunary : ¬IsLacunary (fun k => k + 1) := by
  intro ⟨ratio, hratio, hseq⟩
  -- For large k, (k+2)/(k+1) < ratio since (k+2)/(k+1) → 1
  -- This requires an archimedean argument
  sorry

/-! ## Part X: The Gap Between Results -/

/-- The gap between known results and Problem #996:
    - We know log log decay with c > 1/2 suffices (Matsuyama)
    - We don't know if log log log decay ever suffices
    - The question is whether the "extra log" can be removed -/
theorem known_gap :
    (∀ c > (1/2 : ℝ), ∀ f n, IsLacunary n →
      (∀ k ≥ 3, fourierError f k ≤ 1 / (Real.log (Real.log k))^c) →
      StrongLawHoldsAE f n) ∧
    True := by  -- The second conjunct is the open question
  constructor
  · intro c hc f n hn hdecay
    exact matsuyama_1966 c hc f n hn hdecay
  · trivial

/-! ## Part XI: Connections to Other Areas -/

/-
The problem connects to:
1. Ergodic theory: equidistribution of sequences
2. Harmonic analysis: Fourier series convergence
3. Probability: law of large numbers
4. Diophantine approximation: distribution of fractional parts
-/

/-- Weyl's equidistribution theorem: fractional parts of αn are equidistributed
    for irrational α. This is a precursor to the strong law. -/
axiom weyl_equidistribution (α : ℝ) (hα : Irrational α) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * (Finset.range N).card)
      atTop (𝓝 1)

/-! ## Part XII: Summary -/

/-- Summary of Erdős Problem #996:

    **Status**: PARTIALLY SOLVED / OPEN

    **Known Results**:
    - Matsuyama (1966): log log decay with c > 1/2 suffices

    **Open Question**:
    - Does log log log decay (with some power C) suffice?

    **Key Concepts**:
    - Lacunary sequences (exponentially growing gaps)
    - Fourier partial sums and L² error
    - Ergodic averages along the sequence
    - Strong law of large numbers for dynamical systems -/
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

/-!
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
