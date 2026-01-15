/-
  Erdős Problem #138: Van der Waerden Numbers Growth Rate

  Source: https://erdosproblems.com/138
  Status: OPEN (main conjecture)
  Prize: $500

  Statement:
  Improve the bounds for the van der Waerden number W(k), specifically prove
  that W(k)^{1/k} → ∞.

  The van der Waerden number W(k) is the smallest integer N such that any
  2-coloring of {1, ..., N} must contain a monochromatic k-term arithmetic
  progression.

  Known Results:
  - Berlekamp (1968): W(p+1) ≥ p · 2^p for prime p
  - Gowers (2001): W(k) ≤ 2^{2^{2^{2^{2^{k+9}}}}} (tower of 5)
  - Kozik-Shabanov (2016): W(k) ≫ 2^k (best general lower bound)

  The main conjecture W(k)^{1/k} → ∞ remains OPEN.

  References:
  - Berlekamp, E. R. (1968): "A construction for partitions which avoid
    long arithmetic progressions"
  - Gowers, W. T. (2001): "A new proof of Szemerédi's theorem"
  - Erdős (1980, 1981): Original problem statements
-/

import Mathlib

open Nat Filter Finset

namespace Erdos138

/-! ## Van der Waerden Numbers -/

/-- A coloring of {1, ..., N} using r colors -/
def Coloring (N r : ℕ) := Finset.Icc 1 N → Fin r

/-- A set contains a monochromatic k-term arithmetic progression under
    the given coloring if there exist a, d > 0 such that all of
    a, a+d, a+2d, ..., a+(k-1)d have the same color. -/
def HasMonochromaticAP {N r : ℕ} (c : Coloring N r) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ (∀ i : Fin k, a + i.val * d ∈ Finset.Icc 1 N) ∧
    (∀ i j : Fin k, c ⟨a + i.val * d, by sorry⟩ = c ⟨a + j.val * d, by sorry⟩)

/-- Van der Waerden's Theorem: For any r ≥ 1 and k ≥ 1, there exists N
    such that any r-coloring of {1, ..., N} contains a monochromatic
    k-term arithmetic progression.

    This is a fundamental result in Ramsey theory, proved by van der Waerden
    in 1927. We axiomatize it as the foundation for the van der Waerden numbers. -/
axiom van_der_waerden_theorem :
  ∀ r k : ℕ, r ≥ 1 → k ≥ 1 → ∃ N : ℕ, ∀ c : Coloring N r, HasMonochromaticAP c k

/-- The set of N that guarantee a monochromatic k-term AP for r colors -/
def GuaranteeSet (r k : ℕ) : Set ℕ :=
  { N | ∀ c : Coloring N r, HasMonochromaticAP c k }

/-- The van der Waerden number W(r, k) is the minimum N guaranteeing
    a monochromatic k-term AP in any r-coloring of {1, ..., N}. -/
noncomputable def vanDerWaerden (r k : ℕ) : ℕ :=
  sInf (GuaranteeSet r k)

/-- Standard notation: W(k) = W(2, k) for 2-colorings -/
noncomputable abbrev W (k : ℕ) : ℕ := vanDerWaerden 2 k

/-! ## Known Bounds -/

/-- **Berlekamp (1968)**: For prime p, W(p+1) ≥ p · 2^p.
    This gives strong lower bounds at prime values. -/
axiom berlekamp_lower_bound (p : ℕ) (hp : p.Prime) :
  p * (2 ^ p) ≤ W (p + 1)

/-- **Gowers (2001)**: W(k) ≤ 2^{2^{2^{2^{2^{k+9}}}}}.
    This is the current best upper bound, a tower of height 5.
    It comes from Gowers' analytic proof of Szemerédi's theorem. -/
axiom gowers_upper_bound (k : ℕ) :
  W k ≤ 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (k + 9)))))

/-- **Kozik-Shabanov (2016)**: W(k) ≫ 2^k.
    The best known general lower bound. -/
axiom kozik_shabanov_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 1 → (c * 2^k : ℝ) ≤ W k

/-! ## Small Values -/

/-- W(1) = 1: Any single element is a 1-term AP -/
theorem W_one : W 1 = 1 := by
  sorry -- Requires showing 1 suffices and nothing smaller works

/-- W(2) = 3: To avoid a 2-term AP (any two distinct elements), need N < 3 -/
theorem W_two : W 2 = 3 := by
  sorry -- Classic example

/-- W(3) = 9: First non-trivial case -/
axiom W_three : W 3 = 9

/-- W(4) = 35: Computed by exhaustive search -/
axiom W_four : W 4 = 35

/-- W(5) = 178: Computed by Landman and Robertson (2014) -/
axiom W_five : W 5 = 178

/-- W(6) = 1132: Computed by Kouril and Paul (2008) -/
axiom W_six : W 6 = 1132

/-! ## The Main Conjecture (OPEN) -/

/-- **Erdős Problem #138** (OPEN, $500 prize):
    Does W(k)^{1/k} → ∞ as k → ∞?

    This asks whether the van der Waerden numbers grow faster than
    any exponential function. Given the tower-type upper bounds
    and exponential lower bounds, this is a central open question. -/
def Erdos138Conjecture : Prop :=
  Tendsto (fun k => (W k : ℝ) ^ (1 / (k : ℝ))) atTop atTop

/-! ## Related Questions (Erdős 1980-1981) -/

/-- Does W(k+1)/W(k) → ∞?
    Asks whether consecutive van der Waerden numbers have unbounded ratio. -/
def QuotientDiverges : Prop :=
  Tendsto (fun k => ((W (k + 1) : ℚ) / (W k))) atTop atTop

/-- Does W(k+1) - W(k) → ∞?
    Asks whether consecutive differences grow without bound. -/
def DifferenceDiverges : Prop :=
  Tendsto (fun k => (W (k + 1) - W k : ℤ)) atTop atTop

/-- Does W(k)/2^k → ∞?
    Asks whether W(k) grows faster than 2^k. -/
def ExponentialDiverges : Prop :=
  Tendsto (fun k => ((W k : ℚ) / (2 ^ k))) atTop atTop

/-! ## Implications -/

/-- If the main conjecture holds, then W(k)/2^k → ∞.
    Proof: W(k)^{1/k} → ∞ means for any c, eventually W(k)^{1/k} > c,
    so W(k) > c^k, and choosing c = 2 gives W(k) > 2^k eventually. -/
theorem conjecture_implies_exponential :
    Erdos138Conjecture → ExponentialDiverges := by
  intro hconj
  -- The proof follows from comparing growth rates
  sorry

/-! ## Summary

**Problem Status: OPEN ($500 prize)**

Erdős Problem #138 asks whether W(k)^{1/k} → ∞, i.e., whether the van der
Waerden numbers grow faster than any exponential.

**What we know:**
- Lower: W(k) ≫ 2^k (Kozik-Shabanov 2016)
- Upper: W(k) ≤ tower of height 5 (Gowers 2001)
- At primes: W(p+1) ≥ p · 2^p (Berlekamp 1968)

**The gap:**
The exponential lower bound and tower upper bound leave a vast unknown region.
Improving either bound would be significant progress.

**Related questions:**
- W(k+1)/W(k) → ∞?
- W(k+1) - W(k) → ∞?
- W(k)/2^k → ∞?

References:
- van der Waerden (1927): Original theorem
- Berlekamp (1968): Lower bound construction
- Gowers (2001): Analytic proof with tower bounds
- Erdős (1980, 1981): Problem statement and variants
-/

end Erdos138
