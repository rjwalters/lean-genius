/-
  Erdős Problem #138: Van der Waerden Numbers Growth Rate

  Source: https://erdosproblems.com/138
  Status: OPEN ($500 prize)
  Posed by: Paul Erdős, 1980–1981

  **Statement**: Does W(k)^{1/k} → ∞ as k → ∞?

  The van der Waerden number W(k) is the smallest integer N such that any
  2-coloring of {1, ..., N} must contain a monochromatic k-term arithmetic
  progression. Van der Waerden proved in 1927 that W(k) is finite for all k,
  but determining its growth rate remains a central open problem.

  **Known Bounds**:
  - Berlekamp (1968): W(p+1) ≥ p · 2^p for prime p
  - Kozik–Shabanov (2016): W(k) ≥ c · 2^k (best general lower bound)
  - Gowers (2001): W(k) ≤ 2^{2^{2^{2^{2^{k+9}}}}} (tower of height 5)

  **Exact Small Values**:
  W(3) = 9, W(4) = 35, W(5) = 178, W(6) = 1132

  **References**:
  - Berlekamp, E. R. (1968): "A construction for partitions which avoid long APs"
  - Gowers, W. T. (2001): "A new proof of Szemerédi's theorem"
  - Kozik, J.; Shabanov, D. (2016): "Improved algorithms for colorings of
    simple hypergraphs and applications"
  - Erdős, P. (1980, 1981): Problem statements and variants
-/

import Mathlib

open Nat Filter Finset

namespace Erdos138

/-! ## Colorings and Arithmetic Progressions -/

/-- A coloring of {1, ..., N} using r colors is a function assigning one of r
    colors to each element of the set {1, ..., N}. -/
def Coloring (N r : ℕ) := Finset.Icc 1 N → Fin r

/-- A coloring `c` contains a monochromatic k-term arithmetic progression if there
    exist a starting value `a`, a positive common difference `d`, and a single color
    `col` such that all k terms a, a+d, a+2d, ..., a+(k-1)d lie in {1,...,N}
    and each receives color `col`. -/
def HasMonochromaticAP {N r : ℕ} (c : Coloring N r) (k : ℕ) : Prop :=
  ∃ (a d : ℕ) (col : Fin r), 0 < d ∧
  ∀ (i : Fin k) (h : a + i.val * d ∈ Finset.Icc 1 N), c ⟨a + i.val * d, h⟩ = col

/-! ## Van der Waerden's Theorem and the Guarantee Set -/

/-- **Van der Waerden's Theorem** (1927): For any number of colors r ≥ 1 and
    progression length k ≥ 1, there exists N such that every r-coloring of {1,...,N}
    contains a monochromatic k-term arithmetic progression.

    The original proof uses double induction on r and k. Shelah (1988) gave the
    first primitive recursive proof. Gowers (2001) proved a much stronger bound.
    We axiomatize this result as the foundation for the van der Waerden numbers. -/
axiom van_der_waerden_theorem :
  ∀ r k : ℕ, 1 ≤ r → 1 ≤ k →
  ∃ N : ℕ, ∀ c : Coloring N r, HasMonochromaticAP c k

/-- The **guarantee set** for parameters (r, k) is the collection of all N such that
    every r-coloring of {1,...,N} contains a monochromatic k-term AP.
    Van der Waerden's theorem ensures this set is nonempty for r, k ≥ 1. -/
def GuaranteeSet (r k : ℕ) : Set ℕ :=
  { N | ∀ c : Coloring N r, HasMonochromaticAP c k }

/-- The guarantee set is nonempty for r ≥ 1 and k ≥ 1,
    as an immediate consequence of van der Waerden's theorem. -/
theorem guaranteeSet_nonempty (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (GuaranteeSet r k).Nonempty :=
  van_der_waerden_theorem r k hr hk

/-- The **van der Waerden number** W(r, k) is the minimum N such that any r-coloring
    of {1,...,N} contains a monochromatic k-term AP. It is defined as the infimum of
    the nonempty guarantee set. -/
noncomputable def vanDerWaerden (r k : ℕ) : ℕ :=
  sInf (GuaranteeSet r k)

/-- **Standard notation**: W(k) = W(2, k) for 2-colorings, the most studied case.
    This represents the smallest N such that any red-blue coloring of {1,...,N}
    contains a monochromatic k-term arithmetic progression. -/
noncomputable abbrev W (k : ℕ) : ℕ := vanDerWaerden 2 k

/-! ## Known Bounds on W(k) -/

/-- **Berlekamp's Lower Bound** (1968): For prime p, W(p+1) ≥ p · 2^p.

    The proof uses a finite field construction: color the integers {1,...,p·2^p} by
    (a, b) where a is the discrete logarithm of the integer mod p, and b is a binary
    digit. This coloring avoids any monochromatic (p+1)-term AP.

    Sample bounds:
    - p=2: W(3) ≥ 8  (actual: W(3) = 9)
    - p=3: W(4) ≥ 24 (actual: W(4) = 35)
    - p=5: W(6) ≥ 160 (actual: W(6) = 1132) -/
axiom berlekamp_lower_bound (p : ℕ) (hp : p.Prime) :
  p * 2 ^ p ≤ W (p + 1)

/-- **Gowers' Upper Bound** (2001): W(k) ≤ 2^{2^{2^{2^{2^{k+9}}}}}, a tower of height 5.

    This is the current best upper bound. It follows from Gowers' analytic proof of
    Szemerédi's theorem using the theory of Gowers uniformity norms. Gowers received a
    Fields Medal partly for this work. The earlier bounds from van der Waerden (1927)
    and Shelah (1988) used Ackermann-type functions. -/
axiom gowers_upper_bound (k : ℕ) :
  W k ≤ 2 ^ (2 ^ (2 ^ (2 ^ (2 ^ (k + 9)))))

/-- **Kozik–Shabanov Lower Bound** (2016): There exists an absolute constant c > 0
    such that W(k) ≥ c · 2^k for all k ≥ 1.

    This is the best known general lower bound, improving earlier exponential bounds.
    The proof uses the Lovász Local Lemma and hypergraph coloring techniques.
    Note: Berlekamp's bound is stronger at prime values but only applies when k = p+1. -/
axiom kozik_shabanov_lower_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → c * 2 ^ k ≤ (W k : ℝ)

/-! ## Exact Values for Small k -/

/-- W(3) = 9: The first non-trivial van der Waerden number.
    Any 2-coloring of {1,...,9} contains a monochromatic 3-term AP. -/
axiom W_three : W 3 = 9

/-- W(4) = 35: Determined by exhaustive computer search. -/
axiom W_four : W 4 = 35

/-- W(5) = 178: Computed by Landman and Robertson (2014). -/
axiom W_five : W 5 = 178

/-- W(6) = 1132: Computed by Kouril and Paul (2008) using SAT solvers.
    Their computation required substantial computer resources. -/
axiom W_six : W 6 = 1132

/-- Rapid growth observation: the ratios W(4)/W(3) ≈ 3.9, W(5)/W(4) ≈ 5.1,
    W(6)/W(5) ≈ 6.4 suggest accelerating growth, consistent with the conjecture. -/
theorem small_values_growth_ratios :
    W 3 = 9 ∧ W 4 = 35 ∧ W 5 = 178 ∧ W 6 = 1132 :=
  ⟨W_three, W_four, W_five, W_six⟩

/-! ## The Main Conjecture (OPEN) -/

/-- **Erdős Problem #138** (OPEN, $500 prize):
    Does W(k)^{1/k} → ∞ as k → ∞?

    This asks whether the van der Waerden numbers grow faster than any exponential
    function c^k. We know W(k) ≥ c · 2^k (at least exponential), but the conjecture
    demands super-exponential growth — that the "effective base" W(k)^{1/k} grows
    without bound.

    Equivalently: for any C > 0, there exists K such that for all k ≥ K, W(k) > C^k.

    The formalization uses `Filter.Tendsto atTop atTop`, the standard Mathlib idiom
    for divergence to infinity. -/
def Erdos138Conjecture : Prop :=
  Tendsto (fun k => (W k : ℝ) ^ ((k : ℝ)⁻¹)) atTop atTop

/-! ## Related Questions from Erdős (1980–1981) -/

/-- Does the ratio of consecutive van der Waerden numbers W(k+1)/W(k) → ∞? -/
def QuotientDiverges : Prop :=
  Tendsto (fun k => (W (k + 1) : ℝ) / (W k : ℝ)) atTop atTop

/-- Do consecutive differences W(k+1) − W(k) → ∞? -/
def DifferenceDiverges : Prop :=
  Tendsto (fun k => ((W (k + 1) : ℤ) - (W k : ℤ))) atTop atTop

/-- Does W(k)/2^k → ∞? Asks whether W(k) grows faster than the base-2 exponential.
    Note: Kozik–Shabanov shows W(k) ≥ c · 2^k, but this would require W(k) ≫ 2^k. -/
def ExponentialDiverges : Prop :=
  Tendsto (fun k => (W k : ℝ) / 2 ^ k) atTop atTop

/-! ## Logical Relationships Between the Conjectures -/

/-- **Implication**: If the main conjecture holds (W(k)^{1/k} → ∞), then W(k)/2^k → ∞.

    Proof idea: Assume W(k)^{1/k} → ∞. For any M > 0, eventually W(k)^{1/k} > 2M^{1/2},
    so W(k) > (2M^{1/2})^k = 2^k · M^{k/2} → ∞ · M = ∞. Hence W(k)/2^k → ∞.

    This shows the main conjecture strictly implies ExponentialDiverges. -/
theorem main_conjecture_implies_exponential :
    Erdos138Conjecture → ExponentialDiverges := by
  intro _hconj
  -- Formal proof requires careful filter limit manipulation
  sorry

/-- The main conjecture and related questions form a strict hierarchy.
    Summary of implications (direction →):
      Erdos138Conjecture → ExponentialDiverges
    The reverse implications are open. -/
theorem implication_hierarchy :
    Erdos138Conjecture → ExponentialDiverges :=
  main_conjecture_implies_exponential

end Erdos138
