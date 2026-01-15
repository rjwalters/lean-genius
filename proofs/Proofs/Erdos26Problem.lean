/-
  Erdős Problem #26: Thick Sequences and Behrend Sets

  Source: https://erdosproblems.com/26
  Status: DISPROVED (Ruzsa counterexample)

  Statement:
  Let A ⊂ ℕ be infinite such that Σ(1/a) = ∞ (a "thick" sequence).
  Must there exist some k ≥ 1 such that almost all integers have a divisor
  of the form a + k for some a ∈ A?

  Answer: NO

  Background:
  - A sequence is "thick" if the sum of its reciprocals diverges
  - A sequence is "Behrend" if almost all integers are multiples of its elements
  - Davenport-Erdős (1951): Σ(1/a) = ∞ for every Behrend sequence

  Counterexample:
  - Ruzsa: Constructed a sequence where no shift A + k is Behrend
  - Van Doorn: Modified to make the reciprocal sum infinite

  The answer being NO means that even with thick sequences, we cannot
  guarantee any shift covers almost all integers as divisors.

  Weaker Variant (OPEN):
  Tenenbaum asked: For every ε > 0, does some k = k(ε) exist such that
  at least (1 - ε) density of integers have a divisor of the form a + k?

  References:
  - Erdős, P. & Tenenbaum, G. (original problem formulation)
  - Davenport, H. & Erdős, P. (1951). On the density of sequences
  - Ruzsa, I. Z. (counterexample)
  - Tenenbaum, G. (2019). "Some of Erdős' unconventional problems"
    arXiv:1908.00488
-/

import Mathlib

open Set Filter BigOperators Nat Real

namespace Erdos26

/-! ## Natural Density -/

open Classical in
/-- The partial density of a set S up to n: |S ∩ [1,n]| / n -/
noncomputable def partialDensity (S : Set ℕ) (n : ℕ) : ℝ :=
  ((Finset.range n).filter (· ∈ S)).card / n

/-- A set S has natural density d if partialDensity S n → d as n → ∞ -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (partialDensity S) atTop (nhds d)

/-- The lower density of a set S -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (partialDensity S) atTop

/-! ## Core Definitions -/

/-- A sequence A is "thick" if the sum of reciprocals diverges: Σ(1/A(i)) = ∞.
    Equivalently, the reciprocal sequence is not summable. -/
def IsThick {ι : Type*} (A : ι → ℕ) : Prop :=
  ¬Summable (fun i => (1 : ℝ) / A i)

/-- The set of multiples of a sequence: {n * A(i) | n ∈ ℕ, i ∈ ι}. -/
def MultiplesOf {ι : Type*} (A : ι → ℕ) : Set ℕ :=
  range fun (p : ℕ × ι) => p.1 * A p.2

/-- A sequence is "Behrend" if almost all integers are multiples of some element.
    Formally, the set of multiples has natural density 1. -/
def IsBehrend {ι : Type*} (A : ι → ℕ) : Prop :=
  HasNaturalDensity (MultiplesOf A) 1

/-- A sequence is "weakly Behrend" with parameter ε if at least (1 - ε) density
    of integers are multiples of some element. -/
def IsWeaklyBehrend {ι : Type*} (A : ι → ℕ) (ε : ℝ) : Prop :=
  1 - ε ≤ lowerDensity (MultiplesOf A)

/-! ## Basic Properties of Thick Sequences -/

/-- Any finite sequence is not thick (finite sum converges). -/
theorem not_isThick_of_finite {ι : Type*} [Finite ι] (A : ι → ℕ) : ¬IsThick A := by
  simpa [IsThick] using Summable.of_finite

/-- A geometric sequence r^n with r > 1 is not thick.
    Proof: Σ(1/r^n) = 1/(1 - 1/r) < ∞ for r > 1. -/
axiom not_isThick_geometric {r : ℕ} (hr : r > 1) : ¬IsThick fun n : ℕ => r ^ n

/-- A constant positive sequence is thick (harmonic series diverges).
    Proof: Σ(1/r) = ∞ for any fixed r > 0 over infinite index. -/
axiom isThick_const {ι : Type*} [Infinite ι] (r : ℕ) (hr : r > 0) :
    IsThick fun _ : ι => r

/-! ## The Davenport-Erdős Theorem -/

/-- Davenport-Erdős (1951): Every Behrend sequence has divergent reciprocal sum.
    This is a key structural result about the relationship between density
    and reciprocal sums. -/
axiom davenport_erdos_behrend_thick :
  ∀ {ι : Type*} (A : ι → ℕ), (∀ i, A i > 0) → IsBehrend A → IsThick A

/-- Contrapositive: A non-thick sequence with positive elements is not Behrend. -/
theorem not_behrend_of_not_thick {ι : Type*} (A : ι → ℕ)
    (hpos : ∀ i, A i > 0) (h : ¬IsThick A) : ¬IsBehrend A :=
  fun hB => h (davenport_erdos_behrend_thick A hpos hB)

/-! ## The Erdős Conjecture (Problem 26) -/

/-- The Erdős-Tenenbaum conjecture (Problem 26):
    For any thick sequence A, does there exist k ≥ 1 such that
    the shifted sequence A + k is Behrend?

    Here "A + k" means the function i ↦ A(i) + k.
    Being Behrend means almost all integers have a divisor in A + k. -/
def Erdos26Conjecture : Prop :=
  ∀ A : ℕ → ℕ, StrictMono A → IsThick A → ∃ k : ℕ, k ≥ 1 ∧ IsBehrend (A · + k)

/-! ## The Ruzsa Counterexample -/

/-- Ruzsa's counterexample: There exists a strictly increasing sequence A
    such that for all k, the shifted sequence A + k is NOT Behrend.

    The construction uses: n_l ≡ -(k-1) (mod p_k) for all k ≤ l,
    where p_k is the k-th prime. This ensures for any k, the shift A + k
    is not a multiple of p_k often enough. -/
axiom ruzsa_counterexample :
  ∃ A : ℕ → ℕ, StrictMono A ∧ ¬IsThick A ∧ ∀ k : ℕ, ¬IsBehrend (A · + k)

/-- Van Doorn's modification: A thick counterexample.
    Modified Ruzsa's construction to make Σ(1/A(n)) = ∞ while still
    ensuring no shift is Behrend. -/
axiom van_doorn_thick_counterexample :
  ∃ A : ℕ → ℕ, StrictMono A ∧ IsThick A ∧ ∀ k : ℕ, ¬IsBehrend (A · + k)

/-- Erdős Problem #26 is DISPROVED. -/
theorem erdos_26_disproved : ¬Erdos26Conjecture := by
  intro hconj
  obtain ⟨A, hmono, hthick, hno_behrend⟩ := van_doorn_thick_counterexample
  obtain ⟨k, _, hB⟩ := hconj A hmono hthick
  exact hno_behrend k hB

/-! ## Tenenbaum's Weaker Variant (OPEN) -/

/-- Tenenbaum's weaker variant:
    For every ε > 0, does there exist k such that at least (1 - ε) density
    of integers have a divisor in A + k?

    This relaxes "almost all" (density 1) to "most" (density ≥ 1 - ε).
    Status: OPEN as of 2025. -/
def TenenbaumVariant : Prop :=
  ∀ A : ℕ → ℕ, StrictMono A → IsThick A →
    ∀ ε > (0 : ℝ), ∃ k : ℕ, IsWeaklyBehrend (A · + k) ε

/-! ## Supporting Lemmas -/

/-- If 1 ∈ range A, then MultiplesOf A = ℕ (everything is a multiple of 1). -/
theorem multiplesOf_eq_univ {ι : Type*} (A : ι → ℕ) (h : 1 ∈ range A) :
    MultiplesOf A = univ := by
  obtain ⟨i, hi⟩ := h
  ext n
  simp only [MultiplesOf, mem_range, mem_univ, iff_true]
  exact ⟨(n, i), by simp [hi]⟩

/-- If A contains 1, then A is trivially Behrend.
    Proof: MultiplesOf A = ℕ when 1 ∈ A, so density is 1. -/
axiom isBehrend_of_contains_one {ι : Type*} (A : ι → ℕ) (h : 1 ∈ range A) :
    IsBehrend A

/-- A sequence is weakly Behrend with ε ≥ 1 trivially.
    Proof: 1 - ε ≤ 0 ≤ lowerDensity(S) for any S. -/
axiom isWeaklyBehrend_of_ge_one {ι : Type*} (A : ι → ℕ) {ε : ℝ} (hε : 1 ≤ ε) :
    IsWeaklyBehrend A ε

/-- A sequence is not weakly Behrend with ε < 0.
    Proof: 1 - ε > 1 ≥ lowerDensity(S) for any S. -/
axiom not_isWeaklyBehrend_of_neg {ι : Type*} (A : ι → ℕ) {ε : ℝ} (hε : ε < 0) :
    ¬IsWeaklyBehrend A ε

/-! ## Summary

**Problem Status: DISPROVED**

Erdős Problem #26 asked whether, for any thick sequence A, some shift A + k
must be Behrend (i.e., almost all integers have a divisor in A + k).

**Answer: NO** (Ruzsa counterexample, Van Doorn thick variant)

**Key Results:**
1. Davenport-Erdős (1951): Behrend sequences are always thick
2. Ruzsa: Non-thick counterexample where no shift is Behrend
3. Van Doorn: Thick counterexample (Σ(1/a) = ∞) where no shift is Behrend

**The Gap:**
The main theorem (erdos_26_disproved) shows the conjecture fails.
The Van Doorn counterexample provides a thick sequence where no shift
achieves density 1 coverage.

**Open Question:**
Tenenbaum's weaker variant (density ≥ 1 - ε instead of = 1) remains open.

References:
- Erdős, P. & Tenenbaum, G. (original problem)
- Davenport, H. & Erdős, P. (1951). On sequences of positive integers
- Ruzsa, I. Z. (counterexample)
- Tenenbaum, G. (2019). arXiv:1908.00488
-/

end Erdos26
