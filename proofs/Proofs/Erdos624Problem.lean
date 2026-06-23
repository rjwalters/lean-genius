/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bcd867e5-0c83-43e3-bc92-cce059fca666

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem covering_lower_bound (X : Finset α) (f : Finset α → α) (H : ℕ)
    (hf : IsCoveringFunction X f H) (hX : X.Nonempty) :
    2 ^ H ≥ X.card

- theorem coveringNumber_ge_log (X : Finset α) (hX : X.Nonempty) :
    coveringNumber X ≥ Nat.clog 2 X.card
-/

/-
  Erdős Problem #624: Covering Properties of Subset Functions

  Source: https://erdosproblems.com/624
  Status: OPEN

  Statement:
  Let X be a finite set of size n and let H(n) be the minimum integer such that
  there exists a function f : 𝒫(X) → X with the property that for every Y ⊆ X
  with |Y| ≥ H(n), we have {f(A) : A ⊆ Y} = X.

  Prove that H(n) - log₂(n) → ∞.

  Known Bounds (Erdős-Hajnal 1968):
  - log₂(n) ≤ H(n) < log₂(n) + (3 + o(1)) log₂(log₂(n))

  Weaker Statement:
  For n = 2^k, prove H(n) ≥ k + 1. (This remains open!)

  Related Results:
  - Alon gave an elementary proof of the weaker statement using pigeonhole
  - Alon proved: there exists c > 0 such that for any f, some Y of size k
    has |{f(A) : A ⊆ Y}| < (1 - c) · 2^k
  - Alon constructed f where for |Y| = k, |{f(A) : A ⊆ Y}| > 2^k / 4

  References:
  - [ErHa68] Erdős, Hajnal (1968)
  - [Er99] Erdős (1999)
-/

import Mathlib


open Finset Set

namespace Erdos624

variable {α : Type*} [DecidableEq α]

/- ## Core Definitions -/

/-- The image of f restricted to subsets of Y.
    This is {f(A) : A ⊆ Y}. -/
def subsetImage (f : Finset α → α) (Y : Finset α) : Finset α :=
  (Y.powerset).image f

/-- A function f : 𝒫(X) → X is H-covering if for every Y ⊆ X with |Y| ≥ H,
    the image {f(A) : A ⊆ Y} equals X. -/
def IsCoveringFunction (X : Finset α) (f : Finset α → α) (H : ℕ) : Prop :=
  ∀ Y : Finset α, Y ⊆ X → Y.card ≥ H → subsetImage f Y = X

/-- H(X) is the minimum H such that some H-covering function exists. -/
noncomputable def coveringNumber (X : Finset α) : ℕ :=
  sInf { H : ℕ | ∃ f : Finset α → α, IsCoveringFunction X f H }

/- ## Basic Properties -/

/-- The number of subsets of Y is 2^|Y|. -/
theorem card_powerset_eq (Y : Finset α) : Y.powerset.card = 2 ^ Y.card :=
  Finset.card_powerset Y

/-- The subset image has at most 2^|Y| elements. -/
theorem subsetImage_card_le (f : Finset α → α) (Y : Finset α) :
    (subsetImage f Y).card ≤ 2 ^ Y.card := by
  unfold subsetImage
  calc (Y.powerset.image f).card
      ≤ Y.powerset.card := Finset.card_image_le
    _ = 2 ^ Y.card := card_powerset_eq Y

/- ## Lower Bound: H(n) ≥ log₂(n) -/

/-- If f is H-covering for X, then 2^H ≥ |X|.
    This gives H ≥ log₂|X|. -/
theorem covering_lower_bound (X : Finset α) (f : Finset α → α) (H : ℕ)
    (hf : IsCoveringFunction X f H) (hX : X.Nonempty) :
    2 ^ H ≥ X.card := by
  -- Take Y = any subset of X with |Y| = H (if H ≤ |X|)
  -- Then {f(A) : A ⊆ Y} = X has |X| elements
  -- But {f(A) : A ⊆ Y} has at most 2^|Y| = 2^H elements
  -- So 2^H ≥ |X|
  have h_covering : ∀ Y : Finset α, Y ⊆ X → Y.card ≥ H → X.card ≤ 2 ^ Y.card := by
    intro Y hy hY
    have h_card_image : (subsetImage f Y).card ≤ 2 ^ Y.card := by
      exact?;
    exact le_trans ( by rw [ hf Y hy hY ] ) h_card_image;
  by_cases h : H ≤ X.card;
  · -- Let's choose Y to be a subset of X with cardinality H.
    obtain ⟨Y, hY⟩ : ∃ Y ⊆ X, Y.card = H := by
      exact?;
    grind;
  · exact le_trans ( le_of_lt ( Nat.lt_of_not_ge h ) ) ( le_of_lt ( Nat.recOn H ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ) )

/-- H(n) ≥ ⌈log₂(n)⌉ for any set of size n. -/
theorem coveringNumber_ge_log (X : Finset α) (hX : X.Nonempty) :
    coveringNumber X ≥ Nat.clog 2 X.card := by
  refine' le_csInf _ _;
  · refine' ⟨ X.card + 1, _ ⟩;
    refine' ⟨ fun A => if hA : A.Nonempty then Classical.choose hA else Classical.choose hX, fun Y hy hY => _ ⟩;
    exact absurd hY ( not_le_of_gt ( Nat.lt_succ_of_le ( Finset.card_le_card hy ) ) );
  · intro b hb
    obtain ⟨f, hf⟩ := hb
    have h_card : 2 ^ b ≥ X.card := by
      exact?;
    exact Nat.le_trans ( Nat.clog_mono_right _ h_card ) ( by rw [ Nat.clog_pow ] ; norm_num )

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos624.erdos_hajnal_upper_bound', 'harmonicSorry345943']-/
/- ## Upper Bound Construction

For the upper bound, we need to construct a covering function.
The Erdős-Hajnal construction achieves H < log₂(n) + (3+o(1))log₂log₂(n). -/

/-- There exists a covering function with H < log₂(n) + 3·log₂(log₂(n)) for large n. -/
axiom erdos_hajnal_upper_bound :
    ∀ n : ℕ, n ≥ 4 → ∀ X : Finset ℕ, X.card = n →
      ∃ f : Finset ℕ → ℕ, ∃ H : ℕ,
        IsCoveringFunction X f H ∧
        H < Nat.log 2 n + 3 * Nat.log 2 (Nat.log 2 n) + 10

/- ## The Main Conjecture -/

/-- **Erdős Problem #624 (OPEN)**:
    H(n) - log₂(n) → ∞ as n → ∞.

    Formally: for any constant C, there exists N such that for all n > N,
    H(n) > log₂(n) + C. -/
def MainConjecture : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ n > N, ∀ X : Finset ℕ, X.card = n →
    coveringNumber X > Nat.log 2 n + C

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry535582', 'Erdos624.erdos_624_open']-/
/-- The conjecture remains open. -/
axiom erdos_624_open : MainConjecture

/- ## Weaker Statement (Also Open) -/

/-- Weaker conjecture: For n = 2^k, H(n) ≥ k + 1.
    This is equivalent to saying no function achieves H = k = log₂(n). -/
def WeakerConjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → ∀ X : Finset ℕ, X.card = 2^k →
    coveringNumber X ≥ k + 1

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos624.weaker_conjecture_open', 'harmonicSorry813431']-/
/-- The weaker statement also remains open! -/
axiom weaker_conjecture_open : WeakerConjecture

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos624.alon_upper_bound', 'harmonicSorry187178']-/
/- ## Alon's Results -/

/-- **Alon's Theorem**: There exists c > 0 such that for any f : 𝒫(X) → X
    with |X| = 2^k, there exists Y ⊆ X with |Y| = k such that
    |{f(A) : A ⊆ Y}| < (1 - c) · 2^k.

    This shows no function can be "too good" at covering. -/
axiom alon_upper_bound :
    ∃ c : ℝ, c > 0 ∧ c < 1 ∧
      ∀ k : ℕ, k ≥ 1 → ∀ X : Finset ℕ, X.card = 2^k →
        ∀ f : Finset ℕ → ℕ,
          ∃ Y : Finset ℕ, Y ⊆ X ∧ Y.card = k ∧
            (subsetImage f Y).card < (1 - c) * 2^k

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos624.alon_lower_construction', 'harmonicSorry148500']-/
/-- **Alon's Construction**: There exists f such that for all Y with |Y| = k,
    |{f(A) : A ⊆ Y}| > 2^k / 4.

    This shows the image can be at least 1/4 of X. -/
axiom alon_lower_construction :
    ∀ k : ℕ, k ≥ 2 → ∀ X : Finset ℕ, X.card = 2^k →
      ∃ f : Finset ℕ → ℕ,
        ∀ Y : Finset ℕ, Y ⊆ X → Y.card = k →
          (subsetImage f Y).card > 2^k / 4

/- ## Summary

**Erdős Problem #624** concerns the covering number H(n): the minimum size
such that some function f : 𝒫(X) → X has {f(A) : A ⊆ Y} = X for all Y of
size at least H(n).

**Known**:
- log₂(n) ≤ H(n) < log₂(n) + O(log log n)  [Erdős-Hajnal 1968]
- The gap H(n) - log₂(n) is at least Ω(1)    [Alon]

**Open**:
- Prove H(n) - log₂(n) → ∞
- Even proving H(2^k) ≥ k + 1 is open!

**Tags**: Combinatorics, Set Theory, Covering Problems
-/

end Erdos624