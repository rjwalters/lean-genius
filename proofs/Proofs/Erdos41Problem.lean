/-
  Erdős Problem #41: B_h Sequences and Density Bounds

  Source: https://erdosproblems.com/41
  Status: PARTIALLY SOLVED
  Prize: $500 (for h=3 case)

  Statement:
  Let A ⊆ ℕ be an infinite set such that the h-element sums are all distinct
  (aside from trivial coincidences). Is it true that
    liminf |A ∩ {1,...,N}| / N^(1/h) = 0 ?

  History:
  - Erdős: Proved for h=2 (Sidon sets / B_2 sequences)
  - Nash (1989): Proved for h=4
  - Chen (1996): Proved for all even h

  Status by h:
  - h=2: SOLVED (Erdős)
  - h=3: OPEN ($500 prize)
  - h=4: SOLVED (Nash 1989)
  - h≥4 even: SOLVED (Chen 1996)

  Reference: Guy's collection [Gu04], Problem C11
-/

import Mathlib

open Set Filter Finset
open scoped Topology

namespace Erdos41

/-! ## Core Definitions -/

/-- A set A has the B_h property if all h-element subset sums are distinct.
    Also known as: the "n-tuple condition" or "h-fold Sidon property".

    Formally: for any two h-element subsets I, J ⊆ A, if ∑I = ∑J then I = J.
-/
def IsBhSet (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ (I J : Finset ℕ),
    ↑I ⊆ A → ↑J ⊆ A → I.card = h → J.card = h →
    I.sum id = J.sum id → I = J

/-- The counting function: |A ∩ {1,...,N}| -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 N).ncard

/-- The density ratio: |A ∩ {1,...,N}| / N^(1/h) -/
noncomputable def densityRatio (A : Set ℕ) (N : ℕ) (h : ℕ) : ℝ :=
  (countingFn A N : ℝ) / (N : ℝ) ^ (1 / h : ℝ)

/-! ## The General Conjecture -/

/-- **Erdős's General B_h Conjecture**:

    For all h ≥ 2, if A is an infinite B_h set, then
    liminf |A ∩ {1,...,N}| / N^(1/h) = 0.

    This says B_h sets must have "density zero at order 1/h" infinitely often.
-/
def ErdosBhConjecture (h : ℕ) : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsBhSet A h →
    liminf (fun N => densityRatio A N h) atTop = 0

/-! ## Solved Cases -/

/-- **Erdős's Theorem (h=2)**: Sidon sets have density o(N^(1/2)).

    If A is an infinite B_2 set (all pairwise sums distinct), then
    liminf |A ∩ {1,...,N}| / √N = 0.

    This is the classical result that motivated the general conjecture.
-/
axiom erdos_b2_theorem : ErdosBhConjecture 2

/-- **Nash's Theorem (1989)**: B_4 sets have density o(N^(1/4)).

    Nash proved the conjecture for h=4 using Fourier-analytic methods.
-/
axiom nash_b4_theorem : ErdosBhConjecture 4

/-- **Chen's Theorem (1996)**: B_h sets have density o(N^(1/h)) for all even h.

    Chen extended Nash's techniques to handle all even values of h.
-/
axiom chen_even_h_theorem : ∀ h : ℕ, h ≥ 2 → Even h → ErdosBhConjecture h

/-- Combining Chen's result with Erdős's original theorem. -/
theorem solved_even_cases (h : ℕ) (hge : h ≥ 2) (heven : Even h) :
    ErdosBhConjecture h :=
  chen_even_h_theorem h hge heven

/-! ## The Open Case -/

/-- **Erdős Problem #41 (h=3)**: OPEN ($500 prize)

    The h=3 case remains unsolved. Is it true that for infinite B_3 sets,
    liminf |A ∩ {1,...,N}| / N^(1/3) = 0 ?

    This is the main open problem, as odd h (except h=2 which is even in spirit)
    resists the Fourier-analytic techniques used for even h.
-/
def Erdos41Conjecture : Prop := ErdosBhConjecture 3

/-- The conjecture is decidable classically (either true or false). -/
theorem erdos_41_classical : Erdos41Conjecture ∨ ¬Erdos41Conjecture :=
  Classical.em _

/-! ## Connection to Sidon Sets -/

/-- A B_2 set is exactly a Sidon set (all pairwise sums distinct). -/
def IsSidonSet (A : Set ℕ) : Prop := IsBhSet A 2

/-- Sidon sets satisfy Erdős's density bound. -/
theorem sidon_density_bound (A : Set ℕ) (hinf : A.Infinite) (hsidon : IsSidonSet A) :
    liminf (fun N => densityRatio A N 2) atTop = 0 :=
  erdos_b2_theorem A hinf hsidon

/-! ## Examples -/

/-- The empty set is vacuously a B_h set for any h. -/
theorem empty_is_bh (h : ℕ) : IsBhSet ∅ h := by
  intro I J hI hJ _ _ _
  simp only [subset_empty_iff, coe_eq_empty] at hI hJ
  rw [hI, hJ]

/-- A singleton is a B_h set for any h > 1. -/
theorem singleton_is_bh (a : ℕ) (h : ℕ) (hh : h > 1) : IsBhSet {a} h := by
  intro I J hI hJ hIcard hJcard _
  -- If I and J are h-element subsets of {a} with h > 1, impossible
  have hI_sub : I ⊆ {a} := by exact_mod_cast hI
  have hJ_sub : J ⊆ {a} := by exact_mod_cast hJ
  have hI_card_le : I.card ≤ 1 := by
    calc I.card ≤ ({a} : Finset ℕ).card := card_le_card hI_sub
      _ = 1 := Finset.card_singleton a
  omega

/-- Powers of 2 form a B_2 (Sidon) set: {1, 2, 4, 8, ...} -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2^k}

/-- Key lemma: sums of two distinct powers of 2 determine them uniquely.
    If 2^a + 2^b = 2^c + 2^d (with a ≤ b, c ≤ d), then {a,b} = {c,d}.

    This follows from the uniqueness of binary representation.
-/
axiom powers_of_two_sidon_property :
  ∀ a b c d : ℕ, a ≤ b → c ≤ d →
    2^a + 2^b = 2^c + 2^d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-! ## Summary of Known Results -/

/-- Summary: What's proven about B_h density bounds.

    | h | Status | Proof |
    |---|--------|-------|
    | 2 | SOLVED | Erdős (classical) |
    | 3 | OPEN   | $500 prize |
    | 4 | SOLVED | Nash 1989 |
    | 5 | OPEN   | - |
    | 6 | SOLVED | Chen 1996 |
    | even h≥2 | SOLVED | Chen 1996 |
    | odd h≥3 | OPEN | - |
-/
theorem summary_even_h_solved (h : ℕ) (hge : h ≥ 2) (heven : Even h) :
    ErdosBhConjecture h :=
  chen_even_h_theorem h hge heven

end Erdos41
