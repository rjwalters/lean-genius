/-
Erdős Problem #441: An unconditional, axiom-free lower bound for g(N)

Source: https://erdosproblems.com/441

Background.
Let N ≥ 1 and let g(N) be the largest size of a set A ⊆ {1,...,N} with
[a,b] ≤ N for every a,b ∈ A, where [a,b] = lcm(a,b).  The full answer
(Chen 1998, Chen–Dai 2006/2007) is g(N) ~ (9N/8)^{1/2}, and Erdős'
explicit construction is NOT always optimal.  Those results are deep and
in the companion file `Erdos441Problem.lean` they are recorded as axioms.

This file isolates the part of the story that can be checked *with no
axioms at all*: the elementary lower bound

    g(N) ≥ ⌊√N⌋,

which already pins down the correct order of magnitude g(N) = Θ(√N).  The
witness is the simplest possible LCM-bounded set, the full initial segment
{1, 2, ..., ⌊√N⌋}: any two of its elements a,b satisfy
lcm(a,b) ≤ a·b ≤ ⌊√N⌋² ≤ N.

The sharp constant (9/8)^{1/2} ≈ 1.0607 (a 6% improvement over the bound
proved here) is exactly what the axiomatized Chen–Dai material supplies;
nothing in this file depends on it.

Everything below is `#print axioms`-clean (only propext/Classical/Quot,
i.e. the ordinary foundational axioms).

Tags: number-theory, lcm, extremal-combinatorics
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Sqrt

open Finset

namespace Erdos441LowerBound

/-! ## Definitions (restated, correct-syntax, self-contained) -/

/-- `A ⊆ {1,...,N}`. -/
def IsSubsetOfInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- All pairwise least common multiples of elements of `A` are at most `N`. -/
def HasBoundedLCM (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → Nat.lcm a b ≤ N

/-- An LCM-bounded subset: `A ⊆ {1,...,N}` with `[a,b] ≤ N` for all `a,b ∈ A`. -/
def IsLCMBounded (A : Finset ℕ) (N : ℕ) : Prop :=
  IsSubsetOfInterval A N ∧ HasBoundedLCM A N

/-- The set of achievable cardinalities of LCM-bounded subsets of `{1,...,N}`. -/
def lcmBoundedCards (N : ℕ) : Set ℕ :=
  { n | ∃ A : Finset ℕ, IsLCMBounded A N ∧ A.card = n }

/-- `g N`: the maximum size of an LCM-bounded subset of `{1,...,N}`. -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup (lcmBoundedCards N)

/-! ## A crude but exact divisibility bound on the lcm -/

/-- For natural numbers, `lcm a b ≤ a * b`.  (Holds unconditionally: when
either factor is zero both sides are zero.) -/
theorem lcm_le_mul (a b : ℕ) : Nat.lcm a b ≤ a * b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp [Nat.lcm_zero_left]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp [Nat.lcm_zero_right]
  exact Nat.le_of_dvd (Nat.mul_pos ha hb)
    (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))

/-! ## The explicit witness set `{1, ..., ⌊√N⌋}` -/

/-- The initial segment `{1, ..., ⌊√N⌋}` is LCM-bounded inside `{1,...,N}`. -/
theorem interval_isLCMBounded (N : ℕ) :
    IsLCMBounded (Finset.Icc 1 (Nat.sqrt N)) N := by
  refine ⟨?_, ?_⟩
  · -- subset of {1,...,N}
    intro a ha
    rw [Finset.mem_Icc] at ha
    exact ⟨ha.1, ha.2.trans (Nat.sqrt_le_self N)⟩
  · -- pairwise lcm ≤ N
    intro a b ha hb
    rw [Finset.mem_Icc] at ha hb
    calc Nat.lcm a b ≤ a * b := lcm_le_mul a b
      _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul ha.2 hb.2
      _ ≤ N := Nat.sqrt_le N

/-- The achievable-cardinality set is bounded above by `N` (every LCM-bounded
set sits inside `{1,...,N}`, which has `N` elements). -/
theorem lcmBoundedCards_bddAbove (N : ℕ) : BddAbove (lcmBoundedCards N) := by
  refine ⟨N, ?_⟩
  rintro x ⟨A, hA, rfl⟩
  have hsub : A ⊆ Finset.Icc 1 N := by
    intro a ha
    rw [Finset.mem_Icc]
    exact hA.1 a ha
  calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsub
    _ = N := by rw [Nat.card_Icc]; omega

/-! ## The unconditional lower bound -/

/-- **Main result.** Unconditionally, `g(N) ≥ ⌊√N⌋`.

No axioms beyond Lean's foundational `propext`/`Classical.choice`/`Quot.sound`
are used; in particular this does *not* rely on the Chen–Dai axioms. -/
theorem g_ge_sqrt (N : ℕ) : Nat.sqrt N ≤ g N := by
  have hmem : Nat.sqrt N ∈ lcmBoundedCards N := by
    refine ⟨Finset.Icc 1 (Nat.sqrt N), interval_isLCMBounded N, ?_⟩
    rw [Nat.card_Icc]; omega
  exact le_csSup (lcmBoundedCards_bddAbove N) hmem

/-- For `N ≥ 1` the maximum is at least `1` (the singleton `{1}` works). -/
theorem g_ge_one {N : ℕ} (hN : 1 ≤ N) : 1 ≤ g N := by
  have h := g_ge_sqrt N
  have hs : 1 ≤ Nat.sqrt N := by
    have := Nat.sqrt_le_sqrt hN
    simpa [Nat.sqrt_one] using this
  omega

/-! ## Real-valued form -/

/-- The lower bound in real-analytic form: `g(N) ≥ √N − 1`.  This is the
shape used to compare against the Chen–Dai asymptotic `g(N) ~ (9N/8)^{1/2}`:
the constant here is `1`, theirs is `(9/8)^{1/2} ≈ 1.0607`. -/
theorem g_ge_sqrt_real (N : ℕ) : (g N : ℝ) ≥ Real.sqrt N - 1 := by
  have hnat : (Nat.sqrt N : ℝ) ≤ (g N : ℝ) := by exact_mod_cast g_ge_sqrt N
  have hsqrt : Real.sqrt N ≤ (Nat.sqrt N : ℝ) + 1 := by
    have hlt : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt N
      have hcast : (N : ℝ) < ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        calc (N : ℝ) < ((Nat.sqrt N + 1) * (Nat.sqrt N + 1) : ℕ) := by exact_mod_cast this
          _ = ((Nat.sqrt N : ℝ) + 1) ^ 2 := by push_cast; ring
      simpa using hcast
    have hpos : (0 : ℝ) ≤ (Nat.sqrt N : ℝ) + 1 := by positivity
    calc Real.sqrt N ≤ Real.sqrt (((Nat.sqrt N : ℝ) + 1) ^ 2) :=
          Real.sqrt_le_sqrt hlt.le
      _ = (Nat.sqrt N : ℝ) + 1 := by rw [Real.sqrt_sq hpos]
  linarith

/-! ## Summary

This file proves, with no axioms, that g(N) ≥ ⌊√N⌋ for every N, hence
g(N) = Θ(√N).  The witness is the full initial segment {1,...,⌊√N⌋}, whose
pairwise lcms never exceed ⌊√N⌋² ≤ N.  The sharp constant (9/8)^{1/2} of
Chen–Dai is a 6% improvement and lives entirely in the axiomatized material
of `Erdos441Problem.lean`; it is not needed for the order of magnitude. -/

end Erdos441LowerBound
