/-
  Aristotle targets for SchroederBernsteinOQ03 (Myhill's Isomorphism Theorem)
  Routine supporting lemmas for automated proof search.
  See SchroederBernsteinOQ03.lean for the main formalization.

  Three supporting lemmas for the partial inverse infrastructure:
  - partialInverse_partrec: partial inverse of a computable function is Partrec
  - partialInverse_spec: rfind recovers the correct preimage
  - partialInverse_dom: partial inverse is defined when preimage exists

  The main theorem (myhill_isomorphism hard direction) requires ~200 lines
  of back-and-forth priority construction and is NOT targeted here.
-/
import Mathlib.Computability.Reduce
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Function Computable

namespace SchroederBernsteinOQ03.Aristotle

/-- Partial inverse via rfind: g⁻¹(m) is the unique n with g(n) = m. -/
def partialInverse (g : ℕ → ℕ) : ℕ →. ℕ :=
  fun m => (Nat.rfind fun n => decide (g n = m))

/-- The partial inverse of a computable function is partial recursive.
    Follows from Partrec.rfind applied to the computable decidable predicate. -/
lemma partialInverse_partrec {g : ℕ → ℕ} (hg : Computable g) :
    Partrec (partialInverse g) := by
  sorry

/-- The partial inverse returns the correct preimage.
    If n ∈ partialInverse g m, then g n = m. -/
lemma partialInverse_spec {g : ℕ → ℕ} (hg_inj : Injective g)
    {m n : ℕ} (h : n ∈ partialInverse g m) : g n = m := by
  unfold partialInverse at h
  exact of_decide_eq_true (Nat.rfind_spec h)

/-- If m is in the range of g, the partial inverse is defined at m. -/
lemma partialInverse_dom {g : ℕ → ℕ} {m : ℕ} (hm : ∃ k, g k = m) :
    (partialInverse g m).Dom := by
  unfold partialInverse
  obtain ⟨k, hk⟩ := hm
  obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun n => decide (g n = m)) (by simp [hk])
  exact Part.dom_iff_mem.mpr ⟨n, hn⟩

end SchroederBernsteinOQ03.Aristotle
