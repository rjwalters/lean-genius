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
  unfold partialInverse
  apply Partrec.rfind
  apply Computable.partrec
  -- The predicate `fun (m, n) => decide (g n = m)` is computable: `g` is computable and
  -- nat-equality is primitive recursive (`Primrec.eq.decide`), composed via `Computable₂.comp`.
  have heq : Computable₂ (fun a b : ℕ => decide (a = b)) :=
    Primrec₂.to_comp (Primrec.eq.decide)
  exact Computable₂.comp heq (hg.comp Computable.snd) Computable.fst

/-- The partial inverse returns the correct preimage.
    If n ∈ partialInverse g m, then g n = m. -/
lemma partialInverse_spec {g : ℕ → ℕ} (_hg_inj : Injective g)
    {m n : ℕ} (h : n ∈ partialInverse g m) : g n = m := by
  unfold partialInverse at h
  -- `Nat.rfind_spec` returns membership `true ∈ p n`; simp normalizes
  -- `true ∈ ↑(decide (g n = m))` to `g n = m`.
  simpa using Nat.rfind_spec h

/-- If m is in the range of g, the partial inverse is defined at m. -/
lemma partialInverse_dom {g : ℕ → ℕ} {m : ℕ} (hm : ∃ k, g k = m) :
    (partialInverse g m).Dom := by
  unfold partialInverse
  obtain ⟨k, hk⟩ := hm
  -- Pin the `rfind_min'` witness index to `k` by supplying `decide (g k = m) = true`
  -- explicitly (leaving it to unification fails: the witness stays a metavariable).
  obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun j => decide (g j = m))
    (show decide (g k = m) = true by simp [hk])
  exact Part.dom_iff_mem.mpr ⟨n, hn⟩

end SchroederBernsteinOQ03.Aristotle
