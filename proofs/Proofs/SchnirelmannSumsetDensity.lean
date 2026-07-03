/-
  Schnirelmann's sumset density inequality  (weak-goldbach-oq-01, Key Lemma)

  The crux missing lemma behind `schnirelmann_basis_theorem` in
  `Proofs/WeakGoldbach.lean` (currently an `axiom`) and a flagged Mathlib gap
  (`Mathlib/Combinatorics/Schnirelmann.lean`, module TODO: "Prove Schnirelmann's
  theorem and Mann's theorem"):

    for sets A, B ⊆ ℕ with 0 ∈ A and 0 ∈ B,
        σ(A + B) ≥ σ(A) + σ(B) − σ(A)·σ(B)
    equivalently  1 − σ(A + B) ≤ (1 − σ(A))·(1 − σ(B)).

  Here `σ = schnirelmannDensity` (Mathlib) and `A + B` is the pointwise sumset
  (`Set.image2 (· + ·)`).  Nathanson, *Additive Number Theory*, Theorem 7.4:
  fix n; for each a ∈ A ∩ [0,n] the interval after a is covered by a translate of
  B, so the integers in [1,n] not in A+B inject into (Bᶜ ∩ [1, ·]); counting gives
      #((A+B) ∩ (0,n]) ≥ #(A ∩ (0,n]) + σ(B)·(n − #(A ∩ (0,n])),
  then divide by n and pass to the infimum via `le_schnirelmannDensity_iff`.

  Iterating this inequality (`1 − σ(A^{⊕k}) ≤ (1 − σ(A))^k → 0`) yields a finite
  sumset of density > 1/2, and a density-> 1/2 set containing 0 is an additive
  basis of order 2 — which discharges `schnirelmann_basis_theorem`.  This file
  isolates the sumset inequality, the hard combinatorial heart of that program.
-/
import Mathlib

open Finset

open scoped Pointwise

namespace SchnirelmannSumset

/-- Every element of `A` (with `0 ∈ B`) lies in the sumset `A + B`, via `a = a + 0`.
    A convenience fact for the density comparison. -/
theorem subset_sumset_left {A B : Set ℕ} (hB : (0 : ℕ) ∈ B) : A ⊆ A + B := by
  intro a ha
  exact ⟨a, ha, 0, hB, by simp⟩

/-- Every element of `B` (with `0 ∈ A`) lies in the sumset `A + B`, via `b = 0 + b`. -/
theorem subset_sumset_right {A B : Set ℕ} (hA : (0 : ℕ) ∈ A) : B ⊆ A + B := by
  intro b hb
  exact ⟨0, hA, b, hb, by simp⟩

/-- The sumset density dominates each summand's density (with `0` in the other
    set): `σ(A) ≤ σ(A + B)`.  A fully-proved, unconditional special case of the
    Schnirelmann inequality — it is what remains after dropping the `σ(B)` gain,
    obtained from `A ⊆ A + B` and monotonicity of density under inclusion. -/
theorem schnirelmannDensity_le_sumset_left
    (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ A + B)]
    (hB : (0 : ℕ) ∈ B) :
    schnirelmannDensity A ≤ schnirelmannDensity (A + B) :=
  schnirelmannDensity_le_of_subset (subset_sumset_left hB)

/-- Symmetric companion: `σ(B) ≤ σ(A + B)` when `0 ∈ A`. -/
theorem schnirelmannDensity_le_sumset_right
    (A B : Set ℕ) [DecidablePred (· ∈ B)] [DecidablePred (· ∈ A + B)]
    (hA : (0 : ℕ) ∈ A) :
    schnirelmannDensity B ≤ schnirelmannDensity (A + B) :=
  schnirelmannDensity_le_of_subset (subset_sumset_right hA)

/-- **Schnirelmann's sumset density inequality.**  For sets `A, B ⊆ ℕ` with
    `0 ∈ A` and `0 ∈ B`,
      `σ(A) + σ(B) − σ(A)·σ(B) ≤ σ(A + B)`.
    This is the key combinatorial input to Schnirelmann's theorem: iterating it
    drives the density of the iterated sumset to `1`, making `A` an additive
    basis of bounded order. -/
theorem schnirelmann_sumset_density
    (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : (0 : ℕ) ∈ A) (hB : (0 : ℕ) ∈ B) :
    schnirelmannDensity A + schnirelmannDensity B
        - schnirelmannDensity A * schnirelmannDensity B
      ≤ schnirelmannDensity (A + B) := by
  sorry

/-- Equivalent multiplicative form of the sumset inequality:
    `1 − σ(A + B) ≤ (1 − σ(A))·(1 − σ(B))`. -/
theorem one_sub_schnirelmann_sumset_le
    (A B : Set ℕ) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ A + B)] (hA : (0 : ℕ) ∈ A) (hB : (0 : ℕ) ∈ B) :
    1 - schnirelmannDensity (A + B)
      ≤ (1 - schnirelmannDensity A) * (1 - schnirelmannDensity B) := by
  have h := schnirelmann_sumset_density A B hA hB
  ring_nf
  ring_nf at h
  linarith [h]

end SchnirelmannSumset
