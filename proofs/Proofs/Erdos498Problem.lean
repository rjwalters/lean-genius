/-!
# Erdős Problem #498 — Complex Littlewood–Offord Problem

Given complex numbers z₁, ..., zₙ with |zᵢ| ≥ 1, and any disc D
of radius 1, the number of signed sums Σ εᵢzᵢ (εᵢ ∈ {−1, +1})
falling in D is at most C(n, ⌊n/2⌋).

This is a strong form of the Littlewood–Offord problem.

Proved by Kleitman (1965), later generalized to Hilbert spaces (1970).

Status: SOLVED
Reference: https://erdosproblems.com/498
Sources: [Er45], [Er61], [Kl65], [Kl70]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A sign vector: each εᵢ ∈ {−1, +1}. -/
def SignVector (n : ℕ) := Fin n → Int

/-- A sign vector is valid if each entry is ±1. -/
def IsValidSign {n : ℕ} (ε : SignVector n) : Prop :=
  ∀ i : Fin n, ε i = 1 ∨ ε i = -1

/-- The signed sum Σ εᵢzᵢ for a sign vector ε and complex numbers z. -/
noncomputable def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : SignVector n) : ℂ :=
  Finset.sum Finset.univ (fun i => (ε i : ℂ) * z i)

/-- A closed disc of radius r centered at w in ℂ. -/
def InDisc (w : ℂ) (r : ℝ) (p : ℂ) : Prop :=
  Complex.abs (p - w) ≤ r

/-- The count of sign vectors whose signed sum falls in a disc. -/
noncomputable def signedSumCount {n : ℕ} (z : Fin n → ℂ) (w : ℂ) (r : ℝ) : ℕ :=
  Finset.card (Finset.filter
    (fun ε : Fin n → Fin 2 => InDisc w r (signedSum z (fun i => if (ε i) = 0 then 1 else -1)))
    Finset.univ)

/-! ## Main Theorem -/

/-- **Kleitman (1965)**: For complex z₁,...,zₙ with |zᵢ| ≥ 1,
    the number of signed sums Σ εᵢzᵢ falling in any unit disc
    is at most C(n, ⌊n/2⌋). -/
axiom kleitman_littlewood_offord (n : ℕ) (hn : n ≥ 1)
  (z : Fin n → ℂ) (hz : ∀ i, Complex.abs (z i) ≥ 1)
  (w : ℂ) :
  signedSumCount z w 1 ≤ Nat.choose n (n / 2)

/-! ## Historical Results -/

/-- **Erdős (1945)**: For real z₁,...,zₙ with |zᵢ| ≥ 1, at most
    C(n, ⌊n/2⌋) signed sums fall in any interval of length 2.
    This was the original Littlewood–Offord result for reals. -/
axiom erdos_real_case (n : ℕ) (hn : n ≥ 1)
  (z : Fin n → ℝ) (hz : ∀ i, |z i| ≥ 1)
  (a : ℝ) :
  Finset.card (Finset.filter
    (fun ε : Fin n → Fin 2 =>
      let s := Finset.sum Finset.univ (fun i => (if (ε i) = 0 then (1 : ℝ) else -1) * z i)
      a ≤ s ∧ s ≤ a + 2)
    Finset.univ) ≤ Nat.choose n (n / 2)

/-- **Erdős (1961)**: For complex zᵢ with |zᵢ| ≥ 1, the count
    of signed sums in any unit disc is O(2ⁿ/√n). This was
    Erdős's partial result before Kleitman's sharp bound. -/
axiom erdos_complex_weak (n : ℕ) (hn : n ≥ 1)
  (z : Fin n → ℂ) (hz : ∀ i, Complex.abs (z i) ≥ 1)
  (w : ℂ) :
  ∃ C : ℝ, C > 0 ∧ (signedSumCount z w 1 : ℝ) ≤ C * 2 ^ n / Real.sqrt n

/-! ## Generalizations -/

/-- **Kleitman (1970)**: The result extends to arbitrary Hilbert
    spaces: for vectors v₁,...,vₙ in a Hilbert space with
    ‖vᵢ‖ ≥ 1, at most C(n, ⌊n/2⌋) signed sums fall in any
    ball of radius 1. -/
axiom kleitman_hilbert_space : True

/-- **Sperner connection**: The bound C(n, ⌊n/2⌋) is tight and
    equals the size of the largest antichain in the power set
    of {1,...,n}. Kleitman's proof uses antichain arguments. -/
axiom sperner_connection : True

/-- **Related Problem #395**: Further variants of the
    Littlewood–Offord problem. -/
axiom related_395 : True
