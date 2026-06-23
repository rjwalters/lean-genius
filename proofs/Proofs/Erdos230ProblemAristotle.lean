/-
  Aristotle targets for Erdos230Problem
  Routine supporting lemmas for automated proof search.
  See Erdos230Problem.lean for the main formalization.

  These lemmas support the proof that ultraflat polynomials (Kahane 1980)
  disprove the Erdős-Newman conjecture:
  - Arithmetic inequalities: (1+c/2) < (1+c) when c > 0
  - supNormOnCircle upper bound from IsUltraflat via iSup_le
  - Main disproof: choosing ε = c/2 in kahane_ultraflat yields contradiction
-/
import Mathlib
import Proofs.Erdos230Problem

namespace Erdos230.Aristotle

open Erdos230

/-
  ## Section 1: Arithmetic Lemmas

  When c > 0, using ε = c/2 gives (1+ε) = (1+c/2) < (1+c),
  so the ultraflat upper bound contradicts the conjecture's lower bound.
-/

-- √n > 0 when n ≥ 2
theorem sqrt_pos_of_nat_ge2 (n : ℕ) (hn : n ≥ 2) : Real.sqrt n > 0 := by
  apply Real.sqrt_pos.mpr; norm_cast; omega

-- (1 + c/2) * x < (1 + c) * x when c > 0 and x > 0
theorem half_bound_lt (c x : ℝ) (hc : c > 0) (hx : x > 0) :
    (1 + c / 2) * x < (1 + c) * x := by nlinarith

/-
  ## Section 2: supNormOnCircle Upper Bound

  IsUltraflat P ε asserts |P(z)| ≤ (1+ε)√n for all z with |z|=1.
  Taking the supremum via iSup_le gives supNormOnCircle P ≤ (1+ε)√n.
-/

-- Upper bound on supNormOnCircle from IsUltraflat condition
theorem supNorm_le_of_ultraflat {n : ℕ} (P : UnimodularPolynomial n) (ε : ℝ)
    (hflat : IsUltraflat P ε) :
    supNormOnCircle P ≤ (1 + ε) * Real.sqrt n := by
  unfold supNormOnCircle
  apply iSup_le; intro z
  apply iSup_le; intro hz
  exact (hflat z hz).2

/-
  ## Section 3: Main Disproof

  Kahane's theorem (axiom kahane_ultraflat) provides ultraflat polynomials
  for any ε > 0. Choosing ε = c/2 contradicts a conjecture of the form
  sup ≥ (1+c)√n for all n ≥ 2 and all unimodular P of degree n.
-/

-- Kahane's ultraflat polynomials disprove the Erdős-Newman conjecture
theorem kahane_disproves_ari : ¬ErdosNewmanConjecture := by
  intro ⟨c, hc, hconj⟩
  obtain ⟨N, hN⟩ := kahane_ultraflat (c / 2) (by linarith)
  let n := max N 2
  obtain ⟨P, hflat⟩ := hN n (Nat.le_max_left N 2)
  have hn2 : n ≥ 2 := Nat.le_max_right N 2
  have h_upper : supNormOnCircle P ≤ (1 + c / 2) * Real.sqrt n :=
    supNorm_le_of_ultraflat P (c / 2) hflat
  have h_lower : supNormOnCircle P ≥ (1 + c) * Real.sqrt n := hconj n hn2 P
  have hpos : Real.sqrt n > 0 := sqrt_pos_of_nat_ge2 n hn2
  nlinarith [mul_pos (show (0 : ℝ) < c / 2 by linarith) hpos]

end Erdos230.Aristotle
