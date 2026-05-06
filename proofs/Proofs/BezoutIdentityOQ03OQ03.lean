import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Multi-Variable Bézout and Diophantine Solvability Criterion
(bezout-identity-oq-03-oq-03)

## Main Results

For integers a₁,...,aₙ (indexed by Fin n):

1. **`gcdFin_dvd`**: gcd(a₁,...,aₙ) divides each aᵢ.
2. **`bezout_multivar`**: gcd(a₁,...,aₙ) = a₁x₁ + ... + aₙxₙ for some integers xᵢ.
   (Multi-variable Bézout identity, proved by induction using `Int.gcd_eq_gcd_ab`.)
3. **`diophantine_criterion`**: a₁x₁ + ... + aₙxₙ = d is solvable iff gcd(a₁,...,aₙ) ∣ d.

## Connection to CRT structure

The proof follows the same structure as the CRT:
- Two-variable Bézout gives g₁u + aₙv = gcd(g₁, aₙ) at each inductive step.
- Multi-variable Bézout follows by replacing g₁ with ∑ aᵢyᵢ (the induction hypothesis).
- This is exactly how CRT builds a global solution from local Bézout solutions.

## Status: 0 sorries, 0 axioms
-/

open Finset BigOperators

namespace MultiVarBezout

-- ============================================================
-- Part 1: The GCD of a finite family
-- ============================================================

/-- The GCD of a finite family of integers, indexed by Fin n.
    Defined by folding Nat.gcd over the family. -/
noncomputable def gcdFin : ∀ {n : ℕ}, (Fin n → ℤ) → ℕ
  | 0, _ => 0
  | n + 1, a => Nat.gcd (gcdFin (a ∘ Fin.castSucc)) (a (Fin.last n)).natAbs

@[simp] theorem gcdFin_zero (a : Fin 0 → ℤ) : gcdFin a = 0 := rfl

theorem gcdFin_succ {n : ℕ} (a : Fin (n + 1) → ℤ) :
    gcdFin a = Nat.gcd (gcdFin (a ∘ Fin.castSucc)) (a (Fin.last n)).natAbs := rfl

/-- The family GCD equals Int.gcd applied to the sub-GCD and last element -/
private theorem gcdFin_eq_int_gcd {n : ℕ} (a : Fin (n + 1) → ℤ) :
    gcdFin a = Int.gcd (gcdFin (a ∘ Fin.castSucc) : ℤ) (a (Fin.last n)) := by
  simp only [gcdFin_succ, Int.gcd, Int.natAbs_ofNat]

-- ============================================================
-- Part 2: gcdFin divides each component
-- ============================================================

/-- The family GCD divides every element of the family -/
theorem gcdFin_dvd : ∀ {n : ℕ} (a : Fin n → ℤ) (i : Fin n), (gcdFin a : ℤ) ∣ a i := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ k ih =>
    intro a
    refine Fin.lastCases ?_ ?_
    · -- i = Fin.last k
      rw [gcdFin_succ]
      -- Need: (Nat.gcd g aₙ.natAbs : ℤ) ∣ aₙ
      -- From Nat.gcd_dvd_right: Nat.gcd g aₙ.natAbs ∣ aₙ.natAbs
      -- Case split on the sign of aₙ to handle the ℕ → ℤ dvd conversion
      have hdvd : Nat.gcd (gcdFin (a ∘ Fin.castSucc)) (a (Fin.last k)).natAbs ∣
                  (a (Fin.last k)).natAbs := Nat.gcd_dvd_right _ _
      rcases Int.natAbs_eq (a (Fin.last k)) with h | h
      · rw [h]; exact_mod_cast hdvd
      · rw [h]; exact dvd_neg.mpr (by exact_mod_cast hdvd)
    · -- i = Fin.castSucc j
      intro j
      rw [gcdFin_succ]
      -- (Nat.gcd g aₙ.natAbs : ℤ) ∣ a(castSucc j)
      -- By Nat.gcd_dvd_left, g ∣ Nat.gcd g aₙ.natAbs, hence by ih: (g : ℤ) ∣ a(castSucc j)
      exact dvd_trans (Int.coe_nat_dvd.mpr (Nat.gcd_dvd_left _ _)) (ih (a ∘ Fin.castSucc) j)

-- ============================================================
-- Part 3: Multi-variable Bézout identity
-- ============================================================

/-- **Multi-variable Bézout identity**: The family GCD is a ℤ-linear combination
    of the family elements.

    Proved by induction: at each step, use the two-variable Bézout identity
    `Int.gcd_eq_gcd_ab` to combine the inductive hypothesis with the last element. -/
theorem bezout_multivar : ∀ {n : ℕ} (a : Fin n → ℤ),
    ∃ x : Fin n → ℤ, ∑ i : Fin n, a i * x i = (gcdFin a : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro a
    exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro a
    -- Step 1: Get Bézout combination for the first k elements
    obtain ⟨y, hy⟩ := ih (a ∘ Fin.castSucc)
    -- hy: ∑ i : Fin k, (a ∘ castSucc) i * y i = (gcdFin (a ∘ castSucc) : ℤ)
    -- Step 2: Set g = gcdFin of first k elements
    set g : ℕ := gcdFin (a ∘ Fin.castSucc) with hg
    -- Step 3: Two-variable Bézout: (gcdFin a : ℤ) = g * u + a(last k) * v
    have key : gcdFin a = Int.gcd (g : ℤ) (a (Fin.last k)) := gcdFin_eq_int_gcd a
    -- Step 4: Define the solution
    set u := Int.gcdA (g : ℤ) (a (Fin.last k))
    set v := Int.gcdB (g : ℤ) (a (Fin.last k))
    have huv : (gcdFin a : ℤ) = (g : ℤ) * u + a (Fin.last k) * v := by
      have h1 : (gcdFin a : ℤ) = (Int.gcd (g : ℤ) (a (Fin.last k)) : ℤ) := by
        exact_mod_cast key
      rw [h1]
      exact Int.gcd_eq_gcd_ab _ _
    -- x(castSucc i) = y i * u, x(last k) = v
    refine ⟨Fin.lastCases v (fun i => y i * u), ?_⟩
    -- Step 5: Verify the sum
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    -- Sum over first k: ∑ i, a(castSucc i) * (y i * u) = (∑ i, a(castSucc i) * y i) * u
    have hsum : ∑ i : Fin k, a (Fin.castSucc i) * (y i * u) =
        (∑ i : Fin k, (a ∘ Fin.castSucc) i * y i) * u := by
      rw [Finset.sum_mul]; congr 1; ext i; ring
    rw [hsum, hy]
    -- Now: (g : ℤ) * u + a(last k) * v = gcdFin a
    linarith

-- ============================================================
-- Part 4: Diophantine solvability criterion
-- ============================================================

/-- **Multi-variable Diophantine Solvability Criterion**:

    The linear Diophantine equation a₁x₁ + a₂x₂ + ... + aₙxₙ = d
    has integer solutions (x₁,...,xₙ) if and only if gcd(a₁,...,aₙ) divides d.

    **Proof**:
    - (⟹): gcd(aᵢ) | aᵢ for each i, so it divides any linear combination ∑ aᵢxᵢ = d.
    - (⟸): By multi-variable Bézout, ∃ y with ∑ aᵢyᵢ = gcd. If d = gcd * k, take xᵢ = yᵢ * k. -/
theorem diophantine_criterion {n : ℕ} (a : Fin n → ℤ) (d : ℤ) :
    (∃ x : Fin n → ℤ, ∑ i : Fin n, a i * x i = d) ↔ (gcdFin a : ℤ) ∣ d := by
  constructor
  · -- (⟹): A solution exists → gcd divides d
    intro ⟨x, hx⟩
    rw [← hx]
    apply dvd_sum
    intro i _
    exact dvd_mul_of_dvd_left (gcdFin_dvd a i) _
  · -- (⟸): gcd divides d → a solution exists
    intro ⟨k, hk⟩
    obtain ⟨y, hy⟩ := bezout_multivar a
    -- Scale the Bézout combination: xᵢ = yᵢ * k
    refine ⟨fun i => y i * k, ?_⟩
    have : ∑ i : Fin n, a i * (y i * k) = (∑ i : Fin n, a i * y i) * k := by
      rw [Finset.sum_mul]; congr 1; ext i; ring
    rw [this, hy, hk]

-- ============================================================
-- Corollaries and Examples
-- ============================================================

/-- Necessary condition: solvable → gcd divides d -/
theorem gcd_dvd_of_solvable {n : ℕ} (a : Fin n → ℤ) (d : ℤ)
    (h : ∃ x : Fin n → ℤ, ∑ i, a i * x i = d) : (gcdFin a : ℤ) ∣ d :=
  (diophantine_criterion a d).mp h

/-- Sufficient condition: gcd divides d → solvable -/
theorem solvable_of_gcd_dvd {n : ℕ} (a : Fin n → ℤ) (d : ℤ)
    (h : (gcdFin a : ℤ) ∣ d) : ∃ x : Fin n → ℤ, ∑ i, a i * x i = d :=
  (diophantine_criterion a d).mpr h

/-- Example: 4x + 6y + 9z = 1 has no solution (gcd(4,6,9) = 1 ∣ 1 — wait, yes it does!) -/
example : ∃ x y z : ℤ, 4 * x + 6 * y + 9 * z = 1 := by
  -- gcd(4, gcd(6, 9)) = gcd(4, 3) = 1, so d = 1 is solvable
  exact ⟨1, -1, 1, by ring⟩

/-- Example: 4x + 6y = 5 has no integer solution (gcd(4,6) = 2 ∤ 5) -/
example : ¬∃ x y : ℤ, 4 * x + 6 * y = 5 := by
  intro ⟨x, y, h⟩
  -- 4x + 6y = 2(2x + 3y), so 2 ∣ 4x + 6y = 5, contradiction
  omega

/-- Example: 6x + 10y + 15z = d is solvable for any d ∈ ℤ (gcd(6,10,15) = 1) -/
-- Since 6·16 + 10·(-8) + 15·(-1) = 96 - 80 - 15 = 1, we can scale by d.
example (d : ℤ) : ∃ x y z : ℤ, 6 * x + 10 * y + 15 * z = d :=
  ⟨16 * d, -8 * d, -d, by ring⟩

end MultiVarBezout
