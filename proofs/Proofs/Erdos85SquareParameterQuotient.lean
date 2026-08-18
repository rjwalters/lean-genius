import Proofs.Erdos85SecondOrderQuotient

/-!
# An infinite square-parameter family of abstract boundary quotients

The quotient equations alone do not rule out all even degrees.  This file
exhibits an infinite three-component family satisfying the exact order, row
sum, detailed-balance, and Moore square equations.  Any uniform obstruction
must therefore use information beyond those equations (for example the full
cycle-block spectrum).
-/

namespace Erdos85

/-- Parameters indexed so that every expression is a natural polynomial.
Here the earlier parameter `a` is `2(k+1)`. -/
def squareFamilyDegree (k : ℕ) : ℕ := 4 * k * k + 4 * k + 4
def squareFamilySmallOrder (k : ℕ) : ℕ := 4 * k * k + 6 * k + 5
def squareFamilyRatio (k : ℕ) : ℕ := 2 * k * k + k + 1
def squareFamilyLargeDiagonal (k : ℕ) : ℕ := 2 * k * k + 3 * k + 2

def squareFamilyOrders (k : ℕ) : Fin 3 → ℕ
  | 0 => squareFamilySmallOrder k
  | _ => squareFamilySmallOrder k * squareFamilyRatio k

/-- The branch whose two large diagonal entries are
`squareFamilyLargeDiagonal`. -/
def squareFamilyQuotient (k : ℕ) : Matrix (Fin 3) (Fin 3) ℕ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 2 * (k + 1) else squareFamilyRatio k
    else if j = 0 then 1
    else if i = j then squareFamilyLargeDiagonal k
    else squareFamilyRatio k

theorem squareFamily_degree_sub_three_square (k : ℕ) :
    squareFamilyDegree k - 3 = (2 * k + 1) ^ 2 := by
  simp [squareFamilyDegree]
  ring

theorem squareFamily_total_order (k : ℕ) :
    ∑ i, squareFamilyOrders k i =
      squareFamilyDegree k * (squareFamilyDegree k - 1) + 3 := by
  simp [squareFamilyOrders, squareFamilyDegree, squareFamilySmallOrder,
    squareFamilyRatio, Fin.sum_univ_succ]
  ring

theorem squareFamilyQuotient_row_sum (k : ℕ) (i : Fin 3) :
    ∑ j, squareFamilyQuotient k i j = squareFamilyDegree k := by
  fin_cases i <;>
    simp [squareFamilyQuotient, squareFamilyDegree, squareFamilyRatio,
      squareFamilyLargeDiagonal, Fin.sum_univ_succ] <;> ring

theorem squareFamilyQuotient_balance (k : ℕ) (i j : Fin 3) :
    squareFamilyOrders k i * squareFamilyQuotient k i j =
      squareFamilyOrders k j * squareFamilyQuotient k j i := by
  fin_cases i <;> fin_cases j <;>
    simp [squareFamilyOrders, squareFamilyQuotient,
      squareFamilySmallOrder, squareFamilyRatio,
      squareFamilyLargeDiagonal] <;> ring

theorem squareFamilyQuotient_handshake (k : ℕ) (i : Fin 3) :
    Even (squareFamilyOrders k i * squareFamilyQuotient k i i) := by
  have htu : Even (squareFamilyRatio k * squareFamilyLargeDiagonal k) := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · apply Even.mul_left
      refine ⟨4 * m * m + 3 * m + 1, ?_⟩
      simp [squareFamilyLargeDiagonal]
      ring
    · apply Even.mul_right
      refine ⟨4 * m * m + 5 * m + 2, ?_⟩
      simp [squareFamilyRatio]
      ring
  fin_cases i
  · refine ⟨squareFamilySmallOrder k * (k + 1), ?_⟩
    simp [squareFamilyOrders, squareFamilyQuotient]
    ring
  · simpa [squareFamilyOrders, squareFamilyQuotient, mul_assoc] using
      htu.mul_left (squareFamilySmallOrder k)
  · simpa [squareFamilyOrders, squareFamilyQuotient, mul_assoc] using
      htu.mul_left (squareFamilySmallOrder k)

theorem squareFamilyQuotient_sq_apply (k : ℕ) (i j : Fin 3) :
    (squareFamilyQuotient k * squareFamilyQuotient k) i j =
      (squareFamilyDegree k - 3) * (if i = j then 1 else 0) +
        squareFamilyOrders k j := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, squareFamilyOrders, squareFamilyQuotient,
      squareFamilyDegree, squareFamilySmallOrder, squareFamilyRatio,
      squareFamilyLargeDiagonal, Fin.sum_univ_succ] <;> ring

end Erdos85
