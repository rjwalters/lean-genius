import Mathlib

/-
# Basel Problem (OQ-03-OQ-01): The Stuffle Relation ζ(2)² = ζ(4) + 2·ζ(2,2)

Open question (a leaf of Basel OQ-03, "Multiple Zeta Values vs Single Zeta
Values"): the parent file *records* the harmonic (stuffle) product relation

  ζ(2)² = ζ(4) + 2·ζ(2,2),     ζ(2,2) = ∑_{m > n ≥ 1} 1/(m² n²)

as prose and uses it to back out the value ζ(2,2) = π⁴/120 from Euler's closed
forms. It never forms the honest double sum, and never proves the relation.

This file closes that gap. We define the double zeta value

  ζ(2,2) := ∑_{(m,n) : n < m} 1/(m² n²)

as a genuine `tsum` over the strict lower triangle of ℕ × ℕ (terms with `n = 0`
vanish, so this is exactly ∑_{m > n ≥ 1}), and prove the stuffle relation

  (∑' 1/n²)² = (∑' 1/n⁴) + 2·ζ(2,2)

from first principles by the Fubini *diagonal split*:

  (∑_m 1/m²)(∑_n 1/n²) = ∑_{(m,n)} 1/(m² n²)
                       = ∑_{m=n} + ∑_{m<n} + ∑_{m>n}
                       = ζ(4) + ζ(2,2) + ζ(2,2).

The two off-diagonal triangles are equal because the summand is symmetric and
`(m,n) ↦ (n,m)` is a bijection between them; the diagonal contributes ζ(4)
because 1/(n²·n²) = 1/n⁴.

No appeal to the value of ζ(2) (or π) is made anywhere: this is a pure
absolutely-convergent rearrangement. 0 axioms, 0 sorries.
-/

namespace BaselProblemOQ03OQ01

open scoped BigOperators

/-- The Basel summand `a k = 1/k²` (with the usual `1/0 = 0` convention, so the
`k = 0` term vanishes). -/
noncomputable def a (k : ℕ) : ℝ := 1 / (k : ℝ) ^ 2

/-- Product summand on `ℕ × ℕ`: `F (m,n) = 1/(m² n²) = a m · a n`. -/
noncomputable def F (p : ℕ × ℕ) : ℝ := a p.1 * a p.2

/-- The strict lower triangle `{(m,n) | n < m}` of `ℕ × ℕ`. -/
def Lower : Set (ℕ × ℕ) := {p | p.2 < p.1}

/-- The strict upper triangle `{(m,n) | m < n}` of `ℕ × ℕ`. -/
def Upper : Set (ℕ × ℕ) := {p | p.1 < p.2}

/-- The diagonal `{(m,n) | m = n}` of `ℕ × ℕ`. -/
def Diag : Set (ℕ × ℕ) := {p | p.1 = p.2}

/-- The double zeta value `ζ(2,2) = ∑_{m > n ≥ 1} 1/(m² n²)`, honestly a sum over
the strict lower triangle of `ℕ × ℕ`. -/
noncomputable def zeta22 : ℝ := ∑' p : Lower, F (p : ℕ × ℕ)

/-! ### Basic summability facts -/

theorem summable_a : Summable a := by
  simpa only [a] using (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)

theorem a_nonneg : ∀ k, 0 ≤ a k := fun k => by
  unfold a; positivity

/-- The product family `(m,n) ↦ a m · a n = F (m,n)` is summable over `ℕ × ℕ`. -/
theorem summable_F : Summable F :=
  summable_a.mul_of_nonneg summable_a a_nonneg a_nonneg

/-- `a n · a n = 1/n⁴`. -/
theorem a_mul_a (n : ℕ) : a n * a n = 1 / (n : ℝ) ^ 4 := by
  unfold a
  rw [one_div_mul_one_div]
  congr 1
  ring

/-! ### The diagonal contributes ζ(4) -/

/-- `ℕ ≃ Diag`, `n ↦ (n,n)`. -/
def diagEquiv : ℕ ≃ Diag where
  toFun n := ⟨(n, n), rfl⟩
  invFun p := (p : ℕ × ℕ).1
  left_inv n := rfl
  right_inv := by
    rintro ⟨⟨x, y⟩, h⟩
    apply Subtype.ext
    simp only [Prod.mk.injEq, true_and]
    exact h

theorem tsum_diag : ∑' p : Diag, F (p : ℕ × ℕ) = ∑' n : ℕ, 1 / (n : ℝ) ^ 4 := by
  rw [← Equiv.tsum_eq diagEquiv (fun p : Diag => F (p : ℕ × ℕ))]
  refine tsum_congr (fun n => ?_)
  show F (n, n) = 1 / (n : ℝ) ^ 4
  simpa only [F] using a_mul_a n

/-! ### The two off-diagonal triangles are equal -/

/-- `Lower ≃ Upper` by swapping coordinates. -/
def swapEquiv : Lower ≃ Upper where
  toFun := fun ⟨⟨m, n⟩, h⟩ => ⟨(n, m), h⟩
  invFun := fun ⟨⟨m, n⟩, h⟩ => ⟨(n, m), h⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

theorem tsum_upper_eq_lower :
    ∑' p : Upper, F (p : ℕ × ℕ) = ∑' p : Lower, F (p : ℕ × ℕ) := by
  rw [← Equiv.tsum_eq swapEquiv (fun p : Upper => F (p : ℕ × ℕ))]
  refine tsum_congr (fun p => ?_)
  obtain ⟨⟨m, n⟩, h⟩ := p
  show a n * a m = a m * a n
  exact mul_comm _ _

/-! ### The diagonal split -/

/-- Pointwise: `F = 𝟙_Diag·F + 𝟙_Lower·F + 𝟙_Upper·F`, since every `(m,n)` lies in
exactly one of the diagonal / lower / upper triangle. -/
theorem F_indicator_split (p : ℕ × ℕ) :
    F p = Diag.indicator F p + Lower.indicator F p + Upper.indicator F p := by
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · -- upper triangle: p.1 < p.2
    have hU : p ∈ Upper := h
    have hD : p ∉ Diag := h.ne
    have hL : p ∉ Lower := not_lt.2 h.le
    rw [Set.indicator_of_notMem hD, Set.indicator_of_notMem hL,
      Set.indicator_of_mem hU]
    ring
  · -- diagonal: p.1 = p.2
    have hD : p ∈ Diag := h
    have hU : p ∉ Upper := fun hlt => (ne_of_lt hlt) h
    have hL : p ∉ Lower := fun hlt => (ne_of_lt hlt) h.symm
    rw [Set.indicator_of_mem hD, Set.indicator_of_notMem hL,
      Set.indicator_of_notMem hU]
    ring
  · -- lower triangle: p.2 < p.1
    have hL : p ∈ Lower := h
    have hD : p ∉ Diag := h.ne'
    have hU : p ∉ Upper := not_lt.2 h.le
    rw [Set.indicator_of_notMem hD, Set.indicator_of_mem hL,
      Set.indicator_of_notMem hU]
    ring

theorem tsum_F_split :
    ∑' p : ℕ × ℕ, F p =
      (∑' p : Diag, F (p : ℕ × ℕ))
        + (∑' p : Lower, F (p : ℕ × ℕ))
        + (∑' p : Upper, F (p : ℕ × ℕ)) := by
  have hD : Summable (Diag.indicator F) := summable_F.indicator Diag
  have hL : Summable (Lower.indicator F) := summable_F.indicator Lower
  have hU : Summable (Upper.indicator F) := summable_F.indicator Upper
  -- the three indicator pieces sum, by `HasSum.add`, to the sum of their tsums
  have hs : HasSum (fun p => Diag.indicator F p + Lower.indicator F p + Upper.indicator F p)
      ((∑' p, Diag.indicator F p) + (∑' p, Lower.indicator F p)
        + (∑' p, Upper.indicator F p)) :=
    (hD.hasSum.add hL.hasSum).add hU.hasSum
  rw [tsum_congr F_indicator_split, hs.tsum_eq,
    ← tsum_subtype Diag F, ← tsum_subtype Lower F, ← tsum_subtype Upper F]

/-! ### Main result: the stuffle relation -/

/-- **The stuffle relation** `ζ(2)² = ζ(4) + 2·ζ(2,2)`, proved from scratch by the
Fubini diagonal split — no use of `ζ(2) = π²/6` or any closed form. -/
theorem zeta_two_sq_eq_zeta_four_add_two_zeta22 :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2
      = (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) + 2 * zeta22 := by
  have hmul : (∑' n, a n) * (∑' n, a n) = ∑' p : ℕ × ℕ, F p :=
    summable_a.tsum_mul_tsum summable_a summable_F
  have hsplit := tsum_F_split
  rw [tsum_diag, tsum_upper_eq_lower] at hsplit
  -- assemble
  have key : (∑' n, a n) ^ 2 = (∑' n : ℕ, 1 / (n : ℝ) ^ 4) + 2 * zeta22 := by
    rw [sq, hmul, hsplit]
    unfold zeta22
    ring
  -- `a n = 1/n²`, definitionally
  simpa only [a] using key

/-- Restated: `ζ(2,2)` is exactly `(ζ(2)² − ζ(4))/2`, justifying the value the
parent file recorded by prose. -/
theorem zeta22_eq :
    zeta22 =
      ((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2
        - ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) / 2 := by
  rw [zeta_two_sq_eq_zeta_four_add_two_zeta22]; ring

end BaselProblemOQ03OQ01
