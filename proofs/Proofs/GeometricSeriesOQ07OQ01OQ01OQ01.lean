/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01:
# The combinatorial Eulerian numbers and the coefficients of the Eulerian polynomial

The parent entry `geometric-series-oq-07-oq-01-oq-01` (Frobenius' identity) proves that the
geometric-moment numerator `Nₘ(X) = ∑_{k} S(m,k)·k!·Xᵏ·(1−X)^{m−k}` equals the **Eulerian
polynomial** `Eₘ`, where `Eₘ` is *defined by its first-order differential recurrence*
`E₀ = 1`, `E_{m+1} = X·(1−X)·E′ₘ + (m+1)·X·Eₘ`.  That entry left open (`oq-01`) the textbook
identification of the *coefficients* of `Eₘ` with the **combinatorial Eulerian numbers** `⟨m,k⟩`,
the descent statistic on permutations, defined by the classical triangle recurrence

  ⟨m,k⟩ = (k+1)·⟨m−1,k⟩ + (m−k)·⟨m−1,k−1⟩,    ⟨m,0⟩ = 1.

This entry settles it.  We build `⟨m,k⟩` from scratch (Mathlib has only Eulerian *graphs*, no
Eulerian *numbers*) and prove that the Eulerian polynomial `Eₘ` of the parent is exactly the
generating polynomial of its row:

  **`eulerPoly_eq_eulerianNumbers`** :  `E_{m+1}(X) = ∑_{j=0}^{m} ⟨m+1,j⟩ · X^{j+1}`.

Composing with the parent's Frobenius identity gives the same expansion for the Stirling form
(**`stirlingForm_eq_eulerianNumbers`**):

  `∑_{k=0}^{m+1} S(m+1,k)·k!·Xᵏ·(1−X)^{m+1−k} = ∑_{j=0}^{m} ⟨m+1,j⟩·X^{j+1}`,

so the geometric moment numerator's coefficients are, on the nose, the Eulerian numbers.

## Method

We import the parent's `eulerPoly` and its defining recurrence `eulerPoly_succ`.  The
identification is an induction on `m`: substituting the inductive monomial description of `Eₘ`
into the differential recurrence reproduces, coefficient by coefficient, the Eulerian triangle
recurrence (here packaged as `eulerian_succ_succ`).  The base case `E₁ = X` is the parent's
`eulerPoly_one`.  The Eulerian rows of order `1,2,3` are `1`; `1,1`; `1,4,1`, matching the
parent's `E₁ = X`, `E₂ = X+X²`, `E₃ = X+4X²+X³`.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ01

open Finset Nat Polynomial GeometricSeriesOQ07OQ01OQ01

variable {R : Type*} [CommRing R]

/-! ## The combinatorial Eulerian numbers -/

/-- The **Eulerian numbers** `⟨m,j⟩`, the number of permutations of `{1,…,m}` with `j`
descents, defined by the classical triangle recurrence
`⟨n+1,k+1⟩ = (k+2)·⟨n,k+1⟩ + (n−k)·⟨n,k⟩`, `⟨m,0⟩ = 1` (equivalently
`⟨m,k⟩ = (k+1)·⟨m−1,k⟩ + (m−k)·⟨m−1,k−1⟩`). -/
def eulerian : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k

@[simp] theorem eulerian_zero_zero : eulerian 0 0 = 1 := rfl
@[simp] theorem eulerian_zero_succ (k : ℕ) : eulerian 0 (k + 1) = 0 := rfl
@[simp] theorem eulerian_succ_zero (n : ℕ) : eulerian (n + 1) 0 = 1 := rfl

theorem eulerian_succ_succ (n k : ℕ) :
    eulerian (n + 1) (k + 1) = (k + 2) * eulerian n (k + 1) + (n - k) * eulerian n k := rfl

/-- The Eulerian numbers vanish above the diagonal: `⟨n,j⟩ = 0` for `n < j`. -/
theorem eulerian_eq_zero_of_lt {n j : ℕ} (h : n < j) : eulerian n j = 0 := by
  induction n generalizing j with
  | zero => obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0); rfl
  | succ n ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [eulerian_succ_succ, show n - j = 0 from by omega, zero_mul, add_zero,
      ih (by omega : n < j + 1), mul_zero]

/-- The Eulerian numbers vanish on the diagonal: `⟨n+1,n+1⟩ = 0` (max descents is `n`). -/
theorem eulerian_succ_self (n : ℕ) : eulerian (n + 1) (n + 1) = 0 := by
  rw [eulerian_succ_succ, Nat.sub_self, zero_mul, add_zero,
    eulerian_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero]

/-- Cast helper: a product of two `C`-coerced naturals is the `C`-coercion of their product. -/
private theorem C_natCast_mul (a b : ℕ) :
    (C (a : R)) * (C (b : R)) = C ((a * b : ℕ) : R) := by
  rw [← map_mul]; push_cast; ring

/-! ## The coefficients of the Eulerian polynomial are the Eulerian numbers -/

/-- **The Eulerian polynomial is the generating polynomial of its Eulerian-number row.**
For every `m ≥ 1` (written `m+1`), `E_{m+1}(X) = ∑_{j=0}^{m} ⟨m+1,j⟩ · X^{j+1}`, where `Eₘ` is
the parent's `eulerPoly` (defined by its differential recurrence) and `⟨m,j⟩` are the
combinatorial Eulerian numbers defined above. -/
theorem eulerPoly_eq_eulerianNumbers (m : ℕ) :
    (eulerPoly (m + 1) : R[X])
      = ∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1) := by
  induction m with
  | zero =>
    rw [eulerPoly_one, Finset.sum_range_one]
    simp [show eulerian 1 0 = 1 from rfl]
  | succ m ih =>
    rw [eulerPoly_succ, ih,
      show (((m + 1 : ℕ) : R[X]) + 1) = C (((m + 1 : ℕ) : R) + 1) from by
        rw [map_add, map_natCast, map_one]]
    -- derivative of the Eulerian polynomial (a sum of monomials)
    have hD : derivative (∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1))
        = ∑ j ∈ range (m + 1),
            C ((eulerian (m + 1) j : ℕ) : R) * (C ((j + 1 : ℕ) : R) * X ^ j) := by
      rw [derivative_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [derivative_C_mul, derivative_X_pow, Nat.add_sub_cancel]
    -- assemble the left-hand side into `S₁ + S₂`
    have hLHS :
        X * (1 - X) *
              derivative (∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1))
            + C (((m + 1 : ℕ) : R) + 1) * X *
                ∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1)
          = (∑ j ∈ range (m + 1), C (((j + 1) * eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1))
            + (∑ j ∈ range (m + 1), C (((m + 1 - j) * eulerian (m + 1) j : ℕ) : R) * X ^ (j + 2)) := by
      rw [hD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      have hcast : C (((m + 1 : ℕ) : R) + 1) = C ((j + 1 : ℕ) : R) + C ((m + 1 - j : ℕ) : R) := by
        rw [← map_add]; congr 1; push_cast [Nat.cast_sub (by omega : j ≤ m + 1)]; ring
      have hc1 : C (((j + 1) * eulerian (m + 1) j : ℕ) : R)
          = C ((eulerian (m + 1) j : ℕ) : R) * C ((j + 1 : ℕ) : R) := by
        rw [C_natCast_mul]; congr 1; push_cast; ring
      have hc2 : C (((m + 1 - j) * eulerian (m + 1) j : ℕ) : R)
          = C ((eulerian (m + 1) j : ℕ) : R) * C ((m + 1 - j : ℕ) : R) := by
        rw [C_natCast_mul]; congr 1; push_cast; ring
      rw [hc1, hc2, hcast]
      ring
    rw [hLHS]
    -- expand the target Eulerian polynomial for `m+2` and peel the `i = 0` term
    rw [Finset.sum_range_succ' (fun i => C ((eulerian (m + 2) i : ℕ) : R) * X ^ (i + 1)) (m + 1)]
    have hg0 : C ((eulerian (m + 2) 0 : ℕ) : R) * X ^ (0 + 1) = X := by
      simp [eulerian_succ_zero]
    rw [hg0]
    -- split each `i = k+1` summand by the Eulerian triangle recurrence
    have hsplit : (∑ k ∈ range (m + 1), C ((eulerian (m + 2) (k + 1) : ℕ) : R) * X ^ (k + 1 + 1))
        = (∑ k ∈ range (m + 1), C (((k + 2) * eulerian (m + 1) (k + 1) : ℕ) : R) * X ^ (k + 2))
          + (∑ k ∈ range (m + 1), C (((m + 1 - k) * eulerian (m + 1) k : ℕ) : R) * X ^ (k + 2)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have hrec : eulerian (m + 2) (k + 1)
          = (k + 2) * eulerian (m + 1) (k + 1) + (m + 1 - k) * eulerian (m + 1) k := by
        rw [eulerian_succ_succ]
      rw [hrec, Nat.cast_add, map_add, show k + 1 + 1 = k + 2 from rfl]
      ring
    rw [hsplit]
    -- reconcile the `S₁` part: re-index the `(k+2)·⟨m+1,k+1⟩` sum
    have hS1 : (∑ j ∈ range (m + 1), C (((j + 1) * eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1))
        = (∑ k ∈ range (m + 1), C (((k + 2) * eulerian (m + 1) (k + 1) : ℕ) : R) * X ^ (k + 2))
          + X := by
      rw [Finset.sum_range_succ' (fun j =>
            C (((j + 1) * eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1)) m,
          Finset.sum_range_succ (fun k =>
            C (((k + 2) * eulerian (m + 1) (k + 1) : ℕ) : R) * X ^ (k + 2)) m]
      have hz : C (((m + 2) * eulerian (m + 1) (m + 1) : ℕ) : R) * X ^ (m + 2) = 0 := by
        rw [eulerian_succ_self]; simp
      rw [hz, add_zero]
      have hx0 : C (((0 + 1) * eulerian (m + 1) 0 : ℕ) : R) * X ^ (0 + 1) = X := by
        simp [eulerian_succ_zero]
      rw [hx0]
    rw [hS1]
    ring

/-- **The Stirling moment numerator expanded over the Eulerian numbers.**  Composing the parent's
Frobenius identity `stirlingForm = eulerPoly` with `eulerPoly_eq_eulerianNumbers`:
`∑_{k=0}^{m+1} S(m+1,k)·k!·Xᵏ·(1−X)^{m+1−k} = ∑_{j=0}^{m} ⟨m+1,j⟩·X^{j+1}`. -/
theorem stirlingForm_eq_eulerianNumbers (m : ℕ) :
    (stirlingForm (m + 1) : R[X])
      = ∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1) := by
  rw [← eulerPoly_eq_stirlingForm, eulerPoly_eq_eulerianNumbers]

/-! ## The low-order Eulerian rows

`⟨1,0⟩ = 1`; `⟨2,0⟩ = ⟨2,1⟩ = 1`; `⟨3,0⟩ = ⟨3,2⟩ = 1`, `⟨3,1⟩ = 4`, reproducing the
parent's `E₁ = X`, `E₂ = X + X²`, `E₃ = X + 4X² + X³`. -/

example : eulerian 1 0 = 1 ∧ eulerian 2 0 = 1 ∧ eulerian 2 1 = 1 ∧
    eulerian 3 0 = 1 ∧ eulerian 3 1 = 4 ∧ eulerian 3 2 = 1 := by decide

/-- Order 3: `E₃(X) = ⟨3,0⟩X + ⟨3,1⟩X² + ⟨3,2⟩X³ = X + 4X² + X³`. -/
example : (eulerPoly 3 : ℚ[X]) = X + 4 * X ^ 2 + X ^ 3 := by
  rw [eulerPoly_eq_eulerianNumbers 2, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [show eulerian 3 0 = 1 from by decide, show eulerian 3 1 = 4 from by decide,
    show eulerian 3 2 = 1 from by decide, Nat.cast_one, Nat.cast_ofNat, map_one, map_ofNat]
  ring

end GeometricSeriesOQ07OQ01OQ01OQ01
