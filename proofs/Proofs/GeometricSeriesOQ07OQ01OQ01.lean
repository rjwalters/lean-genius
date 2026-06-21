/-
# Identifying the Moment Numerator with the Eulerian Polynomial

The gallery entry `geometric-series-oq-07-oq-01` proves the general-moment closed form

  ∑_{n≥0} nᵐ · rⁿ  =  ∑_{k=0}^{m}  S(m,k) · k! · rᵏ / (1 - r)^{k+1},      (|r| < 1)

with `S(m,k) = Nat.stirlingSecond`.  Clearing the common denominator `(1 - r)^{m+1}` turns the
right-hand side into a single *polynomial* numerator

  Nₘ(r)  :=  ∑_{k=0}^{m}  S(m,k) · k! · rᵏ · (1 - r)^{m-k},

so that `∑ nᵐ rⁿ = Nₘ(r) / (1 - r)^{m+1}`.  The low-order numerators computed in that entry are

  N₀ = 1,   N₁ = r,   N₂ = r + r²,   N₃ = r + 4r² + r³,

whose coefficients `1; 1; 1,1; 1,4,1` are the **Eulerian numbers** `⟨m,j⟩`.  This file makes
that observation a theorem: the moment numerator *is* the Eulerian polynomial.

## What is proved

Working in the polynomial ring `R[X]` over an arbitrary commutative ring `R`:

* `numer_zero` / `numer_recurrence` — the numerator polynomial `Nₘ` satisfies
  `N₀ = 1` and the **differential recurrence**
      `N_{m+1}  =  X·(1 - X)·N'ₘ  +  (m+1)·X·Nₘ`,
  which is exactly the defining recurrence of the (geometrically-normalised) Eulerian
  polynomials.  This is a pure ring identity, valid over any `CommRing`.
* `eulerian` — the Eulerian numbers `⟨m,j⟩`, defined by the classical triangle recurrence
      `⟨m+1, j+1⟩ = (j+2)·⟨m, j+1⟩ + (m-j)·⟨m, j⟩`,   `⟨m,0⟩ = 1`.
* `numer_eq_eulerianPoly` — **the main identity**: for `m ≥ 1` (written `m+1`),
      `Nₘ₊₁(X)  =  ∑_{j=0}^{m} ⟨m+1,j⟩ · X^{j+1}`,
  i.e. the moment numerator is the Eulerian polynomial `∑_j ⟨m+1,j⟩ X^{j+1}`.
* `stirling_numerator_eq_eulerian` — the same identity written out in full,
      `∑_{k=0}^{m+1} S(m+1,k)·k!·Xᵏ·(1-X)^{m+1-k}  =  ∑_{j=0}^{m} ⟨m+1,j⟩·X^{j+1}`.
* `eulerian_eq_zero_of_lt`, `eulerian_succ_self` — the Eulerian numbers vanish for `j ≥ m`.

The order-`1,2,3` instances exhibit the Eulerian rows `1`; `1,1`; `1,4,1`, matching the
low-order numerators `r`, `r+r²`, `r+4r²+r³` recorded in `geometric-series-oq-07-oq-01`.

## Method

The numerator recurrence is proved by differentiating the defining `Finset` sum term by term
(`Polynomial.derivative_sum`, `derivative_mul`, `derivative_X_pow`, `derivative_pow`) and
re-indexing with the Stirling recurrence `S(m+1,k) = k·S(m,k) + S(m,k-1)`.  The Eulerian
identity then follows by induction on `m`: substituting the inductive description of `Nₘ` as a
sum of monomials into the differential recurrence reproduces, coefficient by coefficient,
the Eulerian triangle recurrence.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib

namespace GeometricSeriesOQ07OQ01OQ01

open Finset Nat Polynomial

variable {R : Type*} [CommRing R]

/-! ## The moment numerator polynomial -/

/-- The **moment numerator** `Nₘ(X) = ∑_{k=0}^{m} S(m,k)·k!·Xᵏ·(1-X)^{m-k}` in `R[X]`. -/
noncomputable def numer (R : Type*) [CommRing R] (m : ℕ) : R[X] :=
  ∑ k ∈ range (m + 1),
    C ((stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m - k)

@[simp] theorem numer_zero : numer R 0 = 1 := by
  simp [numer, stirlingSecond_zero]

/-! ## The Eulerian numbers -/

/-- The **Eulerian numbers** `⟨m,j⟩`, the number of permutations of `{1,…,m}` with `j`
descents, defined by the classical triangle recurrence. -/
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

/-! ## The numerator differential recurrence

We prove `N_{m+1} = X·(1-X)·N'ₘ + (m+1)·X·Nₘ` by differentiating the defining sum term by
term.  Two boundary helpers absorb the truncated exponents `Xᵏ⁻¹` / `(1-X)ᵖ⁻¹` that appear in
`derivative_X_pow` / `derivative_pow`: at the boundary the natural-number coefficient is `0`, so
multiplying by `X` (resp. `1-X`) restores the un-truncated power. -/

/-- Boundary helper: `X · (k · Xᵏ⁻¹) = k · Xᵏ` (the `k = 0` case holds since the coefficient
vanishes). -/
private theorem X_mul_C_X_pow_pred (k : ℕ) :
    (X : R[X]) * (C (k : R) * X ^ (k - 1)) = C (k : R) * X ^ k := by
  rcases k with _ | j
  · simp
  · simp only [Nat.add_sub_cancel]; ring

/-- Boundary helper for the `(1 - X)` factor: `(1-X) · (p · (1-X)ᵖ⁻¹) = p · (1-X)ᵖ`. -/
private theorem oneSubX_mul_C_pow_pred (p : ℕ) :
    (1 - X : R[X]) * (C (p : R) * (1 - X) ^ (p - 1)) = C (p : R) * (1 - X) ^ p := by
  rcases p with _ | q
  · simp
  · simp only [Nat.add_sub_cancel]; ring

/-- Term-by-term derivative of the numerator summand. -/
private theorem derivative_numer_term (m k : ℕ) :
    derivative (C ((stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m - k))
      = C ((stirlingSecond m k * k.factorial : ℕ) : R) *
          (C (k : R) * X ^ (k - 1) * (1 - X) ^ (m - k))
        - C ((stirlingSecond m k * k.factorial : ℕ) : R) *
          (C ((m - k : ℕ) : R) * X ^ k * (1 - X) ^ (m - k - 1)) := by
  have hd1 : derivative (1 - X : R[X]) = -1 := by
    rw [derivative_sub, derivative_one, derivative_X]; ring
  rw [mul_assoc, derivative_C_mul, derivative_mul, derivative_X_pow, derivative_pow, hd1]
  ring

/-- Cast helper: a product of two `C`-coerced naturals is the `C`-coercion of their product. -/
private theorem C_natCast_mul (a b : ℕ) :
    (C (a : R)) * (C (b : R)) = C ((a * b : ℕ) : R) := by
  rw [← map_mul]; push_cast; ring

/-- **The numerator differential recurrence.**  Over any commutative ring,
`N_{m+1} = X·(1 - X)·N'ₘ + (m+1)·X·Nₘ`. -/
theorem numer_recurrence (m : ℕ) :
    numer R (m + 1)
      = X * (1 - X) * derivative (numer R m) + C ((m : R) + 1) * X * numer R m := by
  -- The derivative of `numer R m`, term by term.
  have hD : derivative (numer R m)
      = ∑ k ∈ range (m + 1),
          (C ((stirlingSecond m k * k.factorial : ℕ) : R) *
              (C (k : R) * X ^ (k - 1) * (1 - X) ^ (m - k))
            - C ((stirlingSecond m k * k.factorial : ℕ) : R) *
              (C ((m - k : ℕ) : R) * X ^ k * (1 - X) ^ (m - k - 1))) := by
    rw [numer, derivative_sum]
    exact Finset.sum_congr rfl (fun k _ => derivative_numer_term m k)
  -- Rewrite the whole right-hand side as `T_A + T_B`, two sums over `range (m+1)`.
  have hRHS :
      X * (1 - X) * derivative (numer R m) + C ((m : R) + 1) * X * numer R m
        = (∑ k ∈ range (m + 1),
            C ((k * stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m + 1 - k))
          + (∑ k ∈ range (m + 1),
            C ((stirlingSecond m k * (k + 1).factorial : ℕ) : R) * X ^ (k + 1) * (1 - X) ^ (m - k)) := by
    rw [hD, numer, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    -- the two boundary pieces of the derivative term, multiplied by `X·(1-X)`
    have e1 : X * (1 - X) * (C ((stirlingSecond m k * k.factorial : ℕ) : R) *
                (C (k : R) * X ^ (k - 1) * (1 - X) ^ (m - k)))
            = C ((k * stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m + 1 - k) := by
      have hX : (X : R[X]) * (C (k : R) * X ^ (k - 1)) = C (k : R) * X ^ k :=
        X_mul_C_X_pow_pred k
      have hcoef : C ((k * stirlingSecond m k * k.factorial : ℕ) : R)
          = C ((stirlingSecond m k * k.factorial : ℕ) : R) * C (k : R) := by
        rw [C_natCast_mul]; congr 1; push_cast; ring
      rw [show m + 1 - k = (m - k) + 1 from by omega, pow_succ, hcoef]
      calc X * (1 - X) * (C ((stirlingSecond m k * k.factorial : ℕ) : R) *
              (C (k : R) * X ^ (k - 1) * (1 - X) ^ (m - k)))
          = C ((stirlingSecond m k * k.factorial : ℕ) : R) * (1 - X) ^ (m - k) * (1 - X)
              * (X * (C (k : R) * X ^ (k - 1))) := by ring
        _ = C ((stirlingSecond m k * k.factorial : ℕ) : R) * (1 - X) ^ (m - k) * (1 - X)
              * (C (k : R) * X ^ k) := by rw [hX]
        _ = C ((stirlingSecond m k * k.factorial : ℕ) : R) * C (k : R) * X ^ k
              * ((1 - X) ^ (m - k) * (1 - X)) := by ring
    have e2 : X * (1 - X) * (C ((stirlingSecond m k * k.factorial : ℕ) : R) *
                (C ((m - k : ℕ) : R) * X ^ k * (1 - X) ^ (m - k - 1)))
            = C ((stirlingSecond m k * k.factorial : ℕ) : R) *
                (C ((m - k : ℕ) : R) * (1 - X) ^ (m - k)) * X ^ (k + 1) := by
      have h2 : (1 - X : R[X]) * (C ((m - k : ℕ) : R) * (1 - X) ^ (m - k - 1))
          = C ((m - k : ℕ) : R) * (1 - X) ^ (m - k) := oneSubX_mul_C_pow_pred (m - k)
      rw [pow_succ]
      calc X * (1 - X) * (C ((stirlingSecond m k * k.factorial : ℕ) : R) *
              (C ((m - k : ℕ) : R) * X ^ k * (1 - X) ^ (m - k - 1)))
          = C ((stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k
              * ((1 - X) * (C ((m - k : ℕ) : R) * (1 - X) ^ (m - k - 1))) * X := by ring
        _ = C ((stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k
              * (C ((m - k : ℕ) : R) * (1 - X) ^ (m - k)) * X := by rw [h2]
        _ = C ((stirlingSecond m k * k.factorial : ℕ) : R)
              * (C ((m - k : ℕ) : R) * (1 - X) ^ (m - k)) * (X ^ k * X) := by ring
    have eB : C ((stirlingSecond m k * (k + 1).factorial : ℕ) : R) * X ^ (k + 1) * (1 - X) ^ (m - k)
            = C ((stirlingSecond m k * k.factorial : ℕ) : R) * (C ((k + 1 : ℕ) : R) * (1 - X) ^ (m - k))
                * X ^ (k + 1) := by
      have hc : C ((stirlingSecond m k * (k + 1).factorial : ℕ) : R)
          = C ((stirlingSecond m k * k.factorial : ℕ) : R) * C ((k + 1 : ℕ) : R) := by
        rw [C_natCast_mul]; congr 1; push_cast [Nat.factorial_succ]; ring
      rw [hc]; ring
    -- split the `(m+1)` coefficient as `(m-k) + (k+1)`
    have hcast : C ((m : R) + 1) = C ((m - k : ℕ) : R) + C ((k + 1 : ℕ) : R) := by
      rw [← map_add]; congr 1; push_cast [Nat.cast_sub hk]; ring
    rw [mul_sub, e1, e2, eB, hcast]
    ring
  rw [hRHS]
  -- Now show `numer (m+1) = T_A + T_B`.
  rw [numer]
  rw [Finset.sum_range_succ' (fun j =>
        C ((stirlingSecond (m + 1) j * j.factorial : ℕ) : R) * X ^ j * (1 - X) ^ (m + 1 - j)) (m + 1)]
  -- the `j = 0` term vanishes
  have hg0 : C ((stirlingSecond (m + 1) 0 * (0 : ℕ).factorial : ℕ) : R) * X ^ 0 * (1 - X) ^ (m + 1 - 0)
      = 0 := by simp [stirlingSecond_succ_zero]
  rw [hg0, add_zero]
  -- split each `j = k+1` summand via the Stirling recurrence
  have hsplit : (∑ k ∈ range (m + 1),
        C ((stirlingSecond (m + 1) (k + 1) * (k + 1).factorial : ℕ) : R) * X ^ (k + 1)
          * (1 - X) ^ (m + 1 - (k + 1)))
      = (∑ k ∈ range (m + 1),
          C (((k + 1) * stirlingSecond m (k + 1) * (k + 1).factorial : ℕ) : R) * X ^ (k + 1)
            * (1 - X) ^ (m + 1 - (k + 1)))
        + (∑ k ∈ range (m + 1),
          C ((stirlingSecond m k * (k + 1).factorial : ℕ) : R) * X ^ (k + 1) * (1 - X) ^ (m - k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hrec : stirlingSecond (m + 1) (k + 1)
        = (k + 1) * stirlingSecond m (k + 1) + stirlingSecond m k := by
      rw [stirlingSecond_succ_succ]
    rw [hrec, show m + 1 - (k + 1) = m - k from by omega, add_mul,
      Nat.cast_add, map_add]
    ring
  rw [hsplit]
  -- reconcile the first sum (the `k·S(m,k)·k!` part) by re-indexing
  have hTA : (∑ k ∈ range (m + 1),
        C (((k + 1) * stirlingSecond m (k + 1) * (k + 1).factorial : ℕ) : R) * X ^ (k + 1)
          * (1 - X) ^ (m + 1 - (k + 1)))
      = ∑ k ∈ range (m + 1),
          C ((k * stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m + 1 - k) := by
    rw [Finset.sum_range_succ' (fun k =>
          C ((k * stirlingSecond m k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m + 1 - k)) m,
        Finset.sum_range_succ (fun k =>
          C (((k + 1) * stirlingSecond m (k + 1) * (k + 1).factorial : ℕ) : R) * X ^ (k + 1)
            * (1 - X) ^ (m + 1 - (k + 1))) m]
    have hz : C (((m + 1) * stirlingSecond m (m + 1) * (m + 1).factorial : ℕ) : R)
          * X ^ (m + 1) * (1 - X) ^ (m + 1 - (m + 1)) = 0 := by
      rw [stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m)]; simp
    rw [hz, add_zero]
    have hz0 : C ((0 * stirlingSecond m 0 * (0 : ℕ).factorial : ℕ) : R) * X ^ 0 * (1 - X) ^ (m + 1 - 0)
        = 0 := by simp
    rw [hz0, add_zero]
  rw [hTA]

/-! ## The main identity: the numerator is the Eulerian polynomial -/

/-- **The moment numerator is the Eulerian polynomial.**  For every `m ≥ 1` (written `m+1`),
`Nₘ₊₁(X) = ∑_{j=0}^{m} ⟨m+1,j⟩ · X^{j+1}`.  Equivalently, the change-of-basis Stirling numerator
`∑_{k} S(m+1,k)·k!·Xᵏ·(1-X)^{m+1-k}` equals the Eulerian polynomial `∑_j ⟨m+1,j⟩·X^{j+1}`. -/
theorem numer_eq_eulerianPoly (m : ℕ) :
    numer R (m + 1)
      = ∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1) := by
  induction m with
  | zero =>
    rw [numer, Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_one]
    simp [show stirlingSecond 1 0 = 0 from by decide, show stirlingSecond 1 1 = 1 from by decide]
  | succ m ih =>
    rw [numer_recurrence (m + 1), ih]
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

/-- The main identity, written out as the literal Stirling-number sum:
`∑_{k=0}^{m+1} S(m+1,k)·k!·Xᵏ·(1-X)^{m+1-k} = ∑_{j=0}^{m} ⟨m+1,j⟩·X^{j+1}`. -/
theorem stirling_numerator_eq_eulerian (m : ℕ) :
    (∑ k ∈ range (m + 1 + 1),
        C ((stirlingSecond (m + 1) k * k.factorial : ℕ) : R) * X ^ k * (1 - X) ^ (m + 1 - k))
      = ∑ j ∈ range (m + 1), C ((eulerian (m + 1) j : ℕ) : R) * X ^ (j + 1) := by
  have h := numer_eq_eulerianPoly (R := R) m
  rwa [numer] at h

/-! ## The low-order Eulerian polynomials

The Eulerian numbers `⟨1,0⟩ = 1`, `⟨2,0⟩ = ⟨2,1⟩ = 1`, `⟨3,0⟩ = ⟨3,2⟩ = 1`, `⟨3,1⟩ = 4`
reproduce the numerators recorded in `geometric-series-oq-07-oq-01`. -/

example : eulerian 1 0 = 1 ∧ eulerian 2 0 = 1 ∧ eulerian 2 1 = 1 ∧
    eulerian 3 0 = 1 ∧ eulerian 3 1 = 4 ∧ eulerian 3 2 = 1 := by decide

/-- Order 1: `N₁(X) = X`. -/
example : numer ℚ 1 = X := by
  rw [numer_eq_eulerianPoly 0, Finset.sum_range_one]
  simp

/-- Order 2: `N₂(X) = X + X²`, with Eulerian row `⟨2,0⟩ = ⟨2,1⟩ = 1`. -/
example : numer ℚ 2 = X + X ^ 2 := by
  rw [numer_eq_eulerianPoly 1, Finset.sum_range_succ, Finset.sum_range_one]
  simp [show eulerian 2 0 = 1 from by decide, show eulerian 2 1 = 1 from by decide]

/-- Order 3: `N₃(X) = X + 4X² + X³`, with Eulerian row `⟨3,0⟩,⟨3,1⟩,⟨3,2⟩ = 1,4,1`. -/
example : numer ℚ 3 = X + 4 * X ^ 2 + X ^ 3 := by
  rw [numer_eq_eulerianPoly 2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [show eulerian 3 0 = 1 from by decide, show eulerian 3 1 = 4 from by decide,
    show eulerian 3 2 = 1 from by decide, Nat.cast_one, Nat.cast_ofNat, map_one, map_ofNat]
  ring

end GeometricSeriesOQ07OQ01OQ01
