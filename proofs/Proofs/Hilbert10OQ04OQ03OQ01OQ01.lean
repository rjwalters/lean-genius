/-
# Hilbert's 10th Problem OQ-04 · OQ-03 · OQ-01 · OQ-01:
  The constructive Bézout solver matches Mathlib's abstract `Finset.gcd`

The parent entry (`Proofs/Hilbert10OQ04OQ03OQ01.lean`, merged PR #26924) builds an
*explicit, computable* solver for linear Diophantine equations
`a₀x₀ + … + aₙ₋₁xₙ₋₁ = c`.  Its solvability test is the hand-rolled fold
`vecGcd n a = Int.gcd (a 0) (Int.gcd (a 1) (… 0))`, defined by structural recursion
on the coefficient vector so that the extended Euclidean witness can be peeled off
one coordinate at a time.

Mathlib, on the other hand, packages the gcd of a family of ring elements as the
abstract `Finset.gcd : Finset β → (β → α) → α`, the normalized gcd over a
`NormalizedGCDMonoid`.  This is the object that appears in the structural theory of
finitely generated ideals and invariant factors.

This file **bridges the two**:

* `vecGcd_eq_finset_gcd` — the parent's recursive `vecGcd n a` equals
  `Finset.univ.gcd a` (the normalized `Finset.gcd` over all coordinates).  Both are
  non-negative integers, and the fold is exactly the `Finset.cons`-recursion of
  `Finset.gcd` on `Fin (n+1)`.

* `solvable_iff_finset_gcd_dvd` — consequently the divisibility criterion
  `Finset.univ.gcd a ∣ c` is **equivalent** to solvability of
  `∑ i, a i · x i = c`.  The hard ("yes-instance") direction is discharged
  *verbatim* by the parent's constructive `exists_vec_combo`; the easy direction is
  the standard "the gcd divides every coefficient, hence the linear combination".

The upshot is that the project's explicit-Bézout-witness construction and Mathlib's
abstract `Finset.gcd` divisibility criterion describe one and the same predicate.

Self-contained: depends only on Mathlib and the parent file.

Toolchain: leanprover/lean4 v4.26.0.
-/
import Mathlib
import Proofs.Hilbert10OQ04OQ03OQ01

open Hilbert10OQ04OQ03OQ01

namespace Hilbert10OQ04OQ03OQ01OQ01

/-! ## The recursive `vecGcd` agrees with the abstract `Finset.gcd` -/

/-- **The parent's recursive fold equals Mathlib's normalized `Finset.gcd`.**

    `vecGcd n a` (the explicit `Int.gcd`-fold used by the constructive solver) is
    equal to `Finset.univ.gcd a`, the normalized gcd of the family `a : Fin n → ℤ`.
    The proof is the induction making the `Fin (n+1)` decomposition
    `univ = cons 0 (map succ univ)` match the recursion clause
    `vecGcd (n+1) a = Int.gcd (a 0) (vecGcd n (Fin.tail a))`. -/
theorem vecGcd_eq_finset_gcd :
    ∀ (n : ℕ) (a : Fin n → ℤ), vecGcd n a = (Finset.univ : Finset (Fin n)).gcd a := by
  intro n
  induction n with
  | zero =>
      intro a
      simp [vecGcd]
  | succ n ih =>
      intro a
      simp only [vecGcd]
      rw [Fin.univ_succ, Finset.cons_eq_insert, Finset.gcd_insert,
          Finset.map_eq_image, Finset.gcd_image, Int.coe_gcd]
      -- Goal: GCDMonoid.gcd (a 0) (vecGcd n (Fin.tail a))
      --     = GCDMonoid.gcd (a 0) (univ.gcd (a ∘ Fin.succ))
      -- and `a ∘ Fin.succ` is definitionally `Fin.tail a`.
      congr 1
      exact ih (Fin.tail a)

/-! ## Solvability ⇔ the abstract `Finset.gcd` divisibility criterion -/

/-- **Easy direction.**  If `∑ i, a i · x i = c` has a solution, then the gcd of the
    coefficients divides `c`: the gcd divides every `a i`, hence every summand,
    hence the sum. -/
theorem finset_gcd_dvd_of_solvable (n : ℕ) (a : Fin n → ℤ) (c : ℤ)
    (h : ∃ x : Fin n → ℤ, ∑ i, a i * x i = c) :
    (Finset.univ : Finset (Fin n)).gcd a ∣ c := by
  obtain ⟨x, hx⟩ := h
  rw [← hx]
  exact Finset.dvd_sum fun i _ => (Finset.gcd_dvd (Finset.mem_univ i)).mul_right (x i)

/-- **Hard direction.**  If the gcd of the coefficients divides `c`, then
    `∑ i, a i · x i = c` is solvable.  This is the parent's constructive
    `exists_vec_combo`, restated against the abstract `Finset.gcd` criterion via the
    bridge `vecGcd_eq_finset_gcd`. -/
theorem solvable_of_finset_gcd_dvd (n : ℕ) (a : Fin n → ℤ) (c : ℤ)
    (h : (Finset.univ : Finset (Fin n)).gcd a ∣ c) :
    ∃ x : Fin n → ℤ, ∑ i, a i * x i = c :=
  exists_vec_combo n a c (by rw [vecGcd_eq_finset_gcd]; exact h)

/-- **Linear Diophantine solvability ⇔ `Finset.gcd` divisibility.**

    Unifies the project's explicit-Bézout-witness solver with Mathlib's abstract
    invariant-factor divisibility criterion: the equation `∑ i, a i · x i = c` has an
    integer solution **iff** `Finset.univ.gcd a ∣ c`.  Both directions are fully
    proved — the forward implication reuses the parent's constructive witness. -/
theorem solvable_iff_finset_gcd_dvd (n : ℕ) (a : Fin n → ℤ) (c : ℤ) :
    (∃ x : Fin n → ℤ, ∑ i, a i * x i = c) ↔
      (Finset.univ : Finset (Fin n)).gcd a ∣ c :=
  ⟨finset_gcd_dvd_of_solvable n a c, solvable_of_finset_gcd_dvd n a c⟩

/-! ## Sanity checks -/

-- `3·x + 5·y = 1`: the abstract gcd criterion fires (`Finset.gcd {3,5} = 1 ∣ 1`).
example : ∃ x : Fin 2 → ℤ, ∑ i, ![3, 5] i * x i = 1 :=
  (solvable_iff_finset_gcd_dvd 2 ![3, 5] 1).mpr (by decide)

-- `6·x + 4·y = 10`: solvable, and conversely the gcd `2` must divide `10`.
example : ∃ x : Fin 2 → ℤ, ∑ i, ![6, 4] i * x i = 10 :=
  (solvable_iff_finset_gcd_dvd 2 ![6, 4] 10).mpr (by decide)

end Hilbert10OQ04OQ03OQ01OQ01
