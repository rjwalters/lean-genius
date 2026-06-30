/-
# Hilbert's 10th Problem OQ-04 · OQ-03 · OQ-01:
  A constructive Bézout solver for linear Diophantine equations

The parent entry (`Proofs/Hilbert10OQ04.lean`) records the *decidability* of linear
Diophantine solvability as an axiom (`linear_bezout_n`): the equation
`a₁x₁ + … + aₙxₙ = c` has an integer solution iff `gcd(a₁,…,aₙ) ∣ c`.

This file **upgrades the existential characterization into a constructive solver**.
Rather than merely asserting that a solution exists, we produce an *explicit,
computable* witness `x : Fin n → ℤ` whenever the gcd of the coefficients divides
the target `c`.  The construction is the classical extended Euclidean algorithm,
folded over the coefficient vector:

* For the two–variable case we read the Bézout cofactors straight from Mathlib's
  `Int.gcdA` / `Int.gcdB` (so that `a·gcdA + b·gcdB = gcd a b`) and scale them by
  `c / gcd a b`.
* For `n` variables we recurse: solve `a₀·x₀ + d·t = c` where `d = gcd` of the
  remaining coefficients, then recursively realise the value `d·t` as a combination
  of the tail using the inductive hypothesis.

The headline results are therefore **theorems, not axioms** — the forward
("if the gcd divides `c` then a solution exists, and here it is") direction of the
parent's `linear_bezout_n` is discharged with an explicit construction.

Self-contained: depends only on Mathlib.

Toolchain: leanprover/lean4 v4.26.0.
-/
import Mathlib

namespace Hilbert10OQ04OQ03OQ01

/-! ## Two–variable constructive Bézout solver -/

/-- The `x`-component of the explicit solution of `a·x + b·y = c`:
    the first Bézout cofactor of `a, b`, scaled by `c / gcd a b`. -/
def bezoutX (a b c : ℤ) : ℤ := Int.gcdA a b * (c / (Int.gcd a b : ℤ))

/-- The `y`-component of the explicit solution of `a·x + b·y = c`:
    the second Bézout cofactor of `a, b`, scaled by `c / gcd a b`. -/
def bezoutY (a b c : ℤ) : ℤ := Int.gcdB a b * (c / (Int.gcd a b : ℤ))

/-- **Correctness of the two–variable solver.**
    Whenever `gcd a b ∣ c`, the explicit pair `(bezoutX, bezoutY)` solves
    `a·x + b·y = c`. -/
theorem bezout_solve_spec (a b c : ℤ) (h : (Int.gcd a b : ℤ) ∣ c) :
    a * bezoutX a b c + b * bezoutY a b c = c := by
  unfold bezoutX bezoutY
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
    Int.gcd_eq_gcd_ab a b
  have hrw :
      a * (Int.gcdA a b * (c / (Int.gcd a b : ℤ)))
        + b * (Int.gcdB a b * (c / (Int.gcd a b : ℤ)))
      = (a * Int.gcdA a b + b * Int.gcdB a b) * (c / (Int.gcd a b : ℤ)) := by ring
  rw [hrw, ← hbez, Int.mul_ediv_cancel' h]

/-- Existence form of the two–variable solver. -/
theorem bezout_two_exists (a b c : ℤ) (h : (Int.gcd a b : ℤ) ∣ c) :
    ∃ x y : ℤ, a * x + b * y = c :=
  ⟨bezoutX a b c, bezoutY a b c, bezout_solve_spec a b c h⟩

/-! ## The gcd of a coefficient vector -/

/-- The (non-negative) gcd of all entries of a coefficient vector `a : Fin n → ℤ`,
    defined by folding `Int.gcd` over the vector.  `vecGcd 0 _ = 0` and
    `vecGcd (n+1) a = gcd (a 0) (vecGcd n (tail a))`. -/
def vecGcd : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0,     _ => 0
  | (n+1), a => (Int.gcd (a 0) (vecGcd n (Fin.tail a)) : ℤ)

/-! ## The `n`-variable constructive solver -/

/-- **Constructive linear Diophantine solver (existence with explicit witness).**

    If the gcd of the coefficient vector `a : Fin n → ℤ` divides the target `c`,
    then `a₁x₁ + … + aₙxₙ = c` has an integer solution.  The proof is fully
    constructive: it builds the witness `x` by recursion on `n`, peeling off one
    coordinate at a time and solving the two–variable Bézout problem
    `a₀·x₀ + (gcd of tail)·t = c` at each step. -/
theorem exists_vec_combo :
    ∀ (n : ℕ) (a : Fin n → ℤ) (c : ℤ),
      vecGcd n a ∣ c → ∃ x : Fin n → ℤ, ∑ i, a i * x i = c := by
  intro n
  induction n with
  | zero =>
      intro a c h
      simp only [vecGcd] at h
      have hc : c = 0 := zero_dvd_iff.mp h
      exact ⟨fun _ => 0, by simp [hc]⟩
  | succ n ih =>
      intro a c h
      simp only [vecGcd] at h
      -- `h : ↑(Int.gcd (a 0) (vecGcd n (Fin.tail a))) ∣ c`
      have hsolve := bezout_solve_spec (a 0) (vecGcd n (Fin.tail a)) c h
      -- The tail's gcd trivially divides `(tail gcd) * (Bézout y-component)`.
      have hdvd :
          vecGcd n (Fin.tail a)
            ∣ vecGcd n (Fin.tail a) * bezoutY (a 0) (vecGcd n (Fin.tail a)) c :=
        dvd_mul_right _ _
      obtain ⟨x', hx'⟩ :=
        ih (Fin.tail a)
          (vecGcd n (Fin.tail a) * bezoutY (a 0) (vecGcd n (Fin.tail a)) c) hdvd
      refine ⟨Fin.cons (bezoutX (a 0) (vecGcd n (Fin.tail a)) c) x', ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      -- `Fin.tail a i` is definitionally `a i.succ`, so `hx'` retypes directly.
      have hsum :
          (∑ i : Fin n, a i.succ * x' i)
            = vecGcd n (Fin.tail a) * bezoutY (a 0) (vecGcd n (Fin.tail a)) c := hx'
      rw [hsum]
      exact hsolve

/-- Existence corollary, packaged as a pure ∃-statement (the constructive content
    is in `exists_vec_combo`; this is the "yes-instance" half of the parent's
    `linear_bezout_n`, now proved rather than assumed). -/
theorem linear_solvable_of_gcd_dvd (n : ℕ) (a : Fin n → ℤ) (c : ℤ)
    (h : vecGcd n a ∣ c) : ∃ x : Fin n → ℤ, ∑ i, a i * x i = c :=
  exists_vec_combo n a c h

/-! ## Sanity checks (the solver computes) -/

-- `3·x + 5·y = 1` is solvable since `gcd 3 5 = 1 ∣ 1`.
example : ∃ x y : ℤ, 3 * x + 5 * y = 1 :=
  bezout_two_exists 3 5 1 (by decide)

-- `6·x + 4·y = 10` is solvable since `gcd 6 4 = 2 ∣ 10`.
example : ∃ x y : ℤ, 6 * x + 4 * y = 10 :=
  bezout_two_exists 6 4 10 (by decide)

end Hilbert10OQ04OQ03OQ01
