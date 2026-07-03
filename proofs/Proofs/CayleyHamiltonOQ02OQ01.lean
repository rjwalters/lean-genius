import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-
# Putzer's Algorithm for the Matrix Exponential — Algebraic Core

Putzer's algorithm computes the matrix exponential

  e^{tA} = ∑_{k=1}^n P_k(t) · ρ_{k-1}

**without diagonalizing A or computing eigenvectors**, using only the eigenvalues
λ_1, …, λ_n (the roots of the characteristic polynomial).  Here

  ρ_k = (A - λ_k · I) · … · (A - λ_1 · I),        ρ_0 = I,

and the scalar coefficients P_k(t) solve the triangular linear ODE system

  Ṗ_1 = λ_1 P_1,      P_1(0) = 1,
  Ṗ_k = λ_k P_k + P_{k-1},   P_k(0) = 0   (2 ≤ k ≤ n).

The completed proof differentiates M(t) := ∑_k P_k(t) ρ_{k-1} and, using the
telescoping identity below together with the ODE relations, shows Ṁ = A·M and
M(0) = I; ODE uniqueness against `NormedSpace.exp` then gives M(t) = e^{tA}.

## This file: the purely *algebraic* scaffolding

Everything here requires **no analysis** — it is the algebra that drives the
derivative computation Ṁ = A·M.  Note that `ρ_k` is an *ordered* product of the
(mutually commuting) factors `A - λ_i • 1`; since `Matrix n n R` is not a
`CommMonoid` we build it by the recursion `ρ_{k+1} = ρ_k · (A - λ_k • 1)`.

* `rho_succ`     : ρ_{k+1} = ρ_k · (A - λ_k • 1)                (definitional)
* `commute_A_rho`: A commutes with every ρ_k (each factor is a polynomial in A)
* `A_mul_rho`    : A · ρ_k = ρ_{k+1} + λ_k • ρ_k               — the *key telescoping identity*
* `rho_card`     : ρ_n = 0  when χ_A splits as ∏ (X - λ_i)     (Cayley–Hamilton truncation)
* `rho_succ_left`: ρ_{k+1} = (A - λ_k • 1) · ρ_k              (factor pulled to the left)
* `rho_mul_A`    : ρ_k · A = ρ_{k+1} + λ_k • ρ_k             (right telescoping identity)
* `A_mul_sum_rho`: A · ∑_k a_k • ρ_k = ∑_k a_k • (ρ_{k+1} + λ_k • ρ_k)   (sum-level telescoping)
* `putzer_shift_sum`: ∑_k a_k • ρ_{k+1} = ∑_k b_k • ρ_k  (index shift; uses ρ_m = 0)
* `A_mul_putzer_sum_closed`: A · ∑_k a_k • ρ_k = ∑_k (λ_k a_k + b_k) • ρ_k   (closed telescoped form)

`A_mul_rho` is precisely what converts the term-by-term derivative
d/dt (P_k ρ_{k-1}) = Ṗ_k ρ_{k-1} into a multiple of A, and `rho_card` is what makes
the boundary term P_n ρ_n vanish so the sum closes on itself.

The analytic completion (constructing P_k, differentiating the finite sum, and the
matrix-valued ODE-uniqueness step) is deferred to a companion development.

## Status
- [x] Algebraic core: complete, no sorries
- [ ] Analytic layer (P_k construction, Ṁ = A·M, ODE uniqueness): future work

## Mathlib dependencies
- `Matrix.aeval_self_charpoly` : Cayley–Hamilton (χ_A(A) = 0)
- `Fin.prod_univ_eq_prod_range`, `Finset.prod_range_succ`
- `Algebra.algebraMap_eq_smul_one`
-/

namespace PutzerMatrixExp

open Matrix Polynomial BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

/-- Putzer partial product, built by the ordered recursion
`ρ 0 = 1`, `ρ (k+1) = ρ k · (A - λ_k • 1)`.  The factors mutually commute, so this
is the ordinary product `∏_{i<k} (A - λ_i • 1)` written in a way that does not need
`Matrix n n R` to be a `CommMonoid`. -/
def rho (A : Matrix n n R) (lam : ℕ → R) : ℕ → Matrix n n R
  | 0 => 1
  | (k + 1) => rho A lam k * (A - lam k • (1 : Matrix n n R))

@[simp] lemma rho_zero (A : Matrix n n R) (lam : ℕ → R) : rho A lam 0 = 1 := rfl

/-- The defining recursion: `ρ_{k+1} = ρ_k · (A - λ_k • 1)`. -/
lemma rho_succ (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    rho A lam (k + 1) = rho A lam k * (A - lam k • (1 : Matrix n n R)) := rfl

/-- `A` commutes with each factor `A - λ_i • 1`. -/
lemma commute_A_factor (A : Matrix n n R) (lam : ℕ → R) (i : ℕ) :
    Commute A (A - lam i • (1 : Matrix n n R)) :=
  (Commute.refl A).sub_right ((Commute.one_right A).smul_right (lam i))

/-- `A` commutes with every partial product `ρ_k` (it is a polynomial in `A`). -/
lemma commute_A_rho (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    Commute A (rho A lam k) := by
  induction k with
  | zero => simp [rho]
  | succ k ih => rw [rho_succ]; exact ih.mul_right (commute_A_factor A lam k)

lemma A_comm_rho (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    A * rho A lam k = rho A lam k * A :=
  commute_A_rho A lam k

/-- **Key telescoping identity.** `A · ρ_k = ρ_{k+1} + λ_k • ρ_k`.

This is the algebraic engine of Putzer's algorithm: it lets the derivative of the
`k`-th term be re-expressed so the whole sum telescopes into `A · M`. -/
lemma A_mul_rho (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    A * rho A lam k = rho A lam (k + 1) + lam k • rho A lam k := by
  rw [rho_succ, A_comm_rho, mul_sub, mul_smul_comm, mul_one]
  abel

/-- Evaluation of a linear factor: `aeval A (X - C c) = A - c • 1`. -/
lemma aeval_X_sub_C (A : Matrix n n R) (c : R) :
    (aeval A) (X - C c) = A - c • (1 : Matrix n n R) := by
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- `ρ_k` is the evaluation at `A` of the (commutative, in `R[X]`) partial product
`∏_{i<k} (X - λ_i)`. -/
lemma rho_eq_aeval_prod (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    rho A lam k = (aeval A) (∏ i ∈ Finset.range k, (X - C (lam i))) := by
  induction k with
  | zero => simp [rho]
  | succ k ih =>
    rw [rho_succ, ih, Finset.prod_range_succ, map_mul, aeval_X_sub_C]

/-- **Cayley–Hamilton truncation.** When the characteristic polynomial splits as
`χ_A = ∏ i, (X - λ_i)`, the top partial product vanishes: `ρ_n = 0`.

This is what makes Putzer's sum finite (it stops at `n` terms) and forces the
boundary term `P_n ρ_n` to drop out of the derivative computation. -/
lemma rho_card {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (lam : ℕ → R)
    (hlam : A.charpoly = ∏ i : Fin n, (X - C (lam i))) :
    rho A lam n = 0 := by
  rw [rho_eq_aeval_prod, ← Fin.prod_univ_eq_prod_range (fun i => X - C (lam i)) n, ← hlam,
      Matrix.aeval_self_charpoly]

/-! ## Two-sided factor structure and the sum-level telescoping

The identities above suffice to run the derivative computation `Ṁ = A · M` purely
algebraically.  The factors `A - λ_i • 1` are polynomials in `A`, hence commute with
every `ρ_k`, so each factor may be pulled to *either* side; and multiplication of the whole
Putzer sum `∑_k a_k • ρ_k` by `A` telescopes term-by-term via `A_mul_rho`. -/

/-- The defining factor may be pulled to the **left**: `ρ_{k+1} = (A - λ_k • 1) · ρ_k`.
The complement of `rho_succ` (which multiplies on the right); the two agree because each
factor commutes with `ρ_k`. -/
lemma rho_succ_left (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    rho A lam (k + 1) = (A - lam k • (1 : Matrix n n R)) * rho A lam k := by
  have hcomm : Commute (rho A lam k) (A - lam k • (1 : Matrix n n R)) :=
    ((commute_A_rho A lam k).symm).sub_right
      ((Commute.one_right (rho A lam k)).smul_right (lam k))
  rw [rho_succ]; exact hcomm.eq

/-- **Right telescoping identity.** `ρ_k · A = ρ_{k+1} + λ_k • ρ_k`.
The mirror of `A_mul_rho`; identical because `A` commutes with `ρ_k`. -/
lemma rho_mul_A (A : Matrix n n R) (lam : ℕ → R) (k : ℕ) :
    rho A lam k * A = rho A lam (k + 1) + lam k • rho A lam k := by
  rw [← A_comm_rho, A_mul_rho]

/-- **Sum-level telescoping.** Multiplying the finite Putzer sum `∑_{k<m} a_k • ρ_k` by `A`
distributes into the term-by-term telescoped form

  `A · ∑_{k<m} a_k • ρ_k = ∑_{k<m} a_k • (ρ_{k+1} + λ_k • ρ_k)`.

This is exactly the algebraic content of the derivative computation `Ṁ = A · M` for
`M = ∑_k P_k • ρ_{k-1}`: it converts left-multiplication by `A` into a shift `ρ_k ↦ ρ_{k+1}`
plus a diagonal `λ_k` term, with no analysis involved.  Holds for arbitrary coefficients
`a : ℕ → R` over any `CommRing`. -/
lemma A_mul_sum_rho (A : Matrix n n R) (lam : ℕ → R) (a : ℕ → R) (m : ℕ) :
    A * ∑ k ∈ Finset.range m, a k • rho A lam k
      = ∑ k ∈ Finset.range m, a k • (rho A lam (k + 1) + lam k • rho A lam k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_smul_comm, A_mul_rho]

/-! ## Closing the telescope: the reindex-and-truncate step

`A_mul_sum_rho` leaves `A · ∑ a_k ρ_k` in the *un-closed* form `∑ a_k (ρ_{k+1} + λ_k ρ_k)`,
where the shift `ρ_k ↦ ρ_{k+1}` prevents a direct term-by-term comparison against
`Ṁ = ∑ Ṗ_k ρ_{k-1}`.  The two lemmas below close it back into a single `∑ c_k • ρ_k`.

The shift `∑_{k<m} a_k ρ_{k+1} = ∑_{k<m} b_k ρ_k` (with `b` the up-shift of `a`,
`b_0 = 0`, `b_{k+1} = a_k`) is where the Cayley–Hamilton truncation `ρ_m = 0` is
actually used: it kills the boundary term `a_{m-1} ρ_m` produced by the reindex, so the
shifted sum stays within `range m`.  Combining with the diagonal `λ_k a_k` term gives the
closed form `A · ∑ a_k ρ_k = ∑ (λ_k a_k + b_k) • ρ_k`, whose coefficient `λ_k a_k + b_k`
is exactly the right-hand side of the Putzer ODE `Ṗ_k = λ_k P_k + P_{k-1}`.  Matching this
against `Ṁ = ∑ Ṗ_k ρ_{k-1}` reduces the matrix identity `Ṁ = A·M` to the scalar ODE system,
with no analysis in this step. -/

/-- **Index-shift with truncation.**  With `b` the up-shift of `a` (`b 0 = 0`,
`b (k+1) = a k`) and the boundary vanishing `ρ_m = 0`, the shifted Putzer sum reindexes
back onto `range m`:

  `∑_{k<m} a_k • ρ_{k+1} = ∑_{k<m} b_k • ρ_k`.

The truncation `ρ_m = 0` is what discards the boundary term `a_{m-1} ρ_m` created by the
reindex. -/
lemma putzer_shift_sum (A : Matrix n n R) (lam a b : ℕ → R) {m : ℕ}
    (hb0 : b 0 = 0) (hb : ∀ k, b (k + 1) = a k) (hm : rho A lam m = 0) :
    ∑ k ∈ Finset.range m, a k • rho A lam (k + 1)
      = ∑ k ∈ Finset.range m, b k • rho A lam k := by
  set g : ℕ → Matrix n n R := fun k => b k • rho A lam k with hg
  have hg0 : g 0 = 0 := by simp [hg, hb0]
  have hgm : g m = 0 := by simp [hg, hm]
  have key : ∑ k ∈ Finset.range m, a k • rho A lam (k + 1)
      = ∑ k ∈ Finset.range m, g (k + 1) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hg, hb]
  have h1 : ∑ k ∈ Finset.range (m + 1), g k = ∑ k ∈ Finset.range m, g (k + 1) := by
    rw [Finset.sum_range_succ', hg0, add_zero]
  have h2 : ∑ k ∈ Finset.range (m + 1), g k = ∑ k ∈ Finset.range m, g k := by
    rw [Finset.sum_range_succ, hgm, add_zero]
  rw [key, ← h1, h2]

/-- **Closed telescoped form of `A · M`.**  For the Putzer sum `M = ∑_{k<m} a_k • ρ_k`,
with `b` the up-shift of the coefficients (`b 0 = 0`, `b (k+1) = a k`) and the truncation
`ρ_m = 0`,

  `A · ∑_{k<m} a_k • ρ_k = ∑_{k<m} (λ_k · a_k + b_k) • ρ_k`.

The coefficient `λ_k a_k + b_k = λ_k a_k + a_{k-1}` is precisely the right-hand side of the
Putzer ODE `Ṗ_k = λ_k P_k + P_{k-1}`.  Thus once the scalar coefficients `P_k` satisfy their
ODE, this identity gives `Ṁ = A · M` term-by-term — the entire matrix content of the
derivative computation, discharged algebraically over any `CommRing`. -/
lemma A_mul_putzer_sum_closed (A : Matrix n n R) (lam a b : ℕ → R) {m : ℕ}
    (hb0 : b 0 = 0) (hb : ∀ k, b (k + 1) = a k) (hm : rho A lam m = 0) :
    A * ∑ k ∈ Finset.range m, a k • rho A lam k
      = ∑ k ∈ Finset.range m, (lam k * a k + b k) • rho A lam k := by
  rw [A_mul_sum_rho]
  have expand : ∀ k, a k • (rho A lam (k + 1) + lam k • rho A lam k)
      = a k • rho A lam (k + 1) + (lam k * a k) • rho A lam k := by
    intro k
    rw [smul_add, smul_smul, mul_comm (a k) (lam k)]
  rw [Finset.sum_congr rfl (fun k _ => expand k), Finset.sum_add_distrib,
      putzer_shift_sum A lam a b hb0 hb hm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← add_smul, add_comm (b k) (lam k * a k)]

end PutzerMatrixExp
