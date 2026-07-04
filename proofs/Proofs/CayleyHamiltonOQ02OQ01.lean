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

`A_mul_rho` is precisely what converts the term-by-term derivative
d/dt (P_k ρ_{k-1}) = Ṗ_k ρ_{k-1} into a multiple of A, and `rho_card` is what makes
the boundary term P_n ρ_n vanish so the sum closes on itself.

The analytic completion (constructing P_k, differentiating the finite sum, and the
matrix-valued ODE-uniqueness step) is deferred to a companion development.

## Status
- [x] Algebraic core: complete, no sorries
- [x] Algebraic form of `Ṁ = A·M` (`A_mul_putzer_sum` / `A_mul_putzer_sum_charpoly`): the ODE
      identity reduced to pure algebra, with the Cayley–Hamilton truncation discharging the
      boundary term — no analysis
- [ ] Analytic layer (P_k construction as ODE solutions, term-by-term differentiation of the
      finite sum, matrix-valued ODE uniqueness against `NormedSpace.exp`): future work

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

/-! ## The algebraic form of `Ṁ = A · M` (the analytic bridge)

The Putzer solution is `M(t) = ∑_{k<n} P_k(t) • ρ_k`, where the scalar coefficients satisfy the
triangular ODE system `Ṗ_k = λ_k P_k + P_{k-1}` (with the convention `P_{-1} ≡ 0`).  Differentiating
term-by-term gives `Ṁ = ∑_{k<n} (λ_k P_k + P_{k-1}) • ρ_k`.  The claim that Putzer's formula solves
`Ṁ = A · M` is therefore, *before any analysis is invoked*, the purely algebraic identity

  `A · ∑_{k<n} P_k • ρ_k = ∑_{k<n} (λ_k P_k + P_{k-1}) • ρ_k`.

The two lemmas below isolate exactly this identity and show that it holds **precisely because the
Cayley–Hamilton truncation `ρ_n = 0` kills the boundary term** `P_{n-1} • ρ_n`.  The `P_{k-1}`
convention (`P_{-1} = 0`) is encoded cleanly, without `ℕ`-subtraction, by a second coefficient
family `Pprev` with `Pprev 0 = 0` and `Pprev (k+1) = P k`. -/

/-- Re-indexing the shifted Putzer sum.  With `Pprev 0 = 0` and `Pprev (k+1) = P k` (so `Pprev`
plays the role of `k ↦ P_{k-1}`), the sum of `P_k • ρ_{k+1}` over `k < m` equals the sum of
`Pprev_k • ρ_k` over `k < m + 1`.  Pure book-keeping via `Finset.sum_range_succ'`. -/
lemma sum_P_rho_succ (A : Matrix n n R) (lam P Pprev : ℕ → R)
    (h0 : Pprev 0 = 0) (hsucc : ∀ k, Pprev (k + 1) = P k) (m : ℕ) :
    ∑ k ∈ Finset.range m, P k • rho A lam (k + 1)
      = ∑ k ∈ Finset.range (m + 1), Pprev k • rho A lam k := by
  rw [Finset.sum_range_succ']
  simp only [hsucc, h0, zero_smul, add_zero]

/-- **Algebraic `Ṁ = A · M`.**  For the Putzer sum `M = ∑_{k<m} P_k • ρ_k`, multiplication by `A`
reproduces the derivative coefficients `λ_k P_k + P_{k-1}` **as soon as the boundary product
`ρ_m = 0` vanishes**:

  `A · ∑_{k<m} P_k • ρ_k = ∑_{k<m} (λ_k P_k + Pprev_k) • ρ_k`.

Here `Pprev` encodes `k ↦ P_{k-1}` (with `Pprev 0 = 0`).  The single hypothesis `hbdry : ρ_m = 0`
is what makes the identity close: it deletes the otherwise-leftover term `P_{m-1} • ρ_m`.  This is
the purely algebraic heart of Putzer's ODE argument — no analysis, over any `CommRing`. -/
lemma A_mul_putzer_sum (A : Matrix n n R) (lam P Pprev : ℕ → R)
    (h0 : Pprev 0 = 0) (hsucc : ∀ k, Pprev (k + 1) = P k) (m : ℕ)
    (hbdry : rho A lam m = 0) :
    A * ∑ k ∈ Finset.range m, P k • rho A lam k
      = ∑ k ∈ Finset.range m, (lam k * P k + Pprev k) • rho A lam k := by
  have hshift : ∑ k ∈ Finset.range m, P k • rho A lam (k + 1)
      = ∑ k ∈ Finset.range m, Pprev k • rho A lam k := by
    rw [sum_P_rho_succ A lam P Pprev h0 hsucc, Finset.sum_range_succ, hbdry, smul_zero,
      add_zero]
  calc A * ∑ k ∈ Finset.range m, P k • rho A lam k
      = ∑ k ∈ Finset.range m, P k • (rho A lam (k + 1) + lam k • rho A lam k) :=
        A_mul_sum_rho A lam P m
    _ = ∑ k ∈ Finset.range m, (P k • rho A lam (k + 1) + (lam k * P k) • rho A lam k) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [smul_add, smul_smul, mul_comm (P k) (lam k)]
    _ = (∑ k ∈ Finset.range m, P k • rho A lam (k + 1))
          + ∑ k ∈ Finset.range m, (lam k * P k) • rho A lam k := Finset.sum_add_distrib
    _ = (∑ k ∈ Finset.range m, (lam k * P k) • rho A lam k)
          + ∑ k ∈ Finset.range m, Pprev k • rho A lam k := by rw [hshift, add_comm]
    _ = ∑ k ∈ Finset.range m, ((lam k * P k) • rho A lam k + Pprev k • rho A lam k) :=
        Finset.sum_add_distrib.symm
    _ = ∑ k ∈ Finset.range m, (lam k * P k + Pprev k) • rho A lam k := by
        refine Finset.sum_congr rfl (fun k _ => ?_); rw [add_smul]

/-- **Putzer `Ṁ = A · M`, boundary supplied by Cayley–Hamilton.**  When `χ_A = ∏ i, (X - λ_i)`,
the truncation `ρ_n = 0` (`rho_card`) automatically discharges the boundary term, so the algebraic
`Ṁ = A · M` identity holds at the full length `n` with no side condition beyond the eigenvalue
factorization:

  `A · ∑_{k<n} P_k • ρ_k = ∑_{k<n} (λ_k P_k + P_{k-1}) • ρ_k`.

This is the exact statement the deferred analytic layer will differentiate against: once `P_k` are
the ODE coefficients, the left side is `A · M(t)` and the right side is `Ṁ(t)`. -/
lemma A_mul_putzer_sum_charpoly {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (lam P Pprev : ℕ → R)
    (h0 : Pprev 0 = 0) (hsucc : ∀ k, Pprev (k + 1) = P k)
    (hlam : A.charpoly = ∏ i : Fin n, (X - C (lam i))) :
    A * ∑ k ∈ Finset.range n, P k • rho A lam k
      = ∑ k ∈ Finset.range n, (lam k * P k + Pprev k) • rho A lam k :=
  A_mul_putzer_sum A lam P Pprev h0 hsucc n (rho_card A lam hlam)

/-! ## The algebraic initial condition `M(0) = I`

Putzer's solution is `M(t) = ∑_{k<n} P_k(t) • ρ_k` with scalar coefficients satisfying
`P_0(0) = 1` and `P_k(0) = 0` for `k > 0` (the leading coefficient starts at `1`, all others at
`0`).  Evaluating the finite sum at `t = 0` collapses to the single `k = 0` term `P_0(0) • ρ_0 =
1 • 1 = 1`.  This is the second half of the IVP that pins down `e^{tA}`: together with the
`Ṁ = A · M` identity above, it algebraically characterizes the Putzer sum as *the* solution of
`Ṁ = A · M`, `M(0) = I` — before any analytic uniqueness statement is invoked.  Like everything
in this file it is pure `CommRing` book-keeping, holding for arbitrary evaluation coefficients. -/

/-- **Algebraic initial condition `M(0) = I`.**  If a coefficient family `c` has `c 0 = 1` and
`c k = 0` for every `k > 0`, then the Putzer sum collapses to the identity:

  `∑_{k<m} c_k • ρ_k = 1`   (for any `m ≥ 1`).

Only the `k = 0` term survives, and `ρ_0 = 1`, so the sum is `c_0 • 1 = 1`.  Applied with
`c k = P_k(0)` this is exactly `M(0) = I`. -/
lemma putzer_sum_initial (A : Matrix n n R) (lam c : ℕ → R)
    (h0 : c 0 = 1) (hpos : ∀ k, 0 < k → c k = 0) {m : ℕ} (hm : 0 < m) :
    ∑ k ∈ Finset.range m, c k • rho A lam k = 1 := by
  rw [Finset.sum_eq_single 0]
  · rw [rho_zero, h0, one_smul]
  · intro k _ hne
    rw [hpos k (Nat.pos_of_ne_zero hne), zero_smul]
  · intro h
    exact absurd (Finset.mem_range.mpr hm) h

/-- **Algebraic Putzer IVP at full length `n`.**  Assembling the two halves: when `χ_A` splits as
`∏ i, (X - λ_i)` and the coefficient family `P` has Putzer's initial data `P_0 = 1`, `P_k = 0`
for `k > 0` (with `Pprev` encoding `k ↦ P_{k-1}`), the finite matrix sum `M := ∑_{k<n} P_k • ρ_k`
satisfies **both** algebraic IVP conditions simultaneously:

  `A · M = ∑_{k<n} (λ_k P_k + P_{k-1}) • ρ_k`   (the `Ṁ = A·M` right-hand side), and   `M = 1`.

For `n ≥ 1` this is the complete algebraic skeleton of Putzer's theorem: once the deferred analytic
layer supplies coefficient *functions* `P_k(t)` whose values at `t = 0` are this data and whose
derivatives are `λ_k P_k + P_{k-1}`, the left equation reads `A · M(t) = Ṁ(t)` and the right reads
`M(0) = I`, so matrix-ODE uniqueness gives `M(t) = e^{tA}`. -/
lemma putzer_ivp_charpoly {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (lam P Pprev : ℕ → R)
    (h0 : Pprev 0 = 0) (hsucc : ∀ k, Pprev (k + 1) = P k)
    (hlam : A.charpoly = ∏ i : Fin n, (X - C (lam i)))
    (hP0 : P 0 = 1) (hPpos : ∀ k, 0 < k → P k = 0) (hn : 0 < n) :
    (A * ∑ k ∈ Finset.range n, P k • rho A lam k
        = ∑ k ∈ Finset.range n, (lam k * P k + Pprev k) • rho A lam k)
      ∧ (∑ k ∈ Finset.range n, P k • rho A lam k = 1) :=
  ⟨A_mul_putzer_sum_charpoly A lam P Pprev h0 hsucc hlam,
   putzer_sum_initial A lam P hP0 hPpos hn⟩

end PutzerMatrixExp
