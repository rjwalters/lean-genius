import Mathlib

/-
# Schur's majorization theorem (the forward / "Schur" direction of Schur–Horn)

The **Schur–Horn theorem** relates the diagonal entries of a Hermitian matrix to
its eigenvalue spectrum.  Its *forward* direction — due to **Issai Schur (1923)** —
says that the diagonal is **majorized** by the spectrum:

  `diag(A) ≺ spec(A)`.

This file formalizes that direction in the cleanest equivalent form, the one given
by the **Hardy–Littlewood–Pólya / Karamata** characterization of majorization:
a real tuple `d` is majorized by `λ` iff `∑ φ(dᵢ) ≤ ∑ φ(λⱼ)` for *every* convex
`φ`.  We prove exactly this inequality for the diagonal of an arbitrary symmetric
(Hermitian) operator with respect to *any* orthonormal basis.

## Mathematical content

Let `T` be a symmetric operator on a finite-dimensional inner product space over
`𝕜 = ℝ` or `ℂ`, with spectral data from Mathlib's `LinearMap.IsSymmetric`:
an orthonormal eigenbasis `v` (`hT.eigenvectorBasis hn`) and eigenvalues `λ`
(`hT.eigenvalues hn`).  Fix *any* orthonormal basis `e`.  The "diagonal" of `T` in
the basis `e` is the tuple

  `d i := re ⟪T (e i), e i⟫`.

The matrix `D i j := ‖⟪v j, e i⟫‖²` is **doubly stochastic** (rows and columns sum
to `1`, by Parseval), and the diagonal is the doubly-stochastic image of the
spectrum:

  `d i = ∑ j, D i j • λ j`     (each `d i` is a convex combination of eigenvalues).

The majorization inequality then follows by **Jensen** applied row-by-row and a
sum swap using the column sums:

  `∑ i, φ (d i) ≤ ∑ i ∑ j, D i j • φ (λ j) = ∑ j, (∑ i, D i j) • φ (λ j) = ∑ j, φ (λ j)`.

Specializations recorded here:
* `schur_trace_eq` — basis independence of the trace, `∑ d i = ∑ λ j` (the `k = n`
  equality case of majorization, needing no convexity);
* `schur_sum_sq_le` — `∑ (d i)² ≤ ∑ (λ j)²` (the `φ = (·)²` instance), i.e. the
  diagonal has no larger Euclidean length than the spectrum.

## Relation to Mathlib

Mathlib has the spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis`,
`eigenvalues`) and Birkhoff's theorem on doubly stochastic matrices
(`exists_eq_sum_perm_of_mem_doublyStochastic`), but it has **no majorization
predicate and no Schur–Horn theorem** (only a comment mentioning Schur–Horn in
`Mathlib.Analysis.InnerProductSpace.Spectrum`).  This file supplies the forward
direction in its convex-function (Karamata) form, which is self-contained: it
needs only Parseval, the spectral theorem, and Jensen's inequality — not Birkhoff.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open scoped BigOperators

namespace SchurHorn

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ}
  {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
  (e : OrthonormalBasis (Fin n) 𝕜 E)

/-- The doubly-stochastic weight matrix `D i j = ‖⟪v j, e i⟫‖²`, where `v` is the
orthonormal eigenbasis of `T` and `e` is the chosen orthonormal basis. -/
noncomputable def dsWeight (i j : Fin n) : ℝ :=
  ‖@inner 𝕜 E _ (hT.eigenvectorBasis hn j) (e i)‖ ^ 2

/-- Every weight is nonnegative (it is a squared norm). -/
theorem dsWeight_nonneg (i j : Fin n) : 0 ≤ dsWeight hT hn e i j :=
  sq_nonneg _

/-- **Rows sum to one.**  By Parseval for the eigenbasis `v`,
`∑ j, ‖⟪v j, e i⟫‖² = ‖e i‖² = 1`. -/
theorem dsWeight_row_sum (i : Fin n) : ∑ j, dsWeight hT hn e i j = 1 := by
  simp only [dsWeight]
  rw [(hT.eigenvectorBasis hn).sum_sq_norm_inner_right (e i),
      e.orthonormal.norm_eq_one i, one_pow]

/-- **Columns sum to one.**  By Parseval for the basis `e`,
`∑ i, ‖⟪v j, e i⟫‖² = ‖v j‖² = 1`. -/
theorem dsWeight_col_sum (j : Fin n) : ∑ i, dsWeight hT hn e i j = 1 := by
  simp only [dsWeight]
  rw [e.sum_sq_norm_inner_left (hT.eigenvectorBasis hn j),
      (hT.eigenvectorBasis hn).orthonormal.norm_eq_one j, one_pow]

/-- **Diagonal = doubly-stochastic image of the spectrum.**  The diagonal entry
`re ⟪T (e i), e i⟫` of `T` in the basis `e` is the convex combination
`∑ j, λ j · D i j` of the eigenvalues.  Expanding `e i` in the eigenbasis and using
`T v j = λ j • v j` together with `conj z · z = ‖z‖²`. -/
theorem diag_decomp (i : Fin n) :
    RCLike.re (@inner 𝕜 E _ (T (e i)) (e i))
      = ∑ j, hT.eigenvalues hn j * dsWeight hT hn e i j := by
  -- per-term identity in 𝕜
  have hsummand : ∀ j,
      @inner 𝕜 E _ (T (e i)) (hT.eigenvectorBasis hn j)
        * @inner 𝕜 E _ (hT.eigenvectorBasis hn j) (e i)
      = ((hT.eigenvalues hn j * dsWeight hT hn e i j : ℝ) : 𝕜) := by
    intro j
    have e1 : @inner 𝕜 E _ (hT.eigenvectorBasis hn j) (T (e i))
        = (hT.eigenvalues hn j : 𝕜) * @inner 𝕜 E _ (hT.eigenvectorBasis hn j) (e i) := by
      have h := LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply hT hn (e i) j
      rwa [(hT.eigenvectorBasis hn).repr_apply_apply,
           (hT.eigenvectorBasis hn).repr_apply_apply] at h
    rw [← inner_conj_symm (T (e i)) (hT.eigenvectorBasis hn j), e1, map_mul,
        RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    simp only [dsWeight]
    push_cast
    ring
  have hk : @inner 𝕜 E _ (T (e i)) (e i)
      = ∑ j, ((hT.eigenvalues hn j * dsWeight hT hn e i j : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner (T (e i)) (e i)]
    exact Finset.sum_congr rfl (fun j _ => hsummand j)
  rw [hk, map_sum]
  exact Finset.sum_congr rfl (fun j _ => RCLike.ofReal_re _)

/-- **Schur's majorization theorem (convex / Karamata form).**  For any convex
function `φ` on a set `s` containing all eigenvalues of the symmetric operator `T`,
the diagonal of `T` in *any* orthonormal basis `e` satisfies

  `∑ i, φ (re ⟪T (e i), e i⟫) ≤ ∑ j, φ (λ j)`.

This is the forward (Schur) direction of the Schur–Horn theorem: `diag T ≺ spec T`.
The proof is Jensen's inequality applied row-by-row to the doubly-stochastic matrix
`D i j = ‖⟪v j, e i⟫‖²`, followed by a sum swap using the column sums `∑ i, D i j = 1`. -/
theorem schur_majorization_convexOn {φ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ)
    (hmem : ∀ j, hT.eigenvalues hn j ∈ s) :
    ∑ i, φ (RCLike.re (@inner 𝕜 E _ (T (e i)) (e i))) ≤ ∑ j, φ (hT.eigenvalues hn j) := by
  -- Row-by-row Jensen.
  have step : ∀ i, φ (RCLike.re (@inner 𝕜 E _ (T (e i)) (e i)))
      ≤ ∑ j, dsWeight hT hn e i j • φ (hT.eigenvalues hn j) := by
    intro i
    have hJ := hφ.map_sum_le (t := Finset.univ) (w := fun j => dsWeight hT hn e i j)
      (p := fun j => hT.eigenvalues hn j)
      (fun j _ => dsWeight_nonneg hT hn e i j) (dsWeight_row_sum hT hn e i)
      (fun j _ => hmem j)
    have hsum : (∑ j, dsWeight hT hn e i j • hT.eigenvalues hn j)
        = RCLike.re (@inner 𝕜 E _ (T (e i)) (e i)) := by
      rw [diag_decomp hT hn e i]
      exact Finset.sum_congr rfl (fun j _ => by rw [smul_eq_mul, mul_comm])
    rwa [hsum] at hJ
  -- Sum the rows, swap, collapse columns.
  calc ∑ i, φ (RCLike.re (@inner 𝕜 E _ (T (e i)) (e i)))
      ≤ ∑ i, ∑ j, dsWeight hT hn e i j • φ (hT.eigenvalues hn j) :=
        Finset.sum_le_sum (fun i _ => step i)
    _ = ∑ j, (∑ i, dsWeight hT hn e i j) • φ (hT.eigenvalues hn j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_smul])
    _ = ∑ j, φ (hT.eigenvalues hn j) := by
        exact Finset.sum_congr rfl (fun j _ => by rw [dsWeight_col_sum hT hn e j, one_smul])

/-- **Basis independence of the trace** (the `k = n` equality case of majorization).
The sum of the diagonal entries of `T` in any orthonormal basis equals the sum of
its eigenvalues: `∑ i, re ⟪T (e i), e i⟫ = ∑ j, λ j`.  No convexity needed. -/
theorem schur_trace_eq :
    ∑ i, RCLike.re (@inner 𝕜 E _ (T (e i)) (e i)) = ∑ j, hT.eigenvalues hn j := by
  calc ∑ i, RCLike.re (@inner 𝕜 E _ (T (e i)) (e i))
      = ∑ i, ∑ j, hT.eigenvalues hn j * dsWeight hT hn e i j :=
        Finset.sum_congr rfl (fun i _ => diag_decomp hT hn e i)
    _ = ∑ j, hT.eigenvalues hn j * (∑ i, dsWeight hT hn e i j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    _ = ∑ j, hT.eigenvalues hn j := by
        exact Finset.sum_congr rfl (fun j _ => by rw [dsWeight_col_sum hT hn e j, mul_one])

/-- **Sum-of-squares bound** (the `φ = (·)²` instance of Schur majorization).  The
diagonal of `T` in any orthonormal basis has Euclidean length no larger than the
spectrum: `∑ i, (re ⟪T (e i), e i⟫)² ≤ ∑ j, (λ j)²`. -/
theorem schur_sum_sq_le :
    ∑ i, (RCLike.re (@inner 𝕜 E _ (T (e i)) (e i))) ^ 2 ≤ ∑ j, (hT.eigenvalues hn j) ^ 2 :=
  schur_majorization_convexOn hT hn e
    (φ := fun x => x ^ 2) (s := Set.univ)
    (Even.convexOn_pow (by decide)) (fun _ => Set.mem_univ _)

end SchurHorn
