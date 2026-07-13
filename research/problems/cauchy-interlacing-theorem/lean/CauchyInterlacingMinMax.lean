import Mathlib

/-
# Courant–Fischer k-th max–min — keystone leaf lemmas for Cauchy interlacing

Operator-level companion to the matrix statement of record
(`CauchyInterlacing.lean`, branch `research/cauchy-interlacing-statement`). Via
the spectral theorem the matrix interlacing theorem reduces to the k-th
Courant–Fischer max–min variational characterisation of the descending
eigenvalue, which Mathlib lacks: only the *extreme* (top/bottom) Rayleigh
quotients are available
(`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` /
`_iInf_of_finiteDimensional`).

This file isolates the two **closed** (known-mathematics) leaf lemmas the
keystone is built from, as concrete proof targets — the leaf dependencies that,
per the design (`approaches/keystone-minmax-proof-design.md` §5), should be
discharged first (e.g. by Aristotle `prove_file`) because everything else is
bookkeeping over them.

- `Sublemma B` (`inf_exists_ne_zero_of_finrank_add_gt`) — nontrivial intersection
  by a dimension count. Pure linear algebra; a proof is attempted below.
- `Sublemma A` (`rayleigh_mem_Icc_of_mem_eigenspan`) — the Rayleigh quotient on
  the span of a sub-family of eigenvectors lies between the min and max of the
  corresponding eigenvalues (a convex-combination bound). Stated; proof deferred.
- The keystone max–min identity (`eigenvalue_eq_iSup_iInf_rayleigh`) is stated
  over the operator setting and left `sorry`; its proof is §2 of the design,
  built from Sublemmas A and B.

Status: research skeleton, **build-pending** — no backend was available the
session this was written (Aristotle MCP `prove` → 404; Docker pool saturated at
3 `lean-build` containers on the 7.65 GiB VM). NOT registered in `Proofs.lean`.
-/

namespace CauchyInterlacing.MinMax

open Module

/-- **Sublemma B** (nontrivial intersection by dimension count). Two subspaces of
a finite-dimensional space whose dimensions sum to strictly more than the ambient
dimension meet in a nonzero vector. This is the codimension count the textbook
interlacing proof hides in "two subspaces whose dimensions sum to more than `n`
must intersect". Pure linear algebra — no inner-product structure needed. -/
theorem inf_exists_ne_zero_of_finrank_add_gt
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    (V W : Submodule 𝕜 E)
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) :
    ∃ x ∈ V ⊓ W, x ≠ 0 := by
  have hsum :
      finrank 𝕜 (V ⊔ W : Submodule 𝕜 E) + finrank 𝕜 (V ⊓ W : Submodule 𝕜 E)
        = finrank 𝕜 V + finrank 𝕜 W :=
    Submodule.finrank_sup_add_finrank_inf_eq V W
  have hle : finrank 𝕜 (V ⊔ W : Submodule 𝕜 E) ≤ finrank 𝕜 E :=
    Submodule.finrank_le _
  have hpos : 0 < finrank 𝕜 (V ⊓ W : Submodule 𝕜 E) := by omega
  have hne : (V ⊓ W : Submodule 𝕜 E) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact (lt_irrefl 0) hpos
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

/-- The (real part of the) Rayleigh quotient of a symmetric operator `T` at a
nonzero vector `x`: `re ⟪T x, x⟫ / ‖x‖ ^ 2`. Kept as a local definition so the
whole development stays on one spelling (the design flags the
`ContinuousLinearMap.rayleighQuotient` / `LinearMap` coercion detour as a
hazard). -/
noncomputable def rayleigh {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (T : E →ₗ[𝕜] E) (x : E) : ℝ :=
  RCLike.re (inner (T x) x : 𝕜) / ‖x‖ ^ 2

/-- **Sublemma A** (Rayleigh bounds on a coordinate eigenspan). Let `T` be a
symmetric operator on a finite-dimensional inner product space with orthonormal
eigenbasis `b` and eigenvalues `μ`. For a `Finset I` of eigenindices and any
nonzero `x` in the span of `{b i : i ∈ I}`, the Rayleigh quotient `rayleigh T x`
lies between the min and the max of `{μ i : i ∈ I}` — it is a convex combination
of those eigenvalues with Parseval weights `‖⟪b i, x⟫‖² / ‖x‖²`.

This is the workhorse of the keystone: taking `I = {0,…,k}` gives `rayleigh ≥ μ k`
on the lower witness span, and `I = {k,…,n-1}` gives `rayleigh ≤ μ k` on the
upper span. Proof deferred (design §1, Sublemma A): two Parseval expansions plus
a convex-combination sandwich. -/
theorem rayleigh_mem_Icc_of_mem_eigenspan
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n)
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (I : Finset (Fin n)) (hI : I.Nonempty)
    (x : E) (hx : x ≠ 0)
    (hmem : x ∈ Submodule.span 𝕜 ((hT.eigenvectorBasis hn) '' (I : Set (Fin n)))) :
    (I.inf' hI (hT.eigenvalues hn)) ≤ rayleigh T x ∧
      rayleigh T x ≤ (I.sup' hI (hT.eigenvalues hn)) := by
  sorry

/-- **Keystone — k-th Courant–Fischer max–min identity** (operator form,
descending convention). The `k`-th descending eigenvalue of a symmetric operator
equals the maximum over `(k+1)`-dimensional subspaces `S` of the minimum Rayleigh
quotient over nonzero `x ∈ S`.

Proof (design §2): the witness span `span {b 0,…,b k}` realises `≥` via Sublemma A
(min of the decreasing `μ` over `{0,…,k}` is `μ k`); for `≤`, any `(k+1)`-dim `S`
meets `span {b k,…,b (n-1)}` (dimensions `(k+1)+(n-k) = n+1 > n`, Sublemma B) in a
nonzero vector with Rayleigh `≤ μ k` (Sublemma A). Boundedness obligations
(`BddBelow`/`BddAbove` for the `ciInf`/`ciSup`) are discharged from Sublemma A
with `I = univ`. The dual min–max form follows by applying this to `-T`. -/
theorem eigenvalue_eq_iSup_iInf_rayleigh
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n)
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric) (k : Fin n) :
    hT.eigenvalues hn k
      = ⨆ S : {S : Submodule 𝕜 E // finrank 𝕜 S = (k : ℕ) + 1},
          ⨅ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, rayleigh T x := by
  sorry

end CauchyInterlacing.MinMax
