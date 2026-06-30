import Mathlib

/-
# Hellinger–Toeplitz is sharp: completeness cannot be dropped

The **Hellinger–Toeplitz theorem** states that a symmetric, *everywhere-defined* linear
operator `T` on a Hilbert space is automatically continuous (bounded), and hence a bounded
self-adjoint operator.  In Mathlib this is `LinearMap.IsSymmetric.continuous`, proved via the
closed graph theorem, with the bundling into a bounded self-adjoint operator supplied by
`LinearMap.IsSymmetric.toSelfAdjoint`.  The hypothesis that `T` is everywhere defined is what
makes this surprising: for *densely* defined symmetric operators (the typical situation in
quantum mechanics, e.g. position and momentum) unboundedness is the norm.

The forward theorem crucially uses **completeness** of the space.  This entry proves that the
completeness hypothesis is *sharp* — it cannot be dropped — by exhibiting, on an explicit
**incomplete** inner product space, an everywhere-defined symmetric operator that is **not
bounded**.

The space is `ℕ →₀ ℝ`, the finitely supported real sequences, equipped with the `ℓ²` inner
product `⟪x, y⟫ = ∑ᵢ xᵢ yᵢ` (a finite sum since the sequences have finite support).  Its
completion is the Hilbert space `ℓ²(ℕ)`, but the space itself is a proper dense subspace and so
is not complete.  On it we put the **diagonal operator**

      `D x = (n ↦ n · xₙ)`,

which is everywhere defined, linear, and symmetric, yet sends the unit basis vector `eₖ` to
`k · eₖ`, so `‖D eₖ‖ / ‖eₖ‖ = k → ∞`: `D` is unbounded.

The punchline is a clean structural consequence: because Mathlib's Hellinger–Toeplitz theorem
forces every symmetric operator on a *complete* space to be continuous, the mere existence of
our symmetric **discontinuous** `D` re-proves that the finitely supported `ℓ²` space is **not
complete** (`not_completeSpace`).

All results are fully machine-checked with no axioms or sorries.  The forward Hellinger–Toeplitz
statement is recorded for context and is a thin wrapper around Mathlib; the original content is
the sharpness construction and its consequences.
-/

namespace HellingerToeplitzSharp

open scoped BigOperators

/-! ## The `ℓ²` inner product on finitely supported sequences -/

/-- The `ℓ²` inner product on finitely supported real sequences:
`⟪x, y⟫ = ∑ᵢ xᵢ yᵢ`, a finite sum over the (finite) support of `x`. -/
def ip (x y : ℕ →₀ ℝ) : ℝ := x.sum fun i a => a * y i

/-- `ip` written as a finite sum over any finset containing the support of its first argument. -/
theorem ip_eq_sum_of_subset (x y : ℕ →₀ ℝ) {s : Finset ℕ} (hs : x.support ⊆ s) :
    ip x y = ∑ i ∈ s, x i * y i := by
  rw [ip, Finsupp.sum]
  refine Finset.sum_subset hs ?_
  intro i _ hi
  rw [Finsupp.notMem_support_iff.1 hi, zero_mul]

/-- The inner product is symmetric. -/
theorem ip_comm (x y : ℕ →₀ ℝ) : ip x y = ip y x := by
  rw [ip_eq_sum_of_subset x y (s := x.support ∪ y.support) Finset.subset_union_left,
      ip_eq_sum_of_subset y x (s := x.support ∪ y.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Additivity in the first coordinate. -/
theorem ip_add_left (x y z : ℕ →₀ ℝ) : ip (x + y) z = ip x z + ip y z := by
  simp only [ip]
  exact Finsupp.sum_add_index' (fun i => by rw [zero_mul]) (fun i b₁ b₂ => by rw [add_mul])

/-- Homogeneity in the first coordinate. -/
theorem ip_smul_left (r : ℝ) (x y : ℕ →₀ ℝ) : ip (r • x) y = r * ip x y := by
  simp only [ip]
  rw [Finsupp.sum_smul_index' (fun i => by rw [zero_mul])]
  simp only [smul_eq_mul, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The inner product is positive semidefinite. -/
theorem ip_self_nonneg (x : ℕ →₀ ℝ) : 0 ≤ ip x x := by
  rw [ip, Finsupp.sum]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- The inner product is definite. -/
theorem ip_definite (x : ℕ →₀ ℝ) (h : ip x x = 0) : x = 0 := by
  rw [ip, Finsupp.sum] at h
  have hz : ∀ i ∈ x.support, x i * x i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg _).1 h
  ext i
  by_cases hi : i ∈ x.support
  · rw [Finsupp.zero_apply, ← mul_self_eq_zero]
    exact hz i hi
  · rw [Finsupp.notMem_support_iff.1 hi, Finsupp.zero_apply]

/-- The inner product of a basis-like single with itself. -/
theorem ip_single_self (k : ℕ) (a : ℝ) :
    ip (Finsupp.single k a) (Finsupp.single k a) = a * a := by
  rw [ip_eq_sum_of_subset _ _ (s := {k}) Finsupp.support_single_subset,
      Finset.sum_singleton, Finsupp.single_eq_same]

/-! ## The inner product space structure on `ℕ →₀ ℝ` -/

instance : Inner ℝ (ℕ →₀ ℝ) := ⟨ip⟩

theorem real_inner_eq (x y : ℕ →₀ ℝ) : (inner ℝ x y : ℝ) = ip x y := rfl

noncomputable instance instNAG : NormedAddCommGroup (ℕ →₀ ℝ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (ℕ →₀ ℝ) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by
        simp only [starRingEnd_apply, star_trivial]; exact ip_comm y x
      re_inner_nonneg := fun x => ip_self_nonneg x
      definite := fun x h => ip_definite x h
      add_left := fun x y z => ip_add_left x y z
      smul_left := fun x y r => by
        simp only [starRingEnd_apply, star_trivial]; exact ip_smul_left r x y }

noncomputable instance : InnerProductSpace ℝ (ℕ →₀ ℝ) := InnerProductSpace.ofCore _

/-- The norm of a nonnegative single equals its value. -/
theorem norm_single {k : ℕ} {a : ℝ} (ha : 0 ≤ a) : ‖Finsupp.single k a‖ = a := by
  have hsq : ‖Finsupp.single k a‖ * ‖Finsupp.single k a‖ = a * a := by
    rw [← real_inner_self_eq_norm_mul_norm, real_inner_eq, ip_single_self]
  exact (mul_self_inj (norm_nonneg _) ha).1 hsq

/-! ## The unbounded symmetric diagonal operator -/

/-- The diagonal-weighted sequence `n ↦ n · xₙ` has finite support. -/
theorem diag_support_finite (x : ℕ →₀ ℝ) :
    (Function.support fun i : ℕ => (i : ℝ) * x i).Finite := by
  refine Set.Finite.subset x.support.finite_toSet ?_
  intro i hi
  simp only [Function.mem_support] at hi
  exact Finsupp.mem_support_iff.2 fun h => hi (by rw [h, mul_zero])

/-- The everywhere-defined **diagonal operator** `D x = (n ↦ n · xₙ)`. -/
noncomputable def D : (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) where
  toFun x := Finsupp.ofSupportFinite (fun i : ℕ => (i : ℝ) * x i) (diag_support_finite x)
  map_add' x y := by
    ext i
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.add_apply, mul_add]
  map_smul' r x := by
    ext i
    simp only [Finsupp.ofSupportFinite_coe, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp] theorem D_apply (x : ℕ →₀ ℝ) (i : ℕ) : D x i = (i : ℝ) * x i := rfl

/-- `D` maps the unit basis vector `eₖ = single k 1` to `k · eₖ = single k k`. -/
theorem D_single (k : ℕ) : D (Finsupp.single k (1 : ℝ)) = Finsupp.single k (k : ℝ) := by
  ext i
  rw [D_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

/-- `D` is **symmetric**: `⟪D x, y⟫ = ⟪x, D y⟫` for all `x, y`. -/
theorem D_isSymmetric : (D).IsSymmetric := by
  intro x y
  rw [real_inner_eq, real_inner_eq]
  have hsub1 : (D x).support ⊆ x.support ∪ y.support := by
    refine Finset.Subset.trans ?_ Finset.subset_union_left
    intro i hi
    rw [Finsupp.mem_support_iff] at hi ⊢
    exact fun hx => hi (by rw [D_apply, hx, mul_zero])
  have hsub2 : (D y).support ⊆ x.support ∪ y.support := by
    refine Finset.Subset.trans ?_ Finset.subset_union_right
    intro i hi
    rw [Finsupp.mem_support_iff] at hi ⊢
    exact fun hy => hi (by rw [D_apply, hy, mul_zero])
  rw [ip_comm x (D y), ip_eq_sum_of_subset (D x) y hsub1,
      ip_eq_sum_of_subset (D y) x hsub2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D_apply, D_apply]; ring

/-- `D` is **not continuous**: it is unbounded, witnessed by `‖D eₖ‖ = k‖eₖ‖`. -/
theorem D_not_continuous : ¬ Continuous (D : (ℕ →₀ ℝ) → (ℕ →₀ ℝ)) := by
  intro hcont
  obtain ⟨C, _, hbound⟩ := SemilinearMapClass.bound_of_continuous D hcont
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have h1 : ‖Finsupp.single k (1 : ℝ)‖ = 1 := norm_single zero_le_one
  have h2 : ‖D (Finsupp.single k (1 : ℝ))‖ = (k : ℝ) := by
    rw [D_single, norm_single (Nat.cast_nonneg k)]
  have hb := hbound (Finsupp.single k (1 : ℝ))
  rw [h1, h2, mul_one] at hb
  linarith

/-! ## Sharpness: completeness is necessary

A symmetric operator on a *complete* inner product space is continuous (the Hellinger–Toeplitz
theorem, `LinearMap.IsSymmetric.continuous`).  Our `D` is symmetric but discontinuous, so the
space it lives on cannot be complete. -/

/-- The finitely supported `ℓ²` space is **not complete**: a clean corollary of the existence of
a symmetric discontinuous operator, via the contrapositive of Hellinger–Toeplitz. -/
theorem not_completeSpace : ¬ CompleteSpace (ℕ →₀ ℝ) := by
  intro hcomplete
  haveI := hcomplete
  exact D_not_continuous D_isSymmetric.continuous

/-! ## The forward Hellinger–Toeplitz theorem (context, from Mathlib)

For contrast, the forward direction: on a *complete* inner product space the symmetry hypothesis
alone forces continuity, and the operator is then a bounded self-adjoint operator.  This is a thin
wrapper around Mathlib's `LinearMap.IsSymmetric.continuous`; it is recorded only to frame the
sharpness result above. -/

/-- **Hellinger–Toeplitz theorem.** A symmetric everywhere-defined operator on a complete inner
product space is continuous. -/
theorem hellinger_toeplitz {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    Continuous T := hT.continuous

/-- On a complete space, a symmetric operator bundles into a bounded **self-adjoint** operator. -/
theorem hellinger_toeplitz_selfAdjoint {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    IsSelfAdjoint (hT.toSelfAdjoint : E →L[𝕜] E) :=
  (hT.toSelfAdjoint).2

/-! ## Sanity checks confirming the hypotheses are not vacuous -/

/-- `D` genuinely moves vectors: `D e₂ = 2 e₂ ≠ e₂`. -/
example : D (Finsupp.single 2 (1 : ℝ)) = Finsupp.single 2 (2 : ℝ) := by
  rw [D_single]; norm_num

/-- The unbounded growth is explicit: `‖D eₖ‖ = k`. -/
example (k : ℕ) : ‖D (Finsupp.single k (1 : ℝ))‖ = (k : ℝ) := by
  rw [D_single, norm_single (Nat.cast_nonneg k)]

end HellingerToeplitzSharp
