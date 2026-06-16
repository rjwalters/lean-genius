import Mathlib

/-
# Cauchy interlacing — keystone leaf lemmas (Sublemma A & B), typed targets

These are the two *standalone* leaf lemmas that the Courant–Fischer max–min
keystone (the single Mathlib gap blocking Cauchy interlacing) reduces to. See
`approaches/keystone-minmax-proof-design.md` for the full mathematical proof and
the per-step Mathlib lemma map. That design recommends building / submitting
these two first because they are *closed* (known-mathematics, HARD-not-OPEN) and
have no upstream dependencies.

This file turns that prose design into machine-checked Lean. Sublemma B is the
Grassmann dimension count; Sublemma A is fully decomposed into its
convex-combination core `weighted_mean_mem_inf_sup`, the two Parseval leaf
identities `norm_sq_eq_sum_repr_sq` and `re_inner_apply_eq_sum_repr_mul` (both now
proved via the shared support lemma `repr_eq_zero_of_not_mem`), and the assembly
`rayleigh_bounds_on_eigenspan`.

## Status

VERIFIED — `sorry`-free, 0 axioms. Compiles against Mathlib (Lean v4.26.0) under
`docker-build.sh`. The two Parseval leaves were the last remaining `sorry`s and
are now discharged:
* `repr_eq_zero_of_not_mem` — coordinates vanish off the support, by `span`
  induction + orthonormality (`orthonormal_iff_ite`).
* `norm_sq_eq_sum_repr_sq` — `b.repr.norm_map` + `EuclideanSpace.norm_eq` +
  `Real.sq_sqrt`, then `Finset.sum_subset` to restrict to `I`.
* `repr_apply_of_diag` — `b.repr (T x) i = b.repr x i * μ i` via `sum_repr` +
  `inner_sum` + `Finset.sum_eq_single`.
* `re_inner_apply_eq_sum_repr_mul` — `b.repr.inner_map_map` + `PiLp.inner_apply` +
  `RCLike.mul_conj`/`conj_ofReal`, then restrict and take `re`.

Not registered in `Proofs.lean` (research file). The remaining open obligation for
the problem is the Courant–Fischer max–min keystone itself
(`CauchyInterlacing.lean:95`), which these sublemmas feed.
-/

open scoped InnerProductSpace

namespace CauchyInterlacing.Sublemmas

/-! ## Sublemma B — nontrivial intersection by dimension count

Pure finite-dimensional linear algebra; no inner product needed. This is the
codimension count the textbook proof hides in "two subspaces whose dimensions
sum to more than `n` must meet".

Proof route (design §1.B): `Submodule.finrank_sup_add_finrank_inf_eq V W` gives
`finrank (V ⊔ W) + finrank (V ⊓ W) = finrank V + finrank W`; with
`finrank (V ⊔ W) ≤ finrank E` (`Submodule.finrank_le`) rearrange to
`finrank (V ⊓ W) ≥ finrank V + finrank W − finrank E ≥ 1 > 0`; positive finrank
⇒ `≠ ⊥` ⇒ has a nonzero element. Proof below follows exactly this route. -/
theorem inf_ne_bot_of_finrank_add_lt
    {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] (V W : Submodule 𝕜 E)
    (h : Module.finrank 𝕜 E < Module.finrank 𝕜 V + Module.finrank 𝕜 W) :
    ∃ x ∈ V ⊓ W, x ≠ 0 := by
  -- The Grassmann/dimension formula: `dim(V⊔W) + dim(V⊓W) = dim V + dim W`.
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq V W
  -- The join sits inside the ambient space, so its dimension is bounded by `dim E`.
  have hle : Module.finrank 𝕜 (V ⊔ W : Submodule 𝕜 E) ≤ Module.finrank 𝕜 E :=
    Submodule.finrank_le _
  -- Hence the intersection has strictly positive dimension.
  have hpos : 0 < Module.finrank 𝕜 (V ⊓ W : Submodule 𝕜 E) := by omega
  -- Positive dimension rules out the trivial subspace.
  have hne : (V ⊓ W : Submodule 𝕜 E) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpos
    simp at hpos
  -- A nontrivial subspace contains a nonzero vector.
  exact (Submodule.ne_bot_iff _).1 hne

/-! ## Sublemma A.0 — a weighted mean lies between min and max (the convex-combination core)

This is the purely order-theoretic / real-arithmetic heart of Sublemma A, isolated
as a standalone lemma with **no inner-product or eigenbasis content**. Once the two
Parseval identities reduce the Rayleigh quotient to
`(∑_{i∈I} wᵢ μᵢ) / (∑_{i∈I} wᵢ)` with weights `wᵢ = ‖cᵢ‖² ≥ 0` and positive total
mass, the min/max sandwich is exactly this lemma applied with that `w`.

Proof: with `S := ∑_{i∈I} wᵢ > 0`, clear the denominator (`le_div_iff₀` /
`div_le_iff₀`) and compare termwise. For the lower bound,
`inf'·S = ∑ inf'·wᵢ ≤ ∑ μᵢ·wᵢ` because `inf' ≤ μᵢ` (`Finset.inf'_le`) and `wᵢ ≥ 0`;
the upper bound is symmetric via `Finset.le_sup'`. Fully elementary, no `sorry`. -/
theorem weighted_mean_mem_inf_sup
    {n : ℕ} (μ : Fin n → ℝ) (I : Finset (Fin n)) (hI : I.Nonempty)
    (w : Fin n → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) (hpos : 0 < ∑ i ∈ I, w i) :
    I.inf' hI μ ≤ (∑ i ∈ I, w i * μ i) / (∑ i ∈ I, w i)
      ∧ (∑ i ∈ I, w i * μ i) / (∑ i ∈ I, w i) ≤ I.sup' hI μ := by
  refine ⟨?_, ?_⟩
  · -- lower bound: clear denominator, then `inf' ≤ μᵢ` weighted by `wᵢ ≥ 0`
    rw [le_div_iff₀ hpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_comm (I.inf' hI μ) (w i)]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le μ hi) (hw i hi)
  · -- upper bound: symmetric, `μᵢ ≤ sup'` weighted by `wᵢ ≥ 0`
    rw [div_le_iff₀ hpos, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_comm (I.sup' hI μ) (w i)]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' μ hi) (hw i hi)

/-! ## Sublemma A — Rayleigh bounds on a coordinate eigenspan

If `T` is diagonalised by the orthonormal family `b` with real eigenvalues `μ`,
then for any nonzero `x` in the span of the sub-family `b '' I` the Rayleigh
quotient `R x = re ⟪T x, x⟫ / ‖x‖²` is a convex combination of `{μ i : i ∈ I}`,
hence sandwiched between `min_{i∈I} μ i` and `max_{i∈I} μ i`.

Proof route (design §1.A): expand `x = ∑ i∈I, c i • b i` (orthonormal repr),
two Parseval computations give `‖x‖² = ∑ ‖c i‖²` and
`re ⟪T x, x⟫ = ∑ μ i ‖c i‖²`; so `R x` is a convex combination of the `μ i`
(nonneg weights summing to 1, denominator `> 0` since `x ≠ 0`), which lies
between the min and max of its support.

**Decomposition status.** The closing convex-combination step is discharged by
`weighted_mean_mem_inf_sup` above (proven, `sorry`-free). The *assembly* of
`rayleigh_bounds_on_eigenspan` from the Parseval data is now also discharged
`sorry`-free below: with weights `w i := ‖b.repr x i‖²` the proof
  1. derives the positive-mass hypothesis `0 < ∑ i ∈ I, w i` from `‖x‖ > 0` and
     the norm-Parseval identity (so it is *not* an independent obligation), and
  2. rewrites the Rayleigh quotient by the two Parseval identities and closes with
     `weighted_mean_mem_inf_sup`.
What remain are exactly the two HARD-not-OPEN Parseval leaf identities, isolated
as the named lemmas `norm_sq_eq_sum_repr_sq` and `re_inner_apply_eq_sum_repr_mul`
just above — each a standard orthonormal-basis computation and an ideal Aristotle
/ build target. They share the single nontrivial fact that `b.repr x` is supported
on `I` (because `x ∈ span (b '' I)`), so proving that support lemma first
discharges both. -/

/-- **Support of the coordinates.** When `x ∈ span (b '' I)` the orthonormal
coordinates `b.repr x i = ⟪b i, x⟫` vanish for every index `i ∉ I`. Proved by
`span` induction: generators `b j` (`j ∈ I`) are orthogonal to `b i` since
`i ≠ j`, and the predicate `⟪b i, ·⟫ = 0` is closed under `+` and `•`. This is
the single fact both Parseval identities below reduce to. -/
theorem repr_eq_zero_of_not_mem
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E)
    (I : Finset (Fin n))
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n)))) :
    ∀ i, i ∉ I → b.repr x i = 0 := by
  intro i hiI
  rw [b.repr_apply_apply]
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := by
        rintro rfl; exact hiI (Finset.mem_coe.mp hj)
      have h := (orthonormal_iff_ite.mp b.orthonormal) i j
      rw [if_neg hij] at h
      exact h
  | zero => simp
  | add y z _ _ hyih hzih => rw [inner_add_right, hyih, hzih, add_zero]
  | smul a y _ hyih => rw [inner_smul_right, hyih, mul_zero]

/-- **Parseval for the norm, restricted to the support `I`.** Since
`x ∈ span (b '' I)` the coordinates `b.repr x i` vanish off `I`, so the full
Parseval identity `‖x‖² = ∑_i ‖b.repr x i‖²` collapses to a sum over `I`.

Mathlib map: full Parseval is `b.repr.norm_map` (the `repr` is a
`LinearIsometryEquiv` to `EuclideanSpace`) combined with `EuclideanSpace.norm_eq`
and `Real.sq_sqrt`; the restriction to `I` is `Finset.sum_subset` with the
off-support vanishing `repr_eq_zero_of_not_mem`. -/
theorem norm_sq_eq_sum_repr_sq
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 E)
    (I : Finset (Fin n))
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n)))) :
    ‖x‖ ^ 2 = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 := by
  have hsupp := repr_eq_zero_of_not_mem b I x hx
  have h_full : ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [h_full]
  exact (Finset.sum_subset (Finset.subset_univ I)
    (fun i _ hi => by rw [hsupp i hi]; simp)).symm

/-- **Diagonalisation + Parseval for the quadratic form.** When `b` diagonalises
`T` with real eigenvalues `μ`, the quadratic form is the eigenvalue-weighted
Parseval sum; restricted to the support `I` of `x ∈ span (b '' I)`.

Mathlib map: expand `x = ∑ i, b.repr x i • b i` (`OrthonormalBasis.sum_repr`),
push `T` through (`hb`: `T (b i) = μ i • b i`), then Parseval the inner product
`⟪T x, x⟫ = ∑ i, μ i * ‖b.repr x i‖²`; `RCLike.re` of a real-weighted sum of
`‖·‖²` is the real sum, and `Finset.sum_subset` restricts to `I`. -/
theorem repr_apply_of_diag
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i) (x : E) :
    ∀ i, b.repr (T x) i = b.repr x i * (μ i : 𝕜) := by
  intro i
  have hTx : T x = ∑ j, b.repr x j • ((μ j : 𝕜) • b j) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, hb j]
  rw [b.repr_apply_apply, hTx, inner_sum]
  rw [Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_smul_right,
        (orthonormal_iff_ite.mp b.orthonormal) i i, if_pos rfl, mul_one]
  · intro j _ hji
    rw [inner_smul_right, inner_smul_right,
        (orthonormal_iff_ite.mp b.orthonormal) i j, if_neg (fun h => hji h.symm),
        mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem re_inner_apply_eq_sum_repr_mul
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (I : Finset (Fin n))
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n)))) :
    RCLike.re (@inner 𝕜 E _ (T x) x) = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 * μ i := by
  have hsupp := repr_eq_zero_of_not_mem b I x hx
  have hrepr := repr_apply_of_diag T b μ hb x
  have hinner : (@inner 𝕜 E _ (T x) x)
      = ∑ i, (μ i : 𝕜) * ((‖b.repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← b.repr.inner_map_map (T x) x, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [RCLike.inner_apply, hrepr i, map_mul, RCLike.conj_ofReal, ← mul_assoc,
        RCLike.mul_conj]
    push_cast
    ring
  rw [hinner, map_sum]
  rw [← Finset.sum_subset (Finset.subset_univ I)
        (fun i _ hi => by rw [hsupp i hi]; simp)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.re_ofReal_mul]
  simp [mul_comm]

theorem rayleigh_bounds_on_eigenspan
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →ₗ[𝕜] E) (b : OrthonormalBasis (Fin n) 𝕜 E) (μ : Fin n → ℝ)
    (hb : ∀ i, T (b i) = (μ i : 𝕜) • b i)
    (I : Finset (Fin n)) (hI : I.Nonempty)
    (x : E) (hx : x ∈ Submodule.span 𝕜 ((b : Fin n → E) '' (↑I : Set (Fin n))))
    (hx0 : x ≠ 0) :
    I.inf' hI μ ≤ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2
      ∧ RCLike.re (@inner 𝕜 E _ (T x) x) / ‖x‖ ^ 2 ≤ I.sup' hI μ := by
  -- Parseval weights `w i = ‖b.repr x i‖²`, nonnegative termwise.
  have hwnonneg : ∀ i ∈ I, 0 ≤ ‖b.repr x i‖ ^ 2 := fun i _ => sq_nonneg _
  -- The two Parseval identities (the only remaining leaf obligations).
  have h1 : ‖x‖ ^ 2 = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 := norm_sq_eq_sum_repr_sq b I x hx
  have h2 : RCLike.re (@inner 𝕜 E _ (T x) x) = ∑ i ∈ I, ‖b.repr x i‖ ^ 2 * μ i :=
    re_inner_apply_eq_sum_repr_mul T b μ hb I x hx
  -- Positive total mass: derived from `x ≠ 0` via the norm-Parseval identity,
  -- so it is *not* an independent obligation.
  have h3 : 0 < ∑ i ∈ I, ‖b.repr x i‖ ^ 2 := by
    rw [← h1]
    exact pow_pos (norm_pos_iff.mpr hx0) 2
  -- Rewrite the Rayleigh quotient as a weighted mean and apply the convex core.
  rw [h1, h2]
  exact weighted_mean_mem_inf_sup μ I hI (fun i => ‖b.repr x i‖ ^ 2) hwnonneg h3

end CauchyInterlacing.Sublemmas
