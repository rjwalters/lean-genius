import Mathlib

/-
# Cauchy interlacing — keystone leaf lemmas (Sublemma A & B), typed targets

These are the two *standalone* leaf lemmas that the Courant–Fischer max–min
keystone (the single Mathlib gap blocking Cauchy interlacing) reduces to. See
`approaches/keystone-minmax-proof-design.md` for the full mathematical proof and
the per-step Mathlib lemma map. That design recommends building / submitting
these two first because they are *closed* (known-mathematics, HARD-not-OPEN) and
have no upstream dependencies.

This file turns that prose design into **typed Lean statements** so they are
directly submittable to Aristotle / buildable the moment a backend frees.
Sublemma B carries a **full candidate proof** (Grassmann dimension count).
Sublemma A is further decomposed: its convex-combination core is split off as
`weighted_mean_mem_inf_sup` (a standalone, inner-product-free lemma with a
**full candidate proof**), leaving only the two Parseval identities as the
remaining `sorry` targets inside `rayleigh_bounds_on_eigenspan`.

## Status

BUILD-PENDING (candidate proof for B, sorry for A). Authored / extended while both
backends were down (Aristotle MCP → `Resource not found`; Docker VM saturated at 3
concurrent `lean-build` containers on the 7.65 GiB VM, above the safe ≤2
threshold), so the proof below is **not yet machine-checked**.

Sublemma B is pure finite-dimensional linear algebra: the four lemmas it uses
(`Submodule.finrank_sup_add_finrank_inf_eq`, `Submodule.finrank_le`,
`finrank_bot` via `simp`, `Submodule.ne_bot_iff`) are all standard Mathlib API
and the `omega` arithmetic is routine, so confidence is high — but it must still
be compiled to confirm. Sublemma A carries an inner-product/eigenbasis hypothesis
and its exact spelling (`inner` field annotation, `Finset → Set` image coercion)
should be re-confirmed at first compile. Not registered in `Proofs.lean`.
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

**Decomposition status.** The closing convex-combination step is now discharged by
`weighted_mean_mem_inf_sup` above (proven, `sorry`-free). What remains for a full
proof of `rayleigh_bounds_on_eigenspan` are the two Parseval identities with
`w i := ‖b.repr x i‖²` (support contained in `I` since `x ∈ span (b '' I)`):
  * `‖x‖ ^ 2 = ∑ i ∈ I, w i`  (Parseval for the norm), and
  * `RCLike.re ⟪T x, x⟫ = ∑ i ∈ I, w i * μ i`  (diagonalisation + Parseval),
plus `0 < ∑ i ∈ I, w i` from `x ≠ 0`. These three are the remaining HARD-not-OPEN
targets (Aristotle / build), each a standard orthonormal-basis computation. -/
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
  sorry

end CauchyInterlacing.Sublemmas
