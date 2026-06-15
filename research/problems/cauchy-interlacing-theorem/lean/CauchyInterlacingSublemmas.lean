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
Sublemma B now carries a **full candidate proof** (Grassmann dimension count);
Sublemma A remains `sorry`.

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

/-! ## Sublemma A — Rayleigh bounds on a coordinate eigenspan

If `T` is diagonalised by the orthonormal family `b` with real eigenvalues `μ`,
then for any nonzero `x` in the span of the sub-family `b '' I` the Rayleigh
quotient `R x = re ⟪T x, x⟫ / ‖x‖²` is a convex combination of `{μ i : i ∈ I}`,
hence sandwiched between `min_{i∈I} μ i` and `max_{i∈I} μ i`.

Proof route (design §1.A): expand `x = ∑ i∈I, c i • b i` (orthonormal repr),
two Parseval computations give `‖x‖² = ∑ ‖c i‖²` and
`re ⟪T x, x⟫ = ∑ μ i ‖c i‖²`; so `R x` is a convex combination of the `μ i`
(nonneg weights summing to 1, denominator `> 0` since `x ≠ 0`), which lies
between the min and max of its support. -/
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
