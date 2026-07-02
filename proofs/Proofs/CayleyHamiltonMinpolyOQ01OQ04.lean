/-
  Cayley–Hamilton / Minimal Polynomial, Open Question 01 → OQ 04:
  The rank–nullity tower (Weyr characteristic) is non-increasing.

  For a linear operator `f` on a finite-dimensional space and an eigenvalue `μ`,
  write `aₖ = dim (genEigenspace μ k) = dim ker (f - μ)ᵏ`. The *k-th Weyr number*
  is the jump

      wₖ = a_{k+1} − aₖ                                        (§ `weyr`)

  which counts the Jordan blocks for `μ` of size `≥ k+1`. The theorem proved here
  is that this sequence is **non-increasing** (`weyr_antitone`):

      w_{k+1} ≤ wₖ,   equivalently   aₖ + a_{k+2} ≤ 2·a_{k+1}   (§ `..._concave`),

  i.e. the dimensions `aₖ` form a *concave* sequence. This is the abstract fact
  underlying the shape of the Jordan/Weyr "dot diagram".

  **Proof idea (quotient-free).** Set `N = f - μ`. For each `k` consider the
  subspace

      Uₖ = N^k (ker N^{k+1})  ⊆  ker N.

  Restricting `N^k` to `ker N^{k+1}` has kernel `ker N^k` (which sits inside
  `ker N^{k+1}`) and range `Uₖ`, so rank–nullity gives

      dim Uₖ = a_{k+1} − aₖ   (`finrank_diff_space`).

  A one-line calculation shows `U_{k+1} ⊆ Uₖ` (`diff_space_antitone`): if
  `y = N^{k+1} x` with `x ∈ ker N^{k+2}`, then `y = N^k (N x)` with
  `N x ∈ ker N^{k+1}`. Monotonicity of `finrank` then yields
  `a_{k+2} − a_{k+1} ≤ a_{k+1} − aₖ`, which is the claim.

  No axioms; fully machine-checked against Mathlib.

  Parent: cayley-hamilton-minpoly-oq-01 (Jordan form and the minimal polynomial).
  Reference: standard Jordan/Weyr theory (see e.g. Horn–Johnson, *Matrix Analysis*).
-/

import Mathlib

open Module LinearMap
open scoped Classical

set_option linter.unusedSectionVars false

namespace CayleyHamiltonMinpolyOQ01OQ04

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Applying `Nᵏ⁺¹` is applying `Nᵏ` after one more `N`. -/
lemma pow_succ_apply (N : Module.End K V) (j : ℕ) (x : V) :
    (N ^ (j + 1)) x = (N ^ j) (N x) := by rw [pow_succ]; rfl

/-- Kernels of successive powers grow: `ker Nᵏ ≤ ker Nᵏ⁺¹`. -/
lemma ker_pow_le_succ (N : Module.End K V) (k : ℕ) :
    LinearMap.ker (N ^ k) ≤ LinearMap.ker (N ^ (k + 1)) := by
  intro x hx
  simp only [LinearMap.mem_ker] at hx ⊢
  have h : (N ^ (k + 1)) x = N ((N ^ k) x) := by rw [pow_succ']; rfl
  rw [h, hx, map_zero]

/-- **Rank–nullity for the tower.** `dim (Nᵏ (ker Nᵏ⁺¹)) + dim (ker Nᵏ) = dim (ker Nᵏ⁺¹)`.
    The left summand is the "difference space" whose dimension is the jump
    `a_{k+1} − aₖ`. -/
lemma finrank_diff_space (N : Module.End K V) (k : ℕ) :
    finrank K (Submodule.map (N ^ k) (LinearMap.ker (N ^ (k + 1))))
        + finrank K (LinearMap.ker (N ^ k))
      = finrank K (LinearMap.ker (N ^ (k + 1))) := by
  have key := LinearMap.finrank_range_add_finrank_ker
      ((N ^ k).comp (LinearMap.ker (N ^ (k + 1))).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
      (Submodule.comapSubtypeEquivOfLe (ker_pow_le_succ N k)).finrank_eq] at key
  exact key

/-- **The difference spaces shrink:** `N^{k+1}(ker N^{k+2}) ⊆ Nᵏ(ker Nᵏ⁺¹)`. -/
lemma diff_space_antitone (N : Module.End K V) (k : ℕ) :
    Submodule.map (N ^ (k + 1)) (LinearMap.ker (N ^ (k + 2)))
      ≤ Submodule.map (N ^ k) (LinearMap.ker (N ^ (k + 1))) := by
  intro y hy
  rw [Submodule.mem_map] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  rw [LinearMap.mem_ker] at hx
  refine ⟨N x, ?_, ?_⟩
  · rw [LinearMap.mem_ker, ← pow_succ_apply N (k + 1) x]
    exact hx
  · exact (pow_succ_apply N k x).symm

/-- **Concavity of the kernel dimensions:** `aₖ + a_{k+2} ≤ 2·a_{k+1}` where
    `aₖ = dim ker Nᵏ`. -/
theorem finrank_ker_pow_concave (N : Module.End K V) (k : ℕ) :
    finrank K (LinearMap.ker (N ^ k)) + finrank K (LinearMap.ker (N ^ (k + 2)))
      ≤ 2 * finrank K (LinearMap.ker (N ^ (k + 1))) := by
  have h1 := finrank_diff_space N k
  have h2 := finrank_diff_space N (k + 1)
  rw [show k + 1 + 1 = k + 2 from rfl] at h2
  have h3 := Submodule.finrank_mono (diff_space_antitone N k)
  omega

/-- Concavity restated for generalized eigenspaces:
    `dim (genEigenspace μ k) + dim (genEigenspace μ (k+2)) ≤ 2·dim (genEigenspace μ (k+1))`. -/
theorem genEigenspace_finrank_concave (f : Module.End K V) (μ : K) (k : ℕ) :
    finrank K (f.genEigenspace μ (k : ℕ)) + finrank K (f.genEigenspace μ (k + 2 : ℕ))
      ≤ 2 * finrank K (f.genEigenspace μ (k + 1 : ℕ)) := by
  rw [Module.End.genEigenspace_nat, Module.End.genEigenspace_nat, Module.End.genEigenspace_nat]
  exact finrank_ker_pow_concave (f - μ • 1) k

/-- The `k`-th **Weyr number**: `dim (genEigenspace μ (k+1)) − dim (genEigenspace μ k)`,
    the number of Jordan blocks for `μ` of size `≥ k+1`. -/
noncomputable def weyr (f : Module.End K V) (μ : K) (k : ℕ) : ℕ :=
  finrank K (f.genEigenspace μ (k + 1 : ℕ)) - finrank K (f.genEigenspace μ (k : ℕ))

/-- **Main result: the Weyr characteristic is non-increasing.** The sequence of
    generalized-eigenspace dimension jumps `w₀ ≥ w₁ ≥ w₂ ≥ ⋯` decreases, i.e. the
    number of Jordan blocks of size `≥ k+1` does not exceed the number of size
    `≥ k`. -/
theorem weyr_antitone (f : Module.End K V) (μ : K) (k : ℕ) :
    weyr f μ (k + 1) ≤ weyr f μ k := by
  unfold weyr
  rw [show k + 1 + 1 = k + 2 from rfl]
  have hconv := genEigenspace_finrank_concave f μ k
  have hmono1 :
      finrank K (f.genEigenspace μ (k : ℕ)) ≤ finrank K (f.genEigenspace μ (k + 1 : ℕ)) := by
    rw [Module.End.genEigenspace_nat, Module.End.genEigenspace_nat]
    exact Submodule.finrank_mono (ker_pow_le_succ (f - μ • 1) k)
  have hmono2 :
      finrank K (f.genEigenspace μ (k + 1 : ℕ)) ≤ finrank K (f.genEigenspace μ (k + 2 : ℕ)) := by
    rw [Module.End.genEigenspace_nat, Module.End.genEigenspace_nat]
    exact Submodule.finrank_mono (ker_pow_le_succ (f - μ • 1) (k + 1))
  omega

end CayleyHamiltonMinpolyOQ01OQ04
