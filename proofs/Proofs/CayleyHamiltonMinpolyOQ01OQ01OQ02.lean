/-
  Jordan block counts from the generalized-eigenspace dimension tower
  Open Question (cayley-hamilton-minpoly-oq-01-oq-01-oq-02)

  Parent chain
    cayley-hamilton-minpoly-oq-01        Jordan Canonical Form and the minimal polynomial
    cayley-hamilton-minpoly-oq-01-oq-01  minpoly K f = ∏_{μ} (X - μ)^{e_μ}  (proved, 0 axioms)

  The parent (`CayleyHamiltonMinpolyOQ01OQ01.lean`) proved the full JCF–minpoly
  product identity WITHOUT ever building an explicit Jordan basis, working purely
  through Mathlib's generalized-eigenspace theory.  The natural follow-up open
  question is:

      How are the *Jordan block counts per size* recovered from the
      generalized-eigenspace dimension tower

          d_k(μ) := dim ker ((f - μ)^k),   k = 0, 1, 2, …

      again *without* constructing a Jordan basis (which Mathlib 4.26.0 lacks)?

  Classical linear algebra answers this: for an operator with a single eigenvalue
  (or, per eigenvalue μ, working with the restriction), if `a_j` is the number of
  Jordan blocks of size ≥ j then

          a_j = d_j - d_{j-1},        (blocks of size ≥ j)
          #{blocks of size exactly j} = a_j - a_{j+1} = 2 d_j - d_{j-1} - d_{j+1}.

  For these to be genuine (non-negative!) counts one needs the dimension tower to
  be **concave**: `d_{k+2} + d_k ≤ 2 d_{k+1}`.  This concavity is the mathematical
  heart of the problem, and it is provable with no Jordan basis at all.

  This file:

    * `nullity N k`               the tower `dim ker (N^k)` for a general
                                  endomorphism `N` (take `N = f - μ` for eigenvalues).
    * `ker_pow_mono`              the kernels form an increasing chain.
    * `jordanImage N k`           the submodule `N^k (ker N^{k+1}) ⊆ ker N`, whose
                                  dimension is exactly `a_{k+1}` (blocks of size ≥ k+1).
    * `nullity_succ`              rank–nullity across one level:
                                  `d_{k+1} = dim (jordanImage N k) + d_k`.
    * `jordanImage_antitone`      `N` maps `jordanImage N (k+1)` into `jordanImage N k`,
                                  hence the block-count sequence is non-increasing.
    * `nullity_concave`           `d_{k+2} + d_k ≤ 2 d_{k+1}`  — the concavity theorem.
    * `blocksAtLeast`, `blocksExact`   the block-count functions read off the tower,
                                  with `blocksAtLeast_succ`, `blocksAtLeast_antitone`,
                                  `sum_blocksAtLeast` (telescoping to `d_m`),
                                  `blocksAtLeast_one` (total block count = geometric
                                  multiplicity), and `blocksExact_succ_tower`
                                  (`#{size = k+1} = 2 d_{k+1} - d_k - d_{k+2}`).
    * eigenvalue interface        `nullity_sub_eq_finrank_genEigenspace`,
                                  `eigenvalue_blocksAtLeast`, `eigenvalue_blocks_total`
                                  translating everything into `genEigenspace f μ`.

  The concavity proof is the clean, Jordan-basis-free argument:
  `N` induces an injection `ker N^{k+2}/ker N^{k+1} ↪ ker N^{k+1}/ker N^k`; here it
  is repackaged as `jordanImage N (k+1) ≤ jordanImage N k`, whose dimensions are the
  successive differences `d_{k+2}-d_{k+1}` and `d_{k+1}-d_k` via `nullity_succ`.

  Status: 0 sorries, 0 axioms (only `propext`, `Classical.choice`, `Quot.sound`).

  References:
  - Axler, "Linear Algebra Done Right", Ch. 8 (generalized eigenspaces, nilpotents)
  - Horn & Johnson, "Matrix Analysis", §3.1 (Weyr characteristic / Jordan structure)
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module

namespace CayleyHamiltonMinpolyOQ01OQ01OQ02

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-! ### The nullity tower of an endomorphism -/

/-- The **nullity tower** of an endomorphism `N`: `nullity N k = dim ker (N^k)`.
    Taking `N = f - μ • 1` recovers the generalized-eigenspace dimension tower
    `d_k(μ) = dim (genEigenspace f μ k)` (see `nullity_sub_eq_finrank_genEigenspace`). -/
noncomputable def nullity (N : Module.End K V) (k : ℕ) : ℕ :=
  finrank K (LinearMap.ker (N ^ k))

omit [FiniteDimensional K V] in
/-- The kernels of the powers of `N` form an increasing chain. -/
theorem ker_pow_mono (N : Module.End K V) {a b : ℕ} (h : a ≤ b) :
    LinearMap.ker (N ^ a) ≤ LinearMap.ker (N ^ b) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm a c, pow_add, Module.End.mul_apply, hx, map_zero]

/-- The tower is monotone: `d_a ≤ d_b` whenever `a ≤ b`. -/
theorem nullity_mono (N : Module.End K V) {a b : ℕ} (h : a ≤ b) :
    nullity N a ≤ nullity N b :=
  Submodule.finrank_mono (ker_pow_mono N h)

omit [FiniteDimensional K V] in
@[simp] theorem nullity_zero (N : Module.End K V) : nullity N 0 = 0 := by
  have hbot : LinearMap.ker (N ^ 0) = ⊥ := by
    rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
  show finrank K (LinearMap.ker (N ^ 0)) = 0
  rw [hbot, finrank_bot]

/-! ### The block-count submodule and rank–nullity across one level -/

/-- The image submodule `N^k (ker N^{k+1}) ⊆ ker N`.  Its dimension is the number
    of Jordan blocks of size ≥ `k+1` (for the eigenvalue implicit in `N`). -/
noncomputable def jordanImage (N : Module.End K V) (k : ℕ) : Submodule K V :=
  (LinearMap.ker (N ^ (k + 1))).map (N ^ k)

/-- **Rank–nullity across one level of the tower.**
    `dim ker (N^{k+1}) = dim (jordanImage N k) + dim ker (N^k)`, i.e. the successive
    difference `d_{k+1} - d_k` equals the number of blocks of size ≥ `k+1`.

    Proof: restrict `N^k` to `ker N^{k+1}`.  Its range is `jordanImage N k`, and its
    kernel is `ker N^{k+1} ⊓ ker N^k = ker N^k` (the tower is increasing).  Apply
    rank–nullity on the finite-dimensional space `ker N^{k+1}`. -/
theorem nullity_succ (N : Module.End K V) (k : ℕ) :
    nullity N (k + 1) = finrank K (jordanImage N k) + nullity N k := by
  -- the kernel of the restricted map `N^k : ker N^{k+1} → V` has the nullity of level `k`
  have hkerfin :
      finrank K (LinearMap.ker ((N ^ k).domRestrict (LinearMap.ker (N ^ (k + 1)))))
        = finrank K (LinearMap.ker (N ^ k)) := by
    have hcomp : (N ^ k).domRestrict (LinearMap.ker (N ^ (k + 1)))
        = (N ^ k).comp (LinearMap.ker (N ^ (k + 1))).subtype := rfl
    rw [hcomp, LinearMap.ker_comp,
      ← Submodule.finrank_map_subtype_eq (LinearMap.ker (N ^ (k + 1))),
      Submodule.map_comap_subtype,
      inf_of_le_right (ker_pow_mono N (Nat.le_succ k))]
  -- rank–nullity for the restricted map `N^k : ↥(ker N^{k+1}) → V`
  have hkey := LinearMap.finrank_range_add_finrank_ker
      ((N ^ k).domRestrict (LinearMap.ker (N ^ (k + 1))))
  rw [LinearMap.range_domRestrict, hkerfin] at hkey
  unfold nullity jordanImage
  omega

/-! ### Concavity of the tower -/

omit [FiniteDimensional K V] in
/-- `N` maps `jordanImage N (k+1)` into `jordanImage N k`: the block-count
    submodules are antitone.  This is the heart of the concavity proof. -/
theorem jordanImage_antitone (N : Module.End K V) (k : ℕ) :
    jordanImage N (k + 1) ≤ jordanImage N k := by
  intro y hy
  simp only [jordanImage, Submodule.mem_map, LinearMap.mem_ker] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨N x, ?_, ?_⟩
  · -- `N^{k+1} (N x) = N^{k+2} x = 0`
    have h2 : (N ^ (k + 1)) (N x) = (N ^ (k + 1 + 1)) x := by
      rw [← Module.End.mul_apply, ← pow_succ]
    rw [h2]; exact hx
  · -- `N^k (N x) = N^{k+1} x`
    rw [← Module.End.mul_apply, ← pow_succ]

/-- **Concavity of the nullity tower.**  `d_{k+2} + d_k ≤ 2 d_{k+1}`.

    Equivalently the successive differences `d_{k+1} - d_k` are non-increasing, which
    is exactly the statement that the Jordan block counts of each size are
    well-defined non-negative integers. -/
theorem nullity_concave (N : Module.End K V) (k : ℕ) :
    nullity N (k + 2) + nullity N k ≤ 2 * nullity N (k + 1) := by
  have h1 := nullity_succ N k
  have h2 : nullity N (k + 2)
      = finrank K (jordanImage N (k + 1)) + nullity N (k + 1) := nullity_succ N (k + 1)
  have h3 : finrank K (jordanImage N (k + 1)) ≤ finrank K (jordanImage N k) :=
    Submodule.finrank_mono (jordanImage_antitone N k)
  omega

/-! ### Block-count functions read off the tower -/

/-- Number of Jordan blocks of size ≥ `j` (for the eigenvalue implicit in `N`),
    read off the tower as `d_j - d_{j-1}` (the Weyr characteristic). -/
noncomputable def blocksAtLeast (N : Module.End K V) (j : ℕ) : ℕ :=
  nullity N j - nullity N (j - 1)

/-- Number of Jordan blocks of size **exactly** `j`, read off as
    `blocksAtLeast N j - blocksAtLeast N (j+1) = 2 d_j - d_{j-1} - d_{j+1}`. -/
noncomputable def blocksExact (N : Module.End K V) (j : ℕ) : ℕ :=
  blocksAtLeast N j - blocksAtLeast N (j + 1)

/-- The count of blocks of size ≥ `k+1` equals `dim (jordanImage N k)`. -/
theorem blocksAtLeast_succ (N : Module.End K V) (k : ℕ) :
    blocksAtLeast N (k + 1) = finrank K (jordanImage N k) := by
  have h := nullity_succ N k
  simp only [blocksAtLeast, Nat.add_sub_cancel]
  omega

/-- The block-count sequence is non-increasing in the size threshold. -/
theorem blocksAtLeast_antitone (N : Module.End K V) (k : ℕ) :
    blocksAtLeast N (k + 2) ≤ blocksAtLeast N (k + 1) := by
  rw [blocksAtLeast_succ, blocksAtLeast_succ]
  exact Submodule.finrank_mono (jordanImage_antitone N k)

/-- **Telescoping identity.**  Summing the "blocks of size ≥ j" counts over
    `j = 1, …, m` recovers the level-`m` dimension `d_m`.  (Equivalently
    `∑_j j · #{size = j}` up to `m` reconstructs the algebraic multiplicity.) -/
theorem sum_blocksAtLeast (N : Module.End K V) (m : ℕ) :
    ∑ j ∈ Finset.range m, blocksAtLeast N (j + 1) = nullity N m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, blocksAtLeast_succ]
    have h := nullity_succ N n
    omega

omit [FiniteDimensional K V] in
/-- The total number of Jordan blocks (for the eigenvalue implicit in `N`) equals the
    geometric multiplicity `dim ker N` — recovered as "blocks of size ≥ 1". -/
theorem blocksAtLeast_one (N : Module.End K V) :
    blocksAtLeast N 1 = finrank K (LinearMap.ker N) := by
  show nullity N 1 - nullity N (1 - 1) = finrank K (LinearMap.ker N)
  rw [show (1 : ℕ) - 1 = 0 from rfl, nullity_zero, Nat.sub_zero]
  show finrank K (LinearMap.ker (N ^ 1)) = finrank K (LinearMap.ker N)
  rw [pow_one]

/-- Blocks of exact size `k+1` as a genuine (non-truncated) difference of the
    "size ≥" counts: `#{size = k+1} + dim(jordanImage N (k+1)) = dim(jordanImage N k)`. -/
theorem blocksExact_succ_add (N : Module.End K V) (k : ℕ) :
    blocksExact N (k + 1) + finrank K (jordanImage N (k + 1))
      = finrank K (jordanImage N k) := by
  simp only [blocksExact, blocksAtLeast_succ]
  have h := Submodule.finrank_mono (jordanImage_antitone N k)
  omega

/-- Blocks of exact size `k+1` in tower coordinates:
    `#{size = k+1} = 2 d_{k+1} - d_k - d_{k+2}` (stated additively to avoid
    truncated subtraction). -/
theorem blocksExact_succ_tower (N : Module.End K V) (k : ℕ) :
    blocksExact N (k + 1) + nullity N k + nullity N (k + 2)
      = 2 * nullity N (k + 1) := by
  have e := blocksExact_succ_add N k
  have h1 := nullity_succ N k
  have h2 : nullity N (k + 2)
      = finrank K (jordanImage N (k + 1)) + nullity N (k + 1) := nullity_succ N (k + 1)
  omega

/-! ### Eigenvalue interface (the generalized-eigenspace dimension tower) -/

section Eigenvalues

variable (f : Module.End K V) (μ : K)

omit [FiniteDimensional K V] in
/-- The nullity tower of `f - μ • 1` **is** the generalized-eigenspace dimension
    tower: `nullity (f - μ•1) k = dim (genEigenspace f μ k) = d_k(μ)`. -/
theorem nullity_sub_eq_finrank_genEigenspace (k : ℕ) :
    nullity (f - μ • 1) k = finrank K (f.genEigenspace μ (k : ℕ∞)) := by
  unfold nullity
  rw [(Module.End.genEigenspace_nat : f.genEigenspace μ (k : ℕ∞) = _)]

omit [FiniteDimensional K V] in
/-- Blocks of size ≥ `k+1` for eigenvalue `μ`, in dimension-tower coordinates. -/
theorem eigenvalue_blocksAtLeast (k : ℕ) :
    blocksAtLeast (f - μ • 1) (k + 1)
      = finrank K (f.genEigenspace μ ((k + 1 : ℕ) : ℕ∞))
        - finrank K (f.genEigenspace μ (k : ℕ∞)) := by
  simp only [blocksAtLeast, Nat.add_sub_cancel]
  rw [nullity_sub_eq_finrank_genEigenspace, nullity_sub_eq_finrank_genEigenspace]

omit [FiniteDimensional K V] in
/-- Total number of Jordan blocks at eigenvalue `μ` equals the geometric
    multiplicity `dim (genEigenspace f μ 1) = dim (eigenspace f μ)`. -/
theorem eigenvalue_blocks_total :
    blocksAtLeast (f - μ • 1) 1 = finrank K (f.genEigenspace μ (1 : ℕ∞)) := by
  have h1 : nullity (f - μ • 1) 1 = finrank K (f.genEigenspace μ (1 : ℕ∞)) := by
    have h := nullity_sub_eq_finrank_genEigenspace f μ 1
    rwa [Nat.cast_one] at h
  simp only [blocksAtLeast, show (1 : ℕ) - 1 = 0 from rfl, nullity_zero, Nat.sub_zero]
  exact h1

/-- Concavity of the generalized-eigenspace dimension tower for eigenvalue `μ`:
    `d_{k+2}(μ) + d_k(μ) ≤ 2 d_{k+1}(μ)`. -/
theorem genEigenspace_finrank_concave (k : ℕ) :
    finrank K (f.genEigenspace μ ((k + 2 : ℕ) : ℕ∞)) + finrank K (f.genEigenspace μ (k : ℕ∞))
      ≤ 2 * finrank K (f.genEigenspace μ ((k + 1 : ℕ) : ℕ∞)) := by
  have h := nullity_concave (f - μ • 1) k
  rw [nullity_sub_eq_finrank_genEigenspace, nullity_sub_eq_finrank_genEigenspace,
    nullity_sub_eq_finrank_genEigenspace] at h
  exact h

end Eigenvalues

end CayleyHamiltonMinpolyOQ01OQ01OQ02
