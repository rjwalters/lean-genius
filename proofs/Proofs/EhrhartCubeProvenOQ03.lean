/-
  Ehrhart Polynomial of the Hypersimplex: First-Principles Scaffold
  (ehrhart-cube-proven-oq-03 — S1 OBSERVE)

  This file is a fresh scaffold introducing the **hypersimplex** Δ(d, k),
  the slice of the unit d-cube [0, 1]^d by the affine hyperplane
  Σ x_i = k. Lattice points in n · Δ(d, k) correspond to functions
  x : Fin d → Fin (n + 1) with Σ x_i = n · k.

  This S1 OBSERVE provides:
  1. The lattice-point counting definition `hypersimplexLatticeCount`
     via a `Finset.filter` predicate on `Fin d → Fin (n + 1)`.
  2. Two reference identities stated as `sorry` for S2/S3:
     - `hypersimplex_count_k_one`:
         hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1)
     - `hypersimplex_palindrome_k_d_minus_1`:
         hypersimplexLatticeCount d (d - 1) n
           = hypersimplexLatticeCount d 1 n
  3. Three numeric sanity checks closed by `decide` to anchor the
     definition (no `sorry` in these).

  Sibling files in the `ehrhart-cube-proven` family:
  - `EhrhartCubeProven.lean`    — |[0,1]^d ∩ (1/n)ℤ^d| = (n+1)^d (verified)
  - `EhrhartSimplexProven.lean` — OQ-01 standard simplex (verified)
  - `EhrhartCrossPolytope.lean` — OQ-02 cross-polytope (verified)
  - `EhrhartCubeProvenOQ04.lean` — Eulerian h*-vector + Worpitzky (formalized)

  Status: S1 SCAFFOLD. Sorries: 2 (both theorems above).
-/
import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace EhrhartCubeProvenOQ03

/-! ## Section I — Hypersimplex Lattice-Point Definition

The d-dimensional hypersimplex Δ(d, k) is the convex hull of all 0/1-vectors
in ℤ^d with exactly k coordinates equal to 1. Equivalently it is the slice
of the unit cube [0, 1]^d by the affine hyperplane Σ x_i = k.

Lattice points of `n · Δ(d, k)` are integer points x ∈ [0, n]^d with
Σ x_i = n · k. We encode them as elements of `Fin d → Fin (n + 1)`
filtered by the coordinate-sum predicate. -/

/-- Coordinate-sum predicate on `Fin d → Fin (n + 1)`. -/
def coordSumEq (d n target : ℕ) (x : Fin d → Fin (n + 1)) : Prop :=
  (∑ i : Fin d, (x i : ℕ)) = target

instance (d n target : ℕ) (x : Fin d → Fin (n + 1)) :
    Decidable (coordSumEq d n target x) := by
  unfold coordSumEq
  infer_instance

/-- Lattice-point count of `n · Δ(d, k)` as a `Finset.filter` cardinality.

    The points are functions `Fin d → Fin (n + 1)` whose coordinate sum is
    exactly `n · k`. -/
def hypersimplexLatticeCount (d k n : ℕ) : ℕ :=
  (Finset.univ.filter
      (fun x : Fin d → Fin (n + 1) => (∑ i : Fin d, (x i : ℕ)) = n * k)).card

/-! ## Section II — Reference identities (S2 / S3 targets, `sorry`) -/

/-- **S2 target**: When k = 1, the hypersimplex `Δ(d, 1)` reduces to a
    standard (d - 1)-simplex. Concretely:

      hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1).

    Proof sketch: Lattice points are weak compositions of `n` into `d` parts.
    Setting `y_i = x_i` for i < d - 1 and absorbing the slack into the last
    coordinate yields a bijection with `Sym (Fin d) n`; conclude with
    `Sym.card_sym_eq_choose` (cf. `EhrhartSimplexProven.simplex_lattice_count`). -/
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  sorry

/-- **S3 target**: The lattice-isomorphism `x ↦ (n - x i)` sends `Δ(d, k)`
    bijectively to `Δ(d, d - k)`. Specialising at `k = 1`:

      hypersimplexLatticeCount d (d - 1) n = hypersimplexLatticeCount d 1 n.

    Proof: define the involution `φ x i = ⟨n - x i, _⟩`. The sum-of-complements
    identity `∑ φ x_i + ∑ x_i = d * n` (from `Finset.sum_add_distrib` and
    `n - x_i + x_i = n` pointwise) lets us swap the filter predicates, so the
    `(Fin d → Fin (n+1))`-bundled `Equiv` φ ≃ φ transports the filter
    cardinality via `Finset.card_equiv`. -/
theorem hypersimplex_palindrome_k_d_minus_1 (d n : ℕ) (hd : 2 ≤ d) :
    hypersimplexLatticeCount d (d - 1) n = hypersimplexLatticeCount d 1 n := by
  -- Step 1 — coordinate-bound helper.
  have hbnd : ∀ (x : Fin d → Fin (n + 1)) (i : Fin d), (x i : ℕ) ≤ n := by
    intro x i; have := (x i).isLt; omega
  -- Step 2 — define the involution φ x i = ⟨n - x i, _⟩.
  let φ : (Fin d → Fin (n + 1)) → (Fin d → Fin (n + 1)) :=
    fun x i => ⟨n - (x i : ℕ), by have := (x i).isLt; omega⟩
  -- Step 3 — φ is an involution.
  have hφφ : ∀ x, φ (φ x) = x := by
    intro x
    funext i
    apply Fin.ext
    show n - (n - (x i : ℕ)) = (x i : ℕ)
    have := hbnd x i
    omega
  -- Step 4 — sum-of-complements identity ∑ φ x_i + ∑ x_i = d * n.
  have hsum : ∀ x : Fin d → Fin (n + 1),
      (∑ i, (φ x i : ℕ)) + (∑ i, (x i : ℕ)) = d * n := by
    intro x
    rw [← Finset.sum_add_distrib]
    have h_pt : ∀ i : Fin d, ((φ x i : ℕ) + (x i : ℕ)) = n := by
      intro i
      show (n - (x i : ℕ)) + (x i : ℕ) = n
      have := hbnd x i
      omega
    simp only [h_pt, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  -- Step 5 — bundle φ as an Equiv via the involution property.
  let e : (Fin d → Fin (n + 1)) ≃ (Fin d → Fin (n + 1)) :=
    { toFun := φ, invFun := φ, left_inv := hφφ, right_inv := hφφ }
  -- Step 6 — apply Finset.card_equiv on the filter sets.
  unfold hypersimplexLatticeCount
  refine Finset.card_equiv e ?_
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Goal: (∑ x_i) = n * (d - 1) ↔ (∑ (e x)_i) = n * 1
  -- Unfold e to φ:
  show (∑ i, (x i : ℕ)) = n * (d - 1) ↔ (∑ i, (φ x i : ℕ)) = n * 1
  have h_total := hsum x
  -- h_total : ∑ φ x_i + ∑ x_i = d * n
  -- Linear-arithmetic bridge: d * n = n * 1 + n * (d - 1) for 1 ≤ d.
  have h_d1 : d * n = n * 1 + n * (d - 1) := by
    have hd1 : 1 ≤ d := by omega
    have : d = 1 + (d - 1) := by omega
    calc d * n = (1 + (d - 1)) * n := by rw [← this]
      _ = 1 * n + (d - 1) * n := by rw [Nat.add_mul]
      _ = n * 1 + n * (d - 1) := by ring
  constructor
  · intro hx
    omega
  · intro hx
    omega

/-! ## Section III — Numeric sanity checks (no `sorry`) -/

/-- Sanity: `n · Δ(2, 1)` at `n = 2` contains 3 lattice points
    (namely (0,2), (1,1), (2,0)). -/
theorem hypersimplex_count_2_1_2 :
    hypersimplexLatticeCount 2 1 2 = 3 := by
  decide

/-- Sanity: `n · Δ(3, 1)` at `n = 1` contains 3 lattice points
    (the 3 standard basis directions). -/
theorem hypersimplex_count_3_1_1 :
    hypersimplexLatticeCount 3 1 1 = 3 := by
  decide

/-- Sanity: `n · Δ(3, 2)` at `n = 1` contains 3 lattice points
    (by the palindrome Δ(3, 2) ↔ Δ(3, 1)). -/
theorem hypersimplex_count_3_2_1 :
    hypersimplexLatticeCount 3 2 1 = 3 := by
  decide

/-- Sanity: the binomial RHS at `d = 3`, `n = 2` is `C(4, 2) = 6`,
    matching `hypersimplexLatticeCount 3 1 2`. -/
theorem hypersimplex_count_3_1_2 :
    hypersimplexLatticeCount 3 1 2 = (2 + 3 - 1).choose (3 - 1) := by
  decide

end EhrhartCubeProvenOQ03
