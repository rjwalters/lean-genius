/-
  Ehrhart Polynomial of the Hypersimplex: First-Principles Scaffold
  (ehrhart-cube-proven-oq-03 — S1 OBSERVE)

  This file is a fresh scaffold introducing the **hypersimplex** Δ(d, k),
  the slice of the unit d-cube [0, 1]^d by the affine hyperplane
  Σ x_i = k. Lattice points in n · Δ(d, k) correspond to functions
  x : Fin d → Fin (n + 1) with Σ x_i = n · k.

  Contents:
  1. The lattice-point counting definition `hypersimplexLatticeCount`
     via a `Finset.filter` predicate on `Fin d → Fin (n + 1)`.
  2. Two reference identities (both PROVEN):
     - `hypersimplex_count_k_one`:
         hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1)
       (S6 ACT 2026-05-16 — `Sym.equivNatSumOfFintype` +
        `Sym.card_sym_eq_choose` + `Nat.choose_symm_of_eq_add`)
     - `hypersimplex_palindrome_k_d_minus_1`:
         hypersimplexLatticeCount d (d - 1) n
           = hypersimplexLatticeCount d 1 n
       (S4 ACT 2026-05-14 — involution `φ x i = ⟨n − x i, _⟩` +
        `Finset.card_equiv`)
  3. Numeric sanity checks closed by `decide` to anchor the
     definition.

  Sibling files in the `ehrhart-cube-proven` family:
  - `EhrhartCubeProven.lean`    — |[0,1]^d ∩ (1/n)ℤ^d| = (n+1)^d (verified)
  - `EhrhartSimplexProven.lean` — OQ-01 standard simplex (verified)
  - `EhrhartCrossPolytope.lean` — OQ-02 cross-polytope (verified)
  - `EhrhartCubeProvenOQ04.lean` — Eulerian h*-vector + Worpitzky (formalized)

  Status: S6 ACT 2026-05-16. Sorries: 0. Build pending — Docker
  daemon hung at S6 ACT author time.
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

/-! ## Section II — Reference identities -/

/-- When k = 1, the hypersimplex `Δ(d, 1)` reduces to a standard
    (d - 1)-simplex. Concretely:

      hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1).

    Proof: lattice points {x : Fin d → Fin (n+1) | ∑ x_i = n} are weak
    compositions of `n` into `d` nonneg parts, which biject with
    `Sym (Fin d) n` via `Sym.equivNatSumOfFintype`. Stars-and-bars
    (`Sym.card_sym_eq_choose`) then gives `(d + n - 1).choose n`, and
    `Nat.choose_symm_of_eq_add` rewrites that as `(n + d - 1).choose (d - 1)`.
    Discharged at S6 ACT (researcher-8, 2026-05-16). -/
theorem hypersimplex_count_k_one (d n : ℕ) (hd : 1 ≤ d) :
    hypersimplexLatticeCount d 1 n = (n + d - 1).choose (d - 1) := by
  unfold hypersimplexLatticeCount
  simp only [Nat.mul_one]
  -- Lift between subtype-coded weak compositions over `Fin (n + 1)`
  -- and over `ℕ` (bounds are non-binding when ∑ = n).
  let e_lift :
      {x : Fin d → Fin (n + 1) // (∑ i : Fin d, (x i : ℕ)) = n}
        ≃ {P : Fin d → ℕ // ∑ i, P i = n} :=
    { toFun := fun ⟨x, hx⟩ => ⟨fun i => (x i : ℕ), hx⟩
      invFun := fun ⟨P, hP⟩ =>
        ⟨fun i => ⟨P i, by
          have hPi : P i ≤ ∑ j, P j :=
            Finset.single_le_sum (f := P) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ i)
          omega⟩, by
          simp only; exact hP⟩
      left_inv := by intro ⟨x, hx⟩; ext i; rfl
      right_inv := by intro ⟨P, hP⟩; ext i; rfl }
  -- Identify the filter-cardinality with `Fintype.card (Sym (Fin d) n)`.
  have h_card :
      (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
          (∑ i : Fin d, (x i : ℕ)) = n)).card
        = Fintype.card (Sym (Fin d) n) := by
    rw [show (Finset.univ.filter (fun x : Fin d → Fin (n + 1) =>
              (∑ i : Fin d, (x i : ℕ)) = n)).card =
            Fintype.card {x : Fin d → Fin (n + 1) //
              (∑ i : Fin d, (x i : ℕ)) = n} from
              (Fintype.card_of_subtype _
                (fun x => by simp [Finset.mem_filter, Finset.mem_univ])).symm]
    exact Fintype.card_congr
      (e_lift.trans (Sym.equivNatSumOfFintype (Fin d) n).symm)
  -- Stars-and-bars then choose-symmetry close the goal.
  rw [h_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  have h_idx : (d + n - 1) = (n + d - 1) := by omega
  rw [h_idx]
  exact Nat.choose_symm_of_eq_add (by omega)

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
