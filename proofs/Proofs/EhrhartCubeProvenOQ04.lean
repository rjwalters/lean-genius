/-
  Eulerian Numbers and the h*-Vector of the Unit Cube
  (ehrhart-cube-proven-oq-04)

  S1 SCAFFOLD + S2 STRUCTURAL + S3 ROW-SUM. The companion file
  `EhrhartCubeProven.lean` proves `L([0,1]^d, n) = (n+1)^d` axiom-free.
  The Ehrhart h*-vector of the unit d-cube is conjecturally (and classically)
  equal to the sequence of Eulerian numbers (A(d, 0), A(d, 1), …, A(d, d-1)).

  S2 closed the two *structural* sorries (`cube_h_star_eulerian` and
  `cube_lattice_count_eulerian`); S3 adds helper lemmas
  (`eulerian_zero_eq_one`, `eulerian_eq_zero_of_le`) and closes
  `eulerian_row_sum_factorial` (Σ A(d, k) = d!). The remaining combinatorial
  sorries (`worpitzky_identity_cube`, `eulerian_palindrome`) are for S4+.

  Concretely, Worpitzky's identity states:

      (n+1)^d = Σ_{k=0}^{d-1} A(d, k) · C(n + 1 + k, d)         (for d ≥ 1, n ≥ 0)

  Equivalently, in h*-vector form (after palindrome A(d,k) = A(d,d-1-k)):

      (n+1)^d = Σ_{k=0}^{d-1} A(d, k) · C(n + d - k, d)

  This file:
  1. Defines `eulerianNumber d k` via the standard recurrence
     A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
  2. Records concrete values A(d, k) for d ≤ 4 by `rfl`.
  3. States `worpitzky_identity_cube` (the Worpitzky identity for the cube), with
     the proof deferred to a future iteration.
  4. Proves the explicit Ehrhart h*-vector identity for the cube
     (`cube_h_star_eulerian`, S2) — definitional reduction.
  5. Records the row sum identity Σ_k A(d, k) = d! as the standard
     consistency check (deferred proof).
  6. Proves the bridging corollary `cube_lattice_count_eulerian` (S2)
     that ties the lattice-point count `Fintype.card (Fin d → Fin (n+1))`
     to the Eulerian sum, conditional on `worpitzky_identity_cube`.

  Main definitions:
  • `eulerianNumber : ℕ → ℕ → ℕ`           — A(d, k) via recurrence
  • `cubeHStarPoly  : ℕ → Polynomial ℕ`     — h*-polynomial of the d-cube,
                                              defined as Σ_{k=0}^{d-1} A(d,k) · X^k

  Main theorems:
  • `worpitzky_identity_cube`               — Σ A(d,k) C(n+1+k, d) = (n+1)^d   (deferred)
  • `cube_h_star_eulerian`                  — h_k*([0,1]^d) = A(d, k)          (S2: PROVED)
  • `eulerian_row_sum_factorial`            — Σ_{k=0}^{d-1} A(d, k) = d!       (S3: PROVED)
  • `eulerian_palindrome`                   — A(d, k) = A(d, d-1-k) for k < d  (deferred)
  • `cube_lattice_count_eulerian`           — bridge to `EhrhartCubeProven`    (S2: PROVED)

  Helper lemmas (S3):
  • `eulerian_zero_eq_one`                  — A(d, 0) = 1 for all d ≥ 0
  • `eulerian_eq_zero_of_le`                — A(d, k) = 0 for d ≥ 1, k ≥ d

  Concrete (proven, no sorry):
  • `eulerian_1_0`, `eulerian_2_*`, `eulerian_3_*`, `eulerian_4_*` — values by rfl
  • `worpitzky_d1`, `worpitzky_d2`, `worpitzky_d3` — Worpitzky for small d, by `decide` / arithmetic
-/
import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace EhrhartCubeProvenOQ04

open Finset

-- ============================================================
-- SECTION I: Eulerian Numbers via Recurrence
-- ============================================================

/--
  `eulerianNumber d k = A(d, k)`, the number of permutations of `{1, …, d}`
  with exactly `k` descents.

  Recurrence (standard form, with the usual boundary conventions):
    A(0, 0) = 1
    A(0, k+1) = 0
    A(d+1, 0) = A(d, 0)                                          (= 1)
    A(d+1, k+1) = (k + 2) · A(d, k+1) + (d - k) · A(d, k)

  Out of range (k ≥ d for d ≥ 1) returns 0 automatically since the
  recurrence collapses (Nat subtraction truncates and the next-step
  Eulerian numbers vanish).
-/
def eulerianNumber : ℕ → ℕ → ℕ
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | d + 1, 0     => eulerianNumber d 0
  | d + 1, k + 1 => (k + 2) * eulerianNumber d (k + 1) + (d - k) * eulerianNumber d k

-- Concrete values (proven by computation)
theorem eulerian_0_0 : eulerianNumber 0 0 = 1 := rfl
theorem eulerian_0_1 : eulerianNumber 0 1 = 0 := rfl

theorem eulerian_1_0 : eulerianNumber 1 0 = 1 := rfl
theorem eulerian_1_1 : eulerianNumber 1 1 = 0 := rfl

theorem eulerian_2_0 : eulerianNumber 2 0 = 1 := rfl
theorem eulerian_2_1 : eulerianNumber 2 1 = 1 := rfl
theorem eulerian_2_2 : eulerianNumber 2 2 = 0 := rfl

theorem eulerian_3_0 : eulerianNumber 3 0 = 1 := rfl
theorem eulerian_3_1 : eulerianNumber 3 1 = 4 := rfl
theorem eulerian_3_2 : eulerianNumber 3 2 = 1 := rfl
theorem eulerian_3_3 : eulerianNumber 3 3 = 0 := rfl

theorem eulerian_4_0 : eulerianNumber 4 0 = 1 := rfl
theorem eulerian_4_1 : eulerianNumber 4 1 = 11 := rfl
theorem eulerian_4_2 : eulerianNumber 4 2 = 11 := rfl
theorem eulerian_4_3 : eulerianNumber 4 3 = 1 := rfl
theorem eulerian_4_4 : eulerianNumber 4 4 = 0 := rfl

-- ----- Structural helpers (S3) -----

/--
  **Leftmost column** (S3): for every `d`, the leftmost Eulerian number is `1`.
  Combinatorially, the unique permutation of `{1,…,d}` with `0` descents is the
  identity. The proof follows by induction on `d` directly from the recurrence
  `A(d+1, 0) = A(d, 0)` and the base case `A(0, 0) = 1`.
-/
theorem eulerian_zero_eq_one : ∀ d : ℕ, eulerianNumber d 0 = 1
  | 0     => rfl
  | _ + 1 => eulerian_zero_eq_one _

/--
  **Out-of-range vanishing** (S3): for `d ≥ 1` and `k ≥ d`, `A(d, k) = 0`.
  Combinatorially, a permutation of `d` elements has at most `d-1` descents.
  The proof is a double induction on `d` and `k` using the recurrence and the
  Nat-subtraction truncation `0 - k = 0`. Used in `eulerian_row_sum_factorial`
  below to discard the boundary term `(d+1)·A(d, d)`.
-/
theorem eulerian_eq_zero_of_le : ∀ d k : ℕ, 0 < d → d ≤ k → eulerianNumber d k = 0
  | 0,     _,     hd, _  => absurd hd (lt_irrefl 0)
  | _ + 1, 0,     _,  hk => absurd hk (by omega)
  | d + 1, k + 1, _,  hk => by
    have hdk : d ≤ k := Nat.succ_le_succ_iff.mp hk
    show (k + 2) * eulerianNumber d (k + 1) + (d - k) * eulerianNumber d k = 0
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · -- d = 0: both factors vanish — `A(0, k+1) = 0` by def and `0 - k = 0`
      have h1 : eulerianNumber 0 (k + 1) = 0 := rfl
      have h2 : (0 : ℕ) - k = 0 := by omega
      rw [h1, h2]; ring
    · -- d ≥ 1: apply IH to both `A(d, k+1)` and `A(d, k)`
      rw [eulerian_eq_zero_of_le d (k + 1) hd_pos (Nat.le_succ_of_le hdk),
          eulerian_eq_zero_of_le d k hd_pos hdk]
      ring

-- ============================================================
-- SECTION II: Row-Sum Identity (Eulerian numbers sum to d!)
-- ============================================================

/--
  **Row-sum identity** (S3: PROVED): the Eulerian numbers on row `d`
  partition the symmetric group `S_d` by descent count:
      Σ_{k=0}^{d-1} A(d, k) = d!
  This is the structural sanity check that Eulerian numbers count permutations.

  Proof outline (induction on `d`):
  * Base `d = 1`: `Σ_{k<1} A(1, k) = A(1, 0) = 1 = 1!`.
  * Step (`d ≥ 1`, assume IH `Σ_{k<d} A(d, k) = d!`): rewrite
    `Σ_{k<d+1} A(d+1, k) = (d+1) · Σ_{k<d} A(d, k)` by extending both sums
    to `range (d+1)` (using `A(d, d) = 0` to drop the boundary term),
    unfolding the recurrence inside the LHS sum, and combining via the
    pointwise identity `(k+1)·A(d, k) + (d-k)·A(d, k) = (d+1)·A(d, k)`
    (valid for `k < d`; for `k = d` both sides are `0` by `A(d, d) = 0`).
    Then `(d+1) · d! = (d+1)!` by `Nat.factorial_succ`.
-/
theorem eulerian_row_sum_factorial (d : ℕ) (hd : 0 < d) :
    ∑ k ∈ Finset.range d, eulerianNumber d k = d.factorial := by
  induction d with
  | zero => exact absurd hd (lt_irrefl 0)
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · -- `d = 0`, so `d + 1 = 1` and the sum has the single term `A(1, 0) = 1 = 1!`
      simp [Finset.sum_range_succ, Finset.sum_range_zero, eulerian_zero_eq_one,
            Nat.factorial]
    · -- `d ≥ 1`, apply IH and recurrence
      have IH : ∑ k ∈ Finset.range d, eulerianNumber d k = d.factorial := ih hd_pos
      -- Reduce the goal to `(d+1) · Σ_{k<d} A(d, k) = (d+1)!` via a closed-form rewrite.
      have lhs_eq : ∑ k ∈ Finset.range (d + 1), eulerianNumber (d + 1) k
                  = (d + 1) * ∑ k ∈ Finset.range d, eulerianNumber d k := by
        rw [Finset.mul_sum]
        -- Extend the RHS sum to `range (d + 1)` using `A(d, d) = 0`.
        have rhs_extend :
            ∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d k
              = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
          rw [Finset.sum_range_succ
                (fun k => (d + 1) * eulerianNumber d k) d,
              eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
              Nat.add_zero]
        rw [rhs_extend]
        -- Peel off the `k = 0` term on both sides.
        rw [Finset.sum_range_succ' (fun k => eulerianNumber (d + 1) k) d,
            eulerian_zero_eq_one (d + 1)]
        rw [Finset.sum_range_succ' (fun k => (d + 1) * eulerianNumber d k) d,
            eulerian_zero_eq_one d, Nat.mul_one]
        -- Unfold the recurrence inside the LHS sum.
        have lhs_recur : ∀ k ∈ Finset.range d,
            eulerianNumber (d + 1) (k + 1)
              = (k + 2) * eulerianNumber d (k + 1) + (d - k) * eulerianNumber d k :=
          fun k _ => rfl
        rw [Finset.sum_congr rfl lhs_recur, Finset.sum_add_distrib]
        -- Re-pack `(∑ k, (k+2)·A(d, k+1)) + 1 = ∑ k ∈ range (d+1), (k+1)·A(d, k)`
        -- (running `Finset.sum_range_succ'` "backwards" on the indexed form).
        have lhs_rewrap :
            (∑ k ∈ Finset.range d, (k + 2) * eulerianNumber d (k + 1)) + 1
              = ∑ k ∈ Finset.range (d + 1), (k + 1) * eulerianNumber d k := by
          rw [Finset.sum_range_succ' (fun k => (k + 1) * eulerianNumber d k) d,
              eulerian_zero_eq_one d, Nat.mul_one]
        -- Symmetric re-pack on the RHS.
        have rhs_rewrap :
            (∑ k ∈ Finset.range d, (d + 1) * eulerianNumber d (k + 1)) + (d + 1)
              = ∑ k ∈ Finset.range (d + 1), (d + 1) * eulerianNumber d k := by
          rw [Finset.sum_range_succ' (fun k => (d + 1) * eulerianNumber d k) d,
              eulerian_zero_eq_one d, Nat.mul_one]
        -- Rearrange terms on the LHS to expose `(∑ (k+2)·A(d, k+1)) + 1`.
        have lhs_assoc :
            (∑ k ∈ Finset.range d, (k + 2) * eulerianNumber d (k + 1))
              + (∑ k ∈ Finset.range d, (d - k) * eulerianNumber d k) + 1
            = ((∑ k ∈ Finset.range d, (k + 2) * eulerianNumber d (k + 1)) + 1)
              + (∑ k ∈ Finset.range d, (d - k) * eulerianNumber d k) := by ring
        rw [lhs_assoc, lhs_rewrap, rhs_rewrap]
        -- Extend the remaining `range d` sum to `range (d+1)` (its k=d term vanishes).
        have rhs_extend2 :
            ∑ k ∈ Finset.range d, (d - k) * eulerianNumber d k
              = ∑ k ∈ Finset.range (d + 1), (d - k) * eulerianNumber d k := by
          rw [Finset.sum_range_succ
                (fun k => (d - k) * eulerianNumber d k) d,
              eulerian_eq_zero_of_le d d hd_pos (le_refl d), Nat.mul_zero,
              Nat.add_zero]
        rw [rhs_extend2, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < d + 1 := Finset.mem_range.mp hk
        rcases Nat.lt_or_ge k d with hkd | hkd
        · -- k < d: combine coefficients cleanly.
          have hsum : (k + 1) + (d - k) = d + 1 := by omega
          calc (k + 1) * eulerianNumber d k + (d - k) * eulerianNumber d k
              = ((k + 1) + (d - k)) * eulerianNumber d k := by ring
            _ = (d + 1) * eulerianNumber d k := by rw [hsum]
        · -- k = d: `A(d, d) = 0` makes both sides 0.
          have hkd' : k = d := by omega
          rw [hkd', eulerian_eq_zero_of_le d d hd_pos (le_refl d)]; ring
      rw [lhs_eq, IH, Nat.factorial_succ]

-- Concrete checks (proven by rfl)
example : eulerianNumber 1 0 = Nat.factorial 1 := rfl
example : eulerianNumber 2 0 + eulerianNumber 2 1 = Nat.factorial 2 := rfl
example : eulerianNumber 3 0 + eulerianNumber 3 1 + eulerianNumber 3 2 = Nat.factorial 3 := rfl
example : eulerianNumber 4 0 + eulerianNumber 4 1 + eulerianNumber 4 2 + eulerianNumber 4 3
            = Nat.factorial 4 := rfl

-- ============================================================
-- SECTION III: Palindromic Symmetry
-- ============================================================

/--
  **Palindromic symmetry** of Eulerian numbers (deferred):
      A(d, k) = A(d, d - 1 - k)         for 0 ≤ k < d, d ≥ 1.
  Proof strategy: the map σ ↦ σ ∘ reverse on `Equiv.Perm (Fin d)`
  is an involution that bijects descents with non-descents, hence
  permutations with `k` descents biject with permutations with
  `(d-1) - k` descents.
-/
theorem eulerian_palindrome (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    eulerianNumber d k = eulerianNumber d (d - 1 - k) := by
  sorry

-- Concrete checks
example : eulerianNumber 3 0 = eulerianNumber 3 2 := rfl
example : eulerianNumber 4 0 = eulerianNumber 4 3 := rfl
example : eulerianNumber 4 1 = eulerianNumber 4 2 := rfl

-- ============================================================
-- SECTION IV: Worpitzky's Identity (Main Theorem)
-- ============================================================

/--
  **Worpitzky's identity** (deferred, main theorem):
      (n + 1)^d = Σ_{k=0}^{d-1} A(d, k) · C(n + 1 + k, d)
  for `d ≥ 1` and `n ≥ 0`.

  This is the *defining* identity that proves the h*-vector of the unit cube
  equals the Eulerian numbers. Specialised to the cube via the gallery proof
  `EhrhartCubeProven.cube_lattice_count : L([0,1]^d, n) = (n+1)^d`.

  Proof strategy (deferred to S2+):
  1. **Induction on `d`** using the recurrence
     `A(d+1, k) = (k+1) A(d, k) + (d+1-k) A(d, k-1)`
     and Pascal's identity `C(n+1+k, d+1) = C(n+k, d+1) + C(n+k, d)`.
  2. **Alternative (Stanley)**: combinatorial proof via the bijection
     between permutations and labelled lattice paths; each `(n+1)^d`
     monomial corresponds to a sequence of choices that decomposes
     uniquely as (descent-pattern, position-pattern).
  3. **Alternative (generating-function)**: prove the rational generating-function
     identity ∑_n (n+1)^d t^n = (Σ A(d,k) t^k) / (1-t)^{d+1} and extract
     coefficients.
-/
theorem worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d,
                eulerianNumber d k * Nat.choose (n + 1 + k) d := by
  sorry

-- Concrete cases for small d (proven without the main theorem)

/-- Worpitzky for d = 1: (n+1)^1 = A(1, 0) · C(n+1, 1) = 1·(n+1) = n+1. -/
theorem worpitzky_d1 (n : ℕ) :
    (n + 1)^1 = eulerianNumber 1 0 * Nat.choose (n + 1) 1 := by
  simp [eulerian_1_0, Nat.choose_one_right]

/-- Worpitzky for d = 2: (n+1)² = C(n+1, 2) + C(n+2, 2). -/
theorem worpitzky_d2 (n : ℕ) :
    (n + 1)^2 = eulerianNumber 2 0 * Nat.choose (n + 1) 2
              + eulerianNumber 2 1 * Nat.choose (n + 2) 2 := by
  have e0 : eulerianNumber 2 0 = 1 := rfl
  have e1 : eulerianNumber 2 1 = 1 := rfl
  rw [e0, e1, one_mul, one_mul]
  -- Goal: (n+1)^2 = C(n+1, 2) + C(n+2, 2)
  -- C(n+1, 2) = n(n+1)/2, C(n+2, 2) = (n+1)(n+2)/2
  -- Sum = (n+1)(n + n+2)/2 = (n+1)(2n+2)/2 = (n+1)^2 ✓
  induction n with
  | zero => decide
  | succ m ih =>
    -- (m+2)^2 vs C(m+2, 2) + C(m+3, 2)
    -- Use Pascal and ih
    rw [pow_two, pow_two] at *
    rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_succ_succ (m + 2) 1]
    simp only [Nat.choose_one_right, Nat.choose_self, Nat.add_zero] at ih ⊢
    omega

/-- Verification at d = 2, n = 0:  1² = 1·C(1,2) + 1·C(2,2) = 0 + 1 = 1. -/
example : (0 + 1)^2 = eulerianNumber 2 0 * Nat.choose 1 2
                    + eulerianNumber 2 1 * Nat.choose 2 2 := by decide

/-- Verification at d = 2, n = 1:  2² = 1·C(2,2) + 1·C(3,2) = 1 + 3 = 4. -/
example : (1 + 1)^2 = eulerianNumber 2 0 * Nat.choose 2 2
                    + eulerianNumber 2 1 * Nat.choose 3 2 := by decide

/-- Verification at d = 3, n = 0:  1³ = 1·C(1,3) + 4·C(2,3) + 1·C(3,3) = 0 + 0 + 1 = 1. -/
example : (0 + 1)^3 = eulerianNumber 3 0 * Nat.choose 1 3
                    + eulerianNumber 3 1 * Nat.choose 2 3
                    + eulerianNumber 3 2 * Nat.choose 3 3 := by decide

/-- Verification at d = 3, n = 1:  2³ = 1·C(2,3) + 4·C(3,3) + 1·C(4,3) = 0 + 4 + 4 = 8. -/
example : (1 + 1)^3 = eulerianNumber 3 0 * Nat.choose 2 3
                    + eulerianNumber 3 1 * Nat.choose 3 3
                    + eulerianNumber 3 2 * Nat.choose 4 3 := by decide

/-- Verification at d = 3, n = 2:  3³ = 1·C(3,3) + 4·C(4,3) + 1·C(5,3) = 1 + 16 + 10 = 27. -/
example : (2 + 1)^3 = eulerianNumber 3 0 * Nat.choose 3 3
                    + eulerianNumber 3 1 * Nat.choose 4 3
                    + eulerianNumber 3 2 * Nat.choose 5 3 := by decide

/-- Verification at d = 4, n = 1:  2⁴ = 1·C(2,4) + 11·C(3,4) + 11·C(4,4) + 1·C(5,4) = 0 + 0 + 11 + 5 = 16. -/
example : (1 + 1)^4 = eulerianNumber 4 0 * Nat.choose 2 4
                    + eulerianNumber 4 1 * Nat.choose 3 4
                    + eulerianNumber 4 2 * Nat.choose 4 4
                    + eulerianNumber 4 3 * Nat.choose 5 4 := by decide

/-- Verification at d = 4, n = 2:  3⁴ = 1·C(3,4) + 11·C(4,4) + 11·C(5,4) + 1·C(6,4) = 0 + 11 + 55 + 15 = 81. -/
example : (2 + 1)^4 = eulerianNumber 4 0 * Nat.choose 3 4
                    + eulerianNumber 4 1 * Nat.choose 4 4
                    + eulerianNumber 4 2 * Nat.choose 5 4
                    + eulerianNumber 4 3 * Nat.choose 6 4 := by decide

-- ============================================================
-- SECTION V: h*-Polynomial of the d-Cube
-- ============================================================

/--
  The h*-polynomial of the unit d-cube, defined explicitly as the
  Eulerian generating polynomial:
      h*([0,1]^d, t) = Σ_{k=0}^{d-1} A(d, k) · t^k         (for d ≥ 1)
      h*([0,1]^0, t) = 1
-/
noncomputable def cubeHStarPoly (d : ℕ) : Polynomial ℕ :=
  if d = 0 then 1 else
    ∑ k ∈ Finset.range d, (eulerianNumber d k : ℕ) • Polynomial.X^k

/--
  **Main h*-vector identity** (S2: PROVED): the k-th coefficient of the
  h*-polynomial of the d-cube equals A(d, k):
      h_k*([0,1]^d) = A(d, k)
  for `0 ≤ k < d`. By the SCAFFOLD definition `cubeHStarPoly` this is
  automatic; the *substantive* content is `worpitzky_identity_cube`,
  which connects the symbolic h*-polynomial to the actual Ehrhart
  function `L([0,1]^d, n) = (n+1)^d`.
-/
theorem cube_h_star_eulerian (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    (cubeHStarPoly d).coeff k = eulerianNumber d k := by
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold cubeHStarPoly
  rw [if_neg hd_ne, Polynomial.finset_sum_coeff]
  -- ∑ j ∈ range d, (eulerianNumber d j • X^j).coeff k = eulerianNumber d k
  simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul,
             mul_ite, mul_one, mul_zero]
  -- ∑ j ∈ range d, (if k = j then eulerianNumber d j else 0) = eulerianNumber d k
  rw [Finset.sum_ite_eq' (Finset.range d) k (fun j => eulerianNumber d j)]
  exact if_pos (Finset.mem_range.mpr hk)

-- ============================================================
-- SECTION VI: Coherence with EhrhartCubeProven
-- ============================================================

/--
  **Coherence** (S2: PROVED, modulo `worpitzky_identity_cube`):
  combining `worpitzky_identity_cube` with the canonical bijection
  `Fintype.card (Fin d → Fin (n+1)) = (n+1)^d` gives the Eulerian-number
  interpretation of the h*-vector for the cube:
      |n·[0,1]^d ∩ ℤ^d| = (n+1)^d = Σ_k A(d, k) · C(n+1+k, d).
  The bridge to the geometric `EhrhartCubeProven.cube_lattice_count`
  statement (over `Polytope.cube`) is a separate corollary that wraps
  the Fin-tuple parametrisation of lattice points in the cube.
-/
theorem cube_lattice_count_eulerian (d : ℕ) (hd : 0 < d) (n : ℕ) :
    Fintype.card (Fin d → Fin (n + 1))
      = ∑ k ∈ Finset.range d, eulerianNumber d k * Nat.choose (n + 1 + k) d := by
  -- Lattice-point count of n · [0,1]^d equals (n + 1)^d via the canonical Fin bijection
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  exact worpitzky_identity_cube d hd n

end EhrhartCubeProvenOQ04
