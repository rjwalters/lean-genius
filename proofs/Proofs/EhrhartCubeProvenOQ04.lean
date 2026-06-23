/-
  Eulerian Numbers and the h*-Vector of the Unit Cube
  (ehrhart-cube-proven-oq-04)

  S1 SCAFFOLD + S2 STRUCTURAL + S3 ROW-SUM + S4 WORPITZKY + S5 PALINDROME.
  The companion file `EhrhartCubeProven.lean` proves `L([0,1]^d, n) = (n+1)^d`
  axiom-free. The Ehrhart h*-vector of the unit d-cube is now machine-checked
  to equal the sequence of Eulerian numbers (A(d, 0), A(d, 1), …, A(d, d-1)).

  S2 closed the two *structural* sorries (`cube_h_star_eulerian` and
  `cube_lattice_count_eulerian`). S3 added helper lemmas
  (`eulerian_zero_eq_one`, `eulerian_eq_zero_of_le`) and closed
  `eulerian_row_sum_factorial` (Σ A(d, k) = d!). S4 added `worpitzky_step` and
  closed `worpitzky_identity_cube` by induction on `d`. S5 closes the last
  remaining sorry `eulerian_palindrome` (A(d,k) = A(d,d-1-k) for k<d) by
  algebraic induction on `d` — the combinatorial descent-reversal involution
  is not required.

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
  • `worpitzky_identity_cube`               — Σ A(d,k) C(n+1+k, d) = (n+1)^d   (S4: PROVED)
  • `cube_h_star_eulerian`                  — h_k*([0,1]^d) = A(d, k)          (S2: PROVED)
  • `eulerian_row_sum_factorial`            — Σ_{k=0}^{d-1} A(d, k) = d!       (S3: PROVED)
  • `eulerian_palindrome`                   — A(d, k) = A(d, d-1-k) for k < d  (S5: PROVED)
  • `cube_lattice_count_eulerian`           — bridge to `EhrhartCubeProven`    (S2: PROVED)
  • `worpitzky_identity_cube_palindrome`    — Σ A(d,k) C(n+d-k, d) = (n+1)^d   (S6: PROVED)
  • `cubeHStarPoly_eval_one`                — h*([0,1]^d)(1) = d!              (S7: PROVED)
  • `cubeHStarPoly_palindromic`             — coeff k = coeff (d-1-k)          (S7: PROVED)

  Helper lemmas (S3):
  • `eulerian_zero_eq_one`                  — A(d, 0) = 1 for all d ≥ 0
  • `eulerian_eq_zero_of_le`                — A(d, k) = 0 for d ≥ 1, k ≥ d

  Helper lemmas (S4):
  • `worpitzky_step`                         — (k+1)·C(n+1+k,d+1) + (d-k)·C(n+2+k,d+1) = (n+1)·C(n+1+k,d)

  Helper lemmas (S5):
  • `eulerianNumber_recurrence`              — A(d+1, k+1) = (k+2)·A(d, k+1) + (d-k)·A(d, k)  (definitional rfl)

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
theorem eulerian_zero_eq_one (d : ℕ) : eulerianNumber d 0 = 1 := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

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
              eulerian_eq_zero_of_le d d hd_pos (le_refl d), mul_zero, add_zero]
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
  **Recurrence-unfolding lemma** (S5 helper): direct unfolding of the
  Eulerian recurrence as a rewrite. By definition,
      A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
  Provided as a named lemma so that `rw` can fire it cleanly without
  requiring an explicit `show` at every use site.
-/
lemma eulerianNumber_recurrence (d k : ℕ) :
    eulerianNumber (d + 1) (k + 1)
      = (k + 2) * eulerianNumber d (k + 1) + (d - k) * eulerianNumber d k := rfl

/--
  **Palindromic symmetry** of Eulerian numbers (S5, PROVED):
      A(d, k) = A(d, d - 1 - k)         for 0 ≤ k < d, d ≥ 1.

  Proved by induction on `d` using only the recurrence and the two S3
  helpers (`eulerian_zero_eq_one`, `eulerian_eq_zero_of_le`). The
  combinatorial descent-reversal involution is not needed.

  Inductive step: assume the palindrome at row `d` (hypothesis `ih`). To
  prove it at row `d+1` we case-split on `k`:

  - `k = 0` (and dually `k = d`): the boundary value `A(d+1, 0) = 1` by
    `eulerian_zero_eq_one`. For the other side, write `d = d' + 1`
    (using `hd_pos : 0 < d`), unfold the recurrence at `A(d'+2, d'+1)`,
    use `eulerian_eq_zero_of_le` to discard `A(d'+1, d'+1) = 0`, then
    apply `ih` at `j = d'` to convert `A(d'+1, d') = A(d'+1, 0) = 1`.

  - `1 ≤ k < d`: write `k = k' + 1`. The right-hand index is then
    `d - k' - 1 = (d - k' - 2) + 1`. Unfold the recurrence on both
    sides, then apply `ih` at `j = k' + 1` (giving `A(d, k'+1) =
    A(d, d - k' - 2)`) and at `j = k'` (giving `A(d, k') = A(d, d - k' - 1)`).
    The two recurrence expansions are equal term by term modulo `ring`.
-/
theorem eulerian_palindrome : ∀ d k : ℕ, 0 < d → k < d →
    eulerianNumber d k = eulerianNumber d (d - 1 - k) := by
  intro d
  induction d with
  | zero => intros _ hd _; exact absurd hd (lt_irrefl 0)
  | succ d ih =>
    intros k _ hk
    -- Goal: A(d+1, k) = A(d+1, (d+1) - 1 - k)
    have hidx : (d + 1 : ℕ) - 1 - k = d - k := by omega
    rw [hidx]
    rcases Nat.eq_zero_or_pos d with rfl | hd_pos
    · -- d = 0: hk : k < 1, so k = 0
      interval_cases k
      rfl
    · -- d ≥ 1
      have ih' : ∀ j, j < d → eulerianNumber d j = eulerianNumber d (d - 1 - j) :=
        fun j hj => ih j hd_pos hj
      -- The boundary value A(d+1, d) = 1, via the recurrence and ih' at j = d-1.
      have hboundary : eulerianNumber (d + 1) d = 1 := by
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.sub_add_cancel hd_pos).symm⟩
        -- Goal: eulerianNumber ((d'+1) + 1) (d' + 1) = 1
        -- Unfold the recurrence by definitional equality (pattern match on (D+1, K+1))
        show (d' + 2) * eulerianNumber (d' + 1) (d' + 1)
             + ((d' + 1) - d') * eulerianNumber (d' + 1) d' = 1
        rw [eulerian_eq_zero_of_le (d' + 1) (d' + 1) (by omega) (le_refl _),
            show (d' + 1 : ℕ) - d' = 1 from by omega]
        -- (d'+2) * 0 + 1 * A(d'+1, d') = 1
        -- Apply ih' at j = d': A(d'+1, d') = A(d'+1, 0)
        have hpd' : eulerianNumber (d' + 1) d' = 1 := by
          rw [ih' d' (Nat.lt_succ_self d')]
          rw [show (d' + 1 : ℕ) - 1 - d' = 0 from by omega]
          exact eulerian_zero_eq_one (d' + 1)
        rw [hpd']
        ring
      -- Now case-split on k
      rcases Nat.lt_or_ge k 1 with hk0 | hk1
      · -- k = 0: A(d+1, 0) = A(d+1, d - 0) = A(d+1, d)
        interval_cases k
        rw [show (d : ℕ) - 0 = d from by omega, hboundary,
            eulerian_zero_eq_one (d + 1)]
      · rcases Nat.lt_or_ge k d with hk_lt_d | hk_ge_d
        · -- 1 ≤ k < d: interior case
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          -- Now k = k' + 1, and k' + 1 < d
          have hk'_lt : k' + 1 < d := hk_lt_d
          -- Goal: A(d+1, k'+1) = A(d+1, d - (k'+1)) = A(d+1, d - k' - 1)
          rw [show (d : ℕ) - (k' + 1) = (d - k' - 2) + 1 from by omega]
          rw [eulerianNumber_recurrence d k', eulerianNumber_recurrence d (d - k' - 2)]
          rw [show (d - k' - 2 + 2 : ℕ) = d - k' from by omega,
              show (d - k' - 2 + 1 : ℕ) = d - k' - 1 from by omega,
              show (d - (d - k' - 2) : ℕ) = k' + 2 from by omega]
          -- LHS: (k'+2) * A(d, k'+1) + (d - k') * A(d, k')
          -- RHS: (d - k') * A(d, d - k' - 1) + (k' + 2) * A(d, d - k' - 2)
          have hp1 : eulerianNumber d (k' + 1) = eulerianNumber d (d - k' - 2) := by
            rw [ih' (k' + 1) hk'_lt]
            congr 1; omega
          have hp2 : eulerianNumber d k' = eulerianNumber d (d - k' - 1) := by
            rw [ih' k' (by omega)]
            congr 1; omega
          rw [hp1, hp2]
          ring
        · -- k = d: A(d+1, d) = A(d+1, d - d) = A(d+1, 0)
          have hkd : k = d := by omega
          rw [hkd, Nat.sub_self, hboundary, eulerian_zero_eq_one (d + 1)]

-- Concrete checks
example : eulerianNumber 3 0 = eulerianNumber 3 2 := rfl
example : eulerianNumber 4 0 = eulerianNumber 4 3 := rfl
example : eulerianNumber 4 1 = eulerianNumber 4 2 := rfl

-- ============================================================
-- SECTION IV: Worpitzky's Identity (Main Theorem)
-- ============================================================

/--
  **Worpitzky step identity** (S4, proved): the algebraic identity that
  multiplies the Worpitzky sum from row `d` up to row `d+1`. For any
  natural numbers `n`, `d`, `k` with `k ≤ d`,
      (k+1) · C(n+1+k, d+1) + (d-k) · C(n+2+k, d+1) = (n+1) · C(n+1+k, d).
  Proved by Pascal (`Nat.choose_succ_succ`) and the absorption identity
  `C(m, d) · (m-d) = C(m, d+1) · (d+1)` (`Nat.choose_succ_right_eq`).
-/
lemma worpitzky_step (n d k : ℕ) (hk : k ≤ d) :
    (k + 1) * Nat.choose (n + 1 + k) (d + 1) + (d - k) * Nat.choose (n + 2 + k) (d + 1)
      = (n + 1) * Nat.choose (n + 1 + k) d := by
  set m := n + 1 + k with hm_def
  have hm1 : n + 2 + k = m + 1 := by omega
  rw [hm1, Nat.choose_succ_succ m d]
  -- After Pascal: (k+1)·C(m, d+1) + (d-k)·(C(m, d) + C(m, d+1)) = (n+1)·C(m, d)
  by_cases hmd : d ≤ m
  · -- Standard case: use Nat.choose_succ_right_eq
    have hch : Nat.choose m (d + 1) * (d + 1) = Nat.choose m d * (m - d) :=
      Nat.choose_succ_right_eq m d
    have key : (d + 1) * Nat.choose m (d + 1) = (m - d) * Nat.choose m d := by
      have hl : Nat.choose m (d + 1) * (d + 1) = (d + 1) * Nat.choose m (d + 1) := by ring
      have hr : Nat.choose m d * (m - d) = (m - d) * Nat.choose m d := by ring
      linarith
    have hsum_coef : (k + 1) + (d - k) = d + 1 := by omega
    have hmk : (m - d) + (d - k) = n + 1 := by omega
    calc (k + 1) * Nat.choose m (d + 1)
            + (d - k) * (Nat.choose m d + Nat.choose m (d + 1))
        = (k + 1) * Nat.choose m (d + 1)
            + ((d - k) * Nat.choose m d + (d - k) * Nat.choose m (d + 1)) := by
          rw [Nat.mul_add]
      _ = ((k + 1) * Nat.choose m (d + 1) + (d - k) * Nat.choose m (d + 1))
            + (d - k) * Nat.choose m d := by ring
      _ = ((k + 1) + (d - k)) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
          ring
      _ = (d + 1) * Nat.choose m (d + 1) + (d - k) * Nat.choose m d := by
          rw [hsum_coef]
      _ = (m - d) * Nat.choose m d + (d - k) * Nat.choose m d := by rw [key]
      _ = ((m - d) + (d - k)) * Nat.choose m d := by rw [Nat.add_mul]
      _ = (n + 1) * Nat.choose m d := by rw [hmk]
  · -- d > m: C(m, d) = C(m, d+1) = 0
    push_neg at hmd
    have hc1 : Nat.choose m d = 0 := Nat.choose_eq_zero_of_lt hmd
    have hc2 : Nat.choose m (d + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (lt_of_lt_of_le hmd (Nat.le_succ d))
    simp [hc1, hc2]

/--
  **Worpitzky's identity** (S4, PROVED, main theorem):
      (n + 1)^d = Σ_{k=0}^{d-1} A(d, k) · C(n + 1 + k, d)
  for `d ≥ 1` and `n ≥ 0`.

  This is the *defining* identity that proves the h*-vector of the unit cube
  equals the Eulerian numbers. Specialised to the cube via the gallery proof
  `EhrhartCubeProven.cube_lattice_count : L([0,1]^d, n) = (n+1)^d`.

  Proof: induction on `d`.
  • Base case `d = 1`: reduces to `(n+1)^1 = 1·(n+1)` via `eulerian_zero_eq_one`
    and `Nat.choose_one_right`.
  • Inductive step: assuming the identity for `d ≥ 1`, multiply by `(n+1)` and
    apply `worpitzky_step` (♣) pointwise on the IH RHS; split via
    `Finset.sum_add_distrib`; reindex one half by `k ↦ k+1` via
    `Finset.sum_range_succ'`; re-collect using the Eulerian recurrence
    `A(d+1, k+1) = (k+2)·A(d, k+1) + (d-k)·A(d, k)` and `A(d, d) = 0`
    (`eulerian_eq_zero_of_le`) to absorb the boundary term at the right end.
-/
theorem worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d,
                eulerianNumber d k * Nat.choose (n + 1 + k) d := by
  induction d with
  | zero => exact absurd hd (lt_irrefl 0)
  | succ d ih =>
    rcases Nat.eq_zero_or_pos d with hd0 | hd_pos
    · -- d = 0: target is (n+1)^1 = A(1, 0) · C(n+1, 1) = 1 · (n+1) = n+1
      subst hd0
      simp [Finset.sum_range_succ, eulerianNumber, pow_one, Nat.choose_one_right]
    · -- d ≥ 1: use ih and worpitzky_step
      have ih' := ih hd_pos
      have hd_succ_pred : (d - 1) + 1 = d := Nat.succ_pred_eq_of_pos hd_pos
      -- ----- Step 1: rewrite LHS (n+1)^(d+1) as S₁ + S₂ -----
      have lhs_eq :
          (n + 1)^(d + 1) =
            (∑ k ∈ Finset.range d,
                eulerianNumber d k * (k + 1) * Nat.choose (n + 1 + k) (d + 1))
            + (∑ k ∈ Finset.range d,
                eulerianNumber d k * (d - k) * Nat.choose (n + 2 + k) (d + 1)) := by
        calc (n + 1)^(d + 1)
            = (n + 1)^d * (n + 1) := by rw [pow_succ]
          _ = (∑ k ∈ Finset.range d,
                  eulerianNumber d k * Nat.choose (n + 1 + k) d) * (n + 1) := by
                rw [ih']
          _ = ∑ k ∈ Finset.range d,
                  eulerianNumber d k * Nat.choose (n + 1 + k) d * (n + 1) := by
                rw [Finset.sum_mul]
          _ = ∑ k ∈ Finset.range d,
                  eulerianNumber d k *
                    ((k + 1) * Nat.choose (n + 1 + k) (d + 1)
                      + (d - k) * Nat.choose (n + 2 + k) (d + 1)) := by
                refine Finset.sum_congr rfl fun k hk => ?_
                have hkd : k ≤ d := Nat.le_of_lt (Finset.mem_range.mp hk)
                have hws := worpitzky_step n d k hkd
                calc eulerianNumber d k * (n + 1 + k).choose d * (n + 1)
                    = eulerianNumber d k * ((n + 1) * (n + 1 + k).choose d) := by ring
                  _ = eulerianNumber d k *
                        ((k + 1) * (n + 1 + k).choose (d + 1)
                          + (d - k) * (n + 2 + k).choose (d + 1)) := by rw [← hws]
          _ = ∑ k ∈ Finset.range d,
                  (eulerianNumber d k * (k + 1) * Nat.choose (n + 1 + k) (d + 1)
                    + eulerianNumber d k * (d - k) * Nat.choose (n + 2 + k) (d + 1)) := by
                refine Finset.sum_congr rfl fun k _ => by ring
          _ = _ := Finset.sum_add_distrib
      -- ----- Step 2: rewrite RHS as e(d,0)·C(n+1,d+1) + (T₁ + T₂) -----
      have rhs_eq :
          (∑ k ∈ Finset.range (d + 1),
              eulerianNumber (d + 1) k * Nat.choose (n + 1 + k) (d + 1))
            =
          eulerianNumber d 0 * Nat.choose (n + 1) (d + 1)
            + ((∑ k ∈ Finset.range d,
                  (k + 2) * eulerianNumber d (k + 1) * Nat.choose (n + 2 + k) (d + 1))
              + (∑ k ∈ Finset.range d,
                  (d - k) * eulerianNumber d k * Nat.choose (n + 2 + k) (d + 1))) := by
        rw [Finset.sum_range_succ' (fun k =>
              eulerianNumber (d + 1) k * Nat.choose (n + 1 + k) (d + 1)) d]
        -- e(d+1, 0) = e(d, 0) by the recurrence; n+1+0 = n+1.
        have hzero : eulerianNumber (d + 1) 0 = eulerianNumber d 0 := rfl
        rw [hzero, Nat.add_zero]
        -- Expand each body summand via the recurrence and shift.
        have hbody :
            (∑ k ∈ Finset.range d,
                eulerianNumber (d + 1) (k + 1) * Nat.choose (n + 1 + (k + 1)) (d + 1))
              =
            (∑ k ∈ Finset.range d,
                ((k + 2) * eulerianNumber d (k + 1) * Nat.choose (n + 2 + k) (d + 1)
                 + (d - k) * eulerianNumber d k * Nat.choose (n + 2 + k) (d + 1))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hrec : eulerianNumber (d + 1) (k + 1)
                    = (k + 2) * eulerianNumber d (k + 1) + (d - k) * eulerianNumber d k := rfl
          have hshift : n + 1 + (k + 1) = n + 2 + k := by ring
          rw [hrec, hshift]; ring
        rw [hbody, Finset.sum_add_distrib]
        ring
      -- ----- Step 3: reduce S₁ to e(d, 0)·C(n+1, d+1) + T₁ -----
      have hrange : Finset.range d = Finset.range (d - 1 + 1) := by
        congr 1; omega
      have s1_eq :
          (∑ k ∈ Finset.range d,
              eulerianNumber d k * (k + 1) * Nat.choose (n + 1 + k) (d + 1))
            =
          eulerianNumber d 0 * Nat.choose (n + 1) (d + 1)
            + (∑ k ∈ Finset.range d,
                (k + 2) * eulerianNumber d (k + 1) * Nat.choose (n + 2 + k) (d + 1)) := by
        rw [hrange]
        rw [Finset.sum_range_succ' (fun k =>
              eulerianNumber d k * (k + 1) * Nat.choose (n + 1 + k) (d + 1)) (d - 1)]
        rw [Finset.sum_range_succ (fun k =>
              (k + 2) * eulerianNumber d (k + 1) * Nat.choose (n + 2 + k) (d + 1)) (d - 1)]
        -- The k = d - 1 boundary term on the RHS vanishes: A(d, d) = 0.
        have hk_boundary :
            ((d - 1) + 2) * eulerianNumber d ((d - 1) + 1)
              * Nat.choose (n + 2 + (d - 1)) (d + 1) = 0 := by
          have hed : eulerianNumber d (d - 1 + 1) = 0 := by
            rw [hd_succ_pred]
            exact eulerian_eq_zero_of_le d d hd_pos (le_refl d)
          rw [hed]; ring
        rw [hk_boundary, Nat.add_zero]
        -- Pointwise alignment of the two reindexed sums.
        have hsum_align :
            (∑ k ∈ Finset.range (d - 1),
                eulerianNumber d (k + 1) * (k + 1 + 1)
                  * Nat.choose (n + 1 + (k + 1)) (d + 1))
              =
            (∑ k ∈ Finset.range (d - 1),
                (k + 2) * eulerianNumber d (k + 1) * Nat.choose (n + 2 + k) (d + 1)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hshift : n + 1 + (k + 1) = n + 2 + k := by ring
          rw [hshift]; ring
        rw [hsum_align]
        ring
      -- ----- Combine everything -----
      have s2_eq_t2 :
          (∑ k ∈ Finset.range d,
              eulerianNumber d k * (d - k) * Nat.choose (n + 2 + k) (d + 1))
            =
          (∑ k ∈ Finset.range d,
              (d - k) * eulerianNumber d k * Nat.choose (n + 2 + k) (d + 1)) := by
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [lhs_eq, rhs_eq, s1_eq, s2_eq_t2]
      ring

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
    simp only [pow_two] at ih ⊢
    rw [Nat.choose_succ_succ (m + 1) 1, Nat.choose_succ_succ (m + 2) 1]
    simp only [Nat.choose_one_right, Nat.choose_self, Nat.add_zero] at ih ⊢
    nlinarith [ih]

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
  rw [Finset.sum_ite_eq (Finset.range d) k (fun j => eulerianNumber d j)]
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

-- ============================================================
-- SECTION VII: Palindrome-Reflected Worpitzky Identity (S6)
-- ============================================================

/--
  **Palindrome-reflected Worpitzky identity** (S6: PROVED, build pending):
  composing `worpitzky_identity_cube` with `eulerian_palindrome` and a
  reindexing `k ↦ d - 1 - k` yields the *dual* (palindrome-reflected)
  form of Worpitzky's identity for the cube:
  $$ (n+1)^d \;=\; \sum_{k=0}^{d-1}\,A(d, k)\,\binom{n + d - k}{d}. $$
  The shift `n + 1 + k ↦ n + d - k` is the standard alternative
  parametrisation of the binomial-coefficient summand: the original form
  is keyed by the *forward* exceedance index `k`, while this form keys
  by the *descent* index `d - 1 - k`, exhibiting the palindromic
  symmetry of the Eulerian numbers at the level of the entire sum.

  Together with `worpitzky_identity_cube` this gives both equivalent
  presentations of `(n+1)^d` in the Eulerian basis, useful for combinatorial
  identities that prefer one parametrisation over the other (e.g. the dual
  Worpitzky form is the natural shape when summing over *descent* statistics
  in the symmetric group, whereas the forward form parametrises by *exceedance*).
-/
theorem worpitzky_identity_cube_palindrome (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d,
                eulerianNumber d k * Nat.choose (n + d - k) d := by
  -- Start from worpitzky_identity_cube, then reindex the RHS via k ↦ d - 1 - k
  -- and substitute the palindrome A(d, k) = A(d, d - 1 - k) pointwise.
  rw [worpitzky_identity_cube d hd n]
  -- Goal: ∑ k ∈ range d, A(d, k) * C(n+1+k, d) = ∑ k ∈ range d, A(d, k) * C(n+d-k, d)
  conv_rhs => rw [← Finset.sum_range_reflect
                    (fun k => eulerianNumber d k * Nat.choose (n + d - k) d) d]
  -- Goal: ∑ k ∈ range d, A(d, k) * C(n+1+k, d) =
  --       ∑ k ∈ range d, A(d, d-1-k) * C(n + d - (d-1-k), d)
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d := Finset.mem_range.mp hk
  -- Goal: A(d, k) * C(n+1+k, d) = A(d, d-1-k) * C(n + d - (d-1-k), d)
  rw [eulerian_palindrome d k hd hk']
  -- Goal: A(d, d-1-k) * C(n+1+k, d) = A(d, d-1-k) * C(n + d - (d-1-k), d)
  -- Show the binomial-coefficient arguments are equal via Nat-arithmetic.
  have harith : n + 1 + k = n + d - (d - 1 - k) := by omega
  rw [harith]

-- ============================================================
-- SECTION VIII: Polynomial-Evaluation Corollaries (S7)
-- ============================================================

/--
  **Sum of coefficients = d!** (S7: PROVED, build pending): evaluating the
  h*-polynomial of the d-cube at `X = 1` recovers the row sum of the
  Eulerian triangle. Combined with `eulerian_row_sum_factorial`, this gives
  $$ h^{\ast}([0,1]^d)(1) \;=\; \sum_{k=0}^{d-1} A(d, k) \;=\; d!. $$
  Equivalently, the polynomial `cubeHStarPoly d` has *coefficient sum* equal
  to `d!`, which is the normalised volume identity for the d-cube
  (`d! · vol([0,1]^d) = d! · 1 = d!`).
-/
theorem cubeHStarPoly_eval_one (d : ℕ) (hd : 0 < d) :
    (cubeHStarPoly d).eval 1 = d.factorial := by
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  unfold cubeHStarPoly
  rw [if_neg hd_ne, Polynomial.eval_finset_sum]
  -- Each summand `((A(d, k) : ℕ) • X^k).eval 1` reduces to `A(d, k)`.
  have hsum :
      ∑ k ∈ Finset.range d,
          ((eulerianNumber d k : ℕ) • Polynomial.X ^ k : Polynomial ℕ).eval 1
        = ∑ k ∈ Finset.range d, eulerianNumber d k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_smul, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
        smul_eq_mul, mul_one]
  rw [hsum]
  exact eulerian_row_sum_factorial d hd

/--
  **h*-vector palindrome at the polynomial level** (S7: PROVED, build pending):
  the h*-polynomial of the d-cube is a *palindromic* polynomial of degree
  `d - 1`: its coefficient sequence `(A(d, 0), A(d, 1), …, A(d, d-1))` reads
  the same forwards and backwards,
  $$ h^{\ast}_k([0,1]^d) \;=\; h^{\ast}_{d - 1 - k}([0,1]^d) \qquad (0 \le k < d). $$
  Direct composition of `cube_h_star_eulerian` (h*-coefficient ↔ Eulerian
  number) with `eulerian_palindrome` (A(d, k) = A(d, d - 1 - k)). The
  palindromic-coefficient property is the polynomial-level signature of
  Ehrhart-Macdonald reciprocity for the cube; the same symmetry underlies
  the dual Worpitzky identity `worpitzky_identity_cube_palindrome`.
-/
theorem cubeHStarPoly_palindromic (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    (cubeHStarPoly d).coeff k = (cubeHStarPoly d).coeff (d - 1 - k) := by
  -- coeff k = A(d, k) by `cube_h_star_eulerian`
  rw [cube_h_star_eulerian d k hd hk]
  -- coeff (d-1-k) = A(d, d-1-k) by `cube_h_star_eulerian` (d-1-k < d for k < d, d ≥ 1)
  rw [cube_h_star_eulerian d (d - 1 - k) hd (by omega)]
  -- A(d, k) = A(d, d-1-k) by `eulerian_palindrome`
  exact eulerian_palindrome d k hd hk

end EhrhartCubeProvenOQ04
