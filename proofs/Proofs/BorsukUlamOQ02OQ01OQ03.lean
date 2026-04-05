/-
  Borsuk-Ulam for Non-Cyclic Groups: Dihedral and Symmetric (OQ-02-OQ-01-OQ-03)

  Open Question from BorsukUlamOQ02OQ01:
    "What happens for non-cyclic groups (dihedral, symmetric)?"

  We extend the equivariant BU dimension framework from cyclic groups Z/n
  to two families of non-cyclic groups:
  - D_n: the dihedral group of order 2n (symmetries of regular n-gon)
  - S_n: the symmetric group of order n! (all permutations of n elements)

  Key structural result: Both D_n and S_n contain cyclic subgroups of prime
  order, and subgroup monotonicity (buDim_mono from OQ-02-OQ-01) gives lower
  bounds on their BU dimensions.

  For D_n: contains Z/2 and Z/p for each odd prime p | n, so
    dihedralBUDim n d ≥ max(buDim 2 d, max_{odd prime p | n} buDim p d)

  For S_n: contains Z/p for every prime p ≤ n, so
    symBUDim n d ≥ max_{prime p ≤ n} buDim p d

  All topological content (actual BU dimensions, upper bounds, exact values)
  remains axiomatized. We prove only the lower bounds derivable from
  prime subgroup structure via existing axioms.

  References:
  - Dold, "Simple proofs of some Borsuk-Ulam results" (1983)
  - Fadell & Husseini, "An ideal-valued cohomological index theory" (1988)
  - Matoušek, "Using the Borsuk-Ulam Theorem" (2003), Ch. 6
  - tom Dieck, "Transformation Groups" (1987), Sections 5.4, 7.1
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Proofs.BorsukUlamOQ02OQ01

namespace BorsukUlamNonCyclic

open BorsukUlamOQ02OQ01 Nat

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: DIHEDRAL GROUP BORSUK-ULAM DIMENSION
-- ═══════════════════════════════════════════════════════════════════════

/-- The equivariant Borsuk-Ulam dimension for the dihedral group D_n
    (symmetry group of the regular n-gon, order 2n) acting on a
    d-dimensional real representation space.

    Axiomatic: the full computation requires equivariant topology
    (Fadell-Husseini index, equivariant cohomology) not yet in Mathlib. -/
axiom dihedralBUDim (n d : ℕ) : ℕ

/-- D_n contains Z/2 as a subgroup (reflections).
    Monotonicity: buDim 2 d ≤ dihedralBUDim n d. -/
axiom dihedral_has_Z2 (n d : ℕ) (hn : 1 ≤ n) :
    buDim 2 d ≤ dihedralBUDim n d

/-- D_n contains Z/p for each odd prime p | n (from the rotation subgroup Z/n).
    Monotonicity: buDim p d ≤ dihedralBUDim n d. -/
axiom dihedral_has_rotation_prime (n d p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ n) :
    buDim p d ≤ dihedralBUDim n d

/-- D_1 ≅ Z/2: buDim matches the cyclic group of order 2. -/
axiom dihedralBUDim_one (d : ℕ) : dihedralBUDim 1 d = buDim 2 d

/-- D_2 ≅ Z/2 × Z/2 (Klein four-group): order 4, no odd-prime-order element. -/
axiom dihedralBUDim_two (d : ℕ) : dihedralBUDim 2 d = buDim 2 d

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: SYMMETRIC GROUP BORSUK-ULAM DIMENSION
-- ═══════════════════════════════════════════════════════════════════════

/-- The equivariant Borsuk-Ulam dimension for the symmetric group S_n
    (all permutations of n elements, order n!) acting on a d-dimensional
    real representation space. -/
axiom symBUDim (n d : ℕ) : ℕ

/-- S_n contains Z/p as a subgroup for every prime p ≤ n (via p-cycles).
    Monotonicity: buDim p d ≤ symBUDim n d. -/
axiom sym_has_cyclic_prime (n d p : ℕ) (hp : Nat.Prime p) (hle : p ≤ n) :
    buDim p d ≤ symBUDim n d

/-- S_n contains S_{n-1} (fix one element).
    Monotonicity: symBUDim (n-1) d ≤ symBUDim n d. -/
axiom sym_has_smaller_sym (n d : ℕ) (hn : 1 ≤ n) :
    symBUDim (n - 1) d ≤ symBUDim n d

/-- S_2 ≅ Z/2: only two permutations (identity and swap). -/
axiom symBUDim_two (d : ℕ) : symBUDim 2 d = buDim 2 d

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: LOWER BOUNDS FROM PRIME SUBGROUP STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════

/-- **Lower bound for D_p** (p odd prime): D_p contains Z/2 and Z/p,
    so buDim 2 d ≤ dihedralBUDim p d and buDim p d ≤ dihedralBUDim p d. -/
theorem dihedralBUDim_odd_prime_lower_z2 (p d : ℕ) (hp : Nat.Prime p) :
    buDim 2 d ≤ dihedralBUDim p d :=
  dihedral_has_Z2 p d hp.one_le

theorem dihedralBUDim_odd_prime_lower_zp (p d : ℕ) (hp : Nat.Prime p) :
    buDim p d ≤ dihedralBUDim p d :=
  dihedral_has_rotation_prime p d p hp (dvd_refl p)

/-- **Combined lower bound for D_p**: max of both Z/2 and Z/p bounds. -/
theorem dihedralBUDim_odd_prime_lower (p d : ℕ) (hp : Nat.Prime p) :
    max (buDim 2 d) (buDim p d) ≤ dihedralBUDim p d :=
  Nat.max_le.mpr ⟨dihedral_has_Z2 p d hp.one_le,
                  dihedral_has_rotation_prime p d p hp (dvd_refl p)⟩

/-- **Lower bound for D_n** from any prime factor:
    If p | n, then max(buDim 2 d, buDim p d) ≤ dihedralBUDim n d. -/
theorem dihedralBUDim_from_prime_factor (n d p : ℕ) (hn : 1 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ n) :
    max (buDim 2 d) (buDim p d) ≤ dihedralBUDim n d :=
  Nat.max_le.mpr ⟨dihedral_has_Z2 n d hn,
                  dihedral_has_rotation_prime n d p hp hdvd⟩

/-- **D_6 Z/2 lower bound**: buDim 2 (n+1) = n ≤ dihedralBUDim 6 (n+1). -/
theorem dihedralBUDim_six_z2_bound (n : ℕ) :
    n ≤ dihedralBUDim 6 (n + 1) := by
  have h := dihedral_has_Z2 6 (n + 1) (by norm_num)
  rw [buDim_two] at h
  exact h

/-- **D_6 Z/3 lower bound**: buDim 3 d ≤ dihedralBUDim 6 d (since 3 | 6). -/
theorem dihedralBUDim_six_z3_bound (d : ℕ) :
    buDim 3 d ≤ dihedralBUDim 6 d :=
  dihedral_has_rotation_prime 6 d 3 (by norm_num) (by norm_num)

/-- **D_6 Yang-Borsuk bound** (from Z/3 subgroup):
    For d = 2n: buDim 3 (2n) = 2n-1 ≤ dihedralBUDim 6 (2n). -/
theorem dihedralBUDim_six_yang_borsuk_bound (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ dihedralBUDim 6 (2 * n) := by
  have h := dihedral_has_rotation_prime 6 (2 * n) 3 (by norm_num) (by norm_num)
  rw [buDim_prime 3 n (by norm_num) hn] at h
  exact h

/-- **S_3 lower bounds**: S_3 contains Z/2 (transpositions) and Z/3 (3-cycles). -/
theorem symBUDim_three_z2_bound (d : ℕ) :
    buDim 2 d ≤ symBUDim 3 d :=
  sym_has_cyclic_prime 3 d 2 (by norm_num) (by norm_num)

theorem symBUDim_three_z3_bound (d : ℕ) :
    buDim 3 d ≤ symBUDim 3 d :=
  sym_has_cyclic_prime 3 d 3 (by norm_num) le_rfl

/-- **S_5 lower bound**: S_5 contains Z/5 (5-cycles), giving the sharpest bound. -/
theorem symBUDim_five_lower (d : ℕ) :
    buDim 5 d ≤ symBUDim 5 d :=
  sym_has_cyclic_prime 5 d 5 (by norm_num) le_rfl

/-- **S_5 Yang-Borsuk bound** (from Z/5 subgroup):
    buDim 5 (2n) = 2n-1 ≤ symBUDim 5 (2n). -/
theorem symBUDim_five_yang_borsuk_bound (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ symBUDim 5 (2 * n) := by
  have h := sym_has_cyclic_prime 5 (2 * n) 5 (by norm_num) le_rfl
  rw [buDim_prime 5 n (by norm_num) hn] at h
  exact h

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: MONOTONICITY RESULTS
-- ═══════════════════════════════════════════════════════════════════════

/-- S_n ≥ S_{n-1}: BU dimension non-decreasing in n. -/
theorem symBUDim_monotone (n d : ℕ) (hn : 1 ≤ n) :
    symBUDim (n - 1) d ≤ symBUDim n d :=
  sym_has_smaller_sym n d hn

/-- S_m ≤ S_n for m ≤ n (iterated monotonicity). -/
theorem symBUDim_le_of_le (m n d : ℕ) (hmn : m ≤ n) :
    symBUDim m d ≤ symBUDim n d := by
  induction n with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact le_refl _
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (sym_has_smaller_sym (k + 1) d (by omega))

/-- For S_n, lower bound from any prime p ≤ n. -/
theorem symBUDim_prime_lower (n d p : ℕ) (hp : Nat.Prime p) (hle : p ≤ n) :
    buDim p d ≤ symBUDim n d :=
  sym_has_cyclic_prime n d p hp hle

-- ═══════════════════════════════════════════════════════════════════════
-- PART V: CONCRETE SMALL-CASE BOUNDS
-- ═══════════════════════════════════════════════════════════════════════

-- D_3 (= S_3, order 6): Z/2 gives n ≤ dihedralBUDim 3 (n+1)
example (n : ℕ) : n ≤ dihedralBUDim 3 (n + 1) := by
  have h := dihedral_has_Z2 3 (n + 1) (by norm_num)
  rw [buDim_two] at h; exact h

-- D_5 (order 10): Z/5 Yang-Borsuk bound
example (n : ℕ) (hn : 0 < n) : 2 * n - 1 ≤ dihedralBUDim 5 (2 * n) := by
  have h := dihedral_has_rotation_prime 5 (2 * n) 5 (by norm_num) (by norm_num)
  rw [buDim_prime 5 n (by norm_num) hn] at h; exact h

-- S_4 contains Z/3: buDim 3 d ≤ symBUDim 4 d
example (d : ℕ) : buDim 3 d ≤ symBUDim 4 d :=
  sym_has_cyclic_prime 4 d 3 (by norm_num) (by norm_num)

-- S_6 contains Z/5: buDim 5 d ≤ symBUDim 6 d
example (d : ℕ) : buDim 5 d ≤ symBUDim 6 d :=
  sym_has_cyclic_prime 6 d 5 (by norm_num) (by norm_num)

-- symBUDim is monotone: S_2 ≤ S_6
example (d : ℕ) : symBUDim 2 d ≤ symBUDim 6 d :=
  symBUDim_le_of_le 2 6 d (by norm_num)

end BorsukUlamNonCyclic
