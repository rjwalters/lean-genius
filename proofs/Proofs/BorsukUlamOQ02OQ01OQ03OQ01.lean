/-
  Borsuk-Ulam for Dihedral Groups: the Prime-Subgroup Lower Bound is General,
  and Tightness Reduces to a Single Upper Bound  (OQ-02-OQ-01-OQ-03-OQ-01)

  Open question from BorsukUlamOQ02OQ01OQ03 (openQuestions[0]):
    "Are the dihedral lower bounds tight? Is
       dihedralBUDim n d = max(buDim 2 d, max_{p odd prime | n} buDim p d)?
     This would require RO(D_n)-graded equivariant cohomology to prove the
     matching upper bound."

  The parent file proved the lower bound only for individual small cases
  (D_p, D_5, D_6) by hand. Here we:

  1. State the conjectured exact value uniformly in n as a `Finset.sup` over the
     prime divisors of n, combined with the reflection Z/2 contribution:
         dihedralLowerBound n d = max (buDim 2 d) (∑⁻ over p ∣ n of buDim p d).
     (Including p = 2 in the sup is harmless: its contribution buDim 2 d is
     already the left argument of the outer `max`, so this equals the
     "odd-prime" formula in the open question.)

  2. Prove `dihedralLowerBound n d ≤ dihedralBUDim n d` for every n ≥ 1, using
     ONLY the parent framework's existing axioms (`dihedral_has_Z2`,
     `dihedral_has_rotation_prime`). This adds **0 new axioms** and subsumes the
     parent's case-by-case bounds as immediate corollaries.

  3. Prove that the conjectured exact equality holds **iff** a matching upper
     bound holds. This isolates the single deep topological input — the
     Fadell–Husseini upper bound from RO(D_n)-graded equivariant cohomology — as
     an explicit hypothesis rather than a new global axiom. That upper bound
     itself remains genuinely open (beyond current Mathlib).

  Honesty note: all topological content is inherited from the parent's abstract
  axiomatization of `buDim` / `dihedralBUDim`. The new mathematical content here
  is the uniform-in-n lower bound (a `Finset.sup` statement the parent did not
  formalize) and the precise reduction of tightness to one upper bound. No new
  axioms are introduced.

  References:
  - Fadell & Husseini, "An ideal-valued cohomological index theory" (1988)
  - tom Dieck, "Transformation Groups" (1987), §5.4, §7.1
  - Matoušek, "Using the Borsuk-Ulam Theorem" (2003), Ch. 6
-/

import Mathlib
import Proofs.BorsukUlamOQ02OQ01
import Proofs.BorsukUlamOQ02OQ01OQ03

namespace BorsukUlamDihedralTight

open BorsukUlamOQ02OQ01 BorsukUlamNonCyclic Nat

-- ═══════════════════════════════════════════════════════════════════════
-- The conjectured exact value, uniform in n
-- ═══════════════════════════════════════════════════════════════════════

/-- The prime-subgroup lower bound for the dihedral group `D_n`, uniform in `n`.

    `D_n` always contains a reflection `Z/2` (the `buDim 2 d` term) and contains
    `Z/p` for every prime divisor `p ∣ n` coming from the rotation subgroup
    `Z/n` (the `Finset.sup` term). This is the value conjectured to equal
    `dihedralBUDim n d`. -/
noncomputable def dihedralLowerBound (n d : ℕ) : ℕ :=
  max (buDim 2 d) (n.primeFactors.sup fun p => buDim p d)

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: THE GENERAL LOWER BOUND (0 new axioms)
-- ═══════════════════════════════════════════════════════════════════════

/-- **General dihedral lower bound.** For every `n ≥ 1`,
    `dihedralLowerBound n d ≤ dihedralBUDim n d`.

    Proof: the reflection axiom `dihedral_has_Z2` handles the `buDim 2 d` term;
    each prime divisor `p ∣ n` is handled by `dihedral_has_rotation_prime`, and
    `Finset.sup_le` combines them. Uses only the parent's axioms. -/
theorem dihedralLowerBound_le (n d : ℕ) (hn : 1 ≤ n) :
    dihedralLowerBound n d ≤ dihedralBUDim n d := by
  refine Nat.max_le.mpr ⟨dihedral_has_Z2 n d hn, ?_⟩
  refine Finset.sup_le ?_
  intro p hp
  exact dihedral_has_rotation_prime n d p
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- Every prime divisor of `n` contributes its cyclic bound to `dihedralBUDim`. -/
theorem dihedralBUDim_ge_of_prime_dvd (n d p : ℕ) (hn : 1 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ n) :
    buDim p d ≤ dihedralBUDim n d := by
  have hmem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩
  calc buDim p d ≤ n.primeFactors.sup (fun q => buDim q d) :=
        Finset.le_sup (f := fun q => buDim q d) hmem
    _ ≤ dihedralLowerBound n d := le_max_right _ _
    _ ≤ dihedralBUDim n d := dihedralLowerBound_le n d hn

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: TIGHTNESS REDUCES TO A SINGLE UPPER BOUND
-- ═══════════════════════════════════════════════════════════════════════

/-- **Tightness ⇔ matching upper bound.** The conjectured exact value
    `dihedralBUDim n d = dihedralLowerBound n d` holds precisely when the
    upper bound `dihedralBUDim n d ≤ dihedralLowerBound n d` holds.

    The lower bound is supplied unconditionally (Part I); the upper bound is the
    open Fadell–Husseini equivariant-cohomology input. This theorem pins down
    *exactly* what is missing to close the open question. -/
theorem dihedral_tight_iff_upper (n d : ℕ) (hn : 1 ≤ n) :
    dihedralBUDim n d = dihedralLowerBound n d ↔
      dihedralBUDim n d ≤ dihedralLowerBound n d :=
  ⟨fun h => h.le, fun hupper => le_antisymm hupper (dihedralLowerBound_le n d hn)⟩

/-- The exact dihedral BU dimension, conditional on the upper bound. -/
theorem dihedral_exact_of_upper (n d : ℕ) (hn : 1 ≤ n)
    (hupper : dihedralBUDim n d ≤ dihedralLowerBound n d) :
    dihedralBUDim n d = dihedralLowerBound n d :=
  le_antisymm hupper (dihedralLowerBound_le n d hn)

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: THE GENERAL BOUND SUBSUMES THE PARENT'S SPECIAL CASES
-- ═══════════════════════════════════════════════════════════════════════

/-- Recover the parent's `D_6 ⊇ Z/3` bound from the general Finset-sup bound. -/
theorem dihedralBUDim_six_ge_buDim_three (d : ℕ) :
    buDim 3 d ≤ dihedralBUDim 6 d :=
  dihedralBUDim_ge_of_prime_dvd 6 d 3 (by norm_num) (by norm_num) (by norm_num)

/-- Recover the parent's `D_6` Yang–Borsuk bound `2n-1 ≤ dihedralBUDim 6 (2n)`
    as a corollary of the uniform lower bound (via the `Z/3` rotation). -/
theorem dihedralBUDim_six_yang_borsuk (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ dihedralBUDim 6 (2 * n) := by
  have h := dihedralBUDim_six_ge_buDim_three (2 * n)
  rwa [buDim_prime 3 n (by norm_num) hn] at h

/-- For an odd prime `p`, `D_p` lower bound `max(buDim 2 d, buDim p d)` follows
    from the general bound (`p.primeFactors = {p}`, plus the reflection term). -/
theorem dihedralBUDim_odd_prime_ge (p d : ℕ) (hp : Nat.Prime p) :
    max (buDim 2 d) (buDim p d) ≤ dihedralBUDim p d :=
  Nat.max_le.mpr
    ⟨dihedral_has_Z2 p d hp.one_le,
     dihedralBUDim_ge_of_prime_dvd p d p hp.one_le hp (dvd_refl p)⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: SANITY CHECKS
-- ═══════════════════════════════════════════════════════════════════════

-- The reflection term alone always bounds the dihedral dimension.
example (n d : ℕ) (hn : 1 ≤ n) : buDim 2 d ≤ dihedralBUDim n d :=
  (le_max_left _ _).trans (dihedralLowerBound_le n d hn)

-- D_12 contains Z/3 (3 ∣ 12): general bound applies.
example (d : ℕ) : buDim 3 d ≤ dihedralBUDim 12 d :=
  dihedralBUDim_ge_of_prime_dvd 12 d 3 (by norm_num) (by norm_num) (by norm_num)

-- D_15 contains Z/5 (5 ∣ 15): general bound applies even with no factor of 2.
example (d : ℕ) : buDim 5 d ≤ dihedralBUDim 15 d :=
  dihedralBUDim_ge_of_prime_dvd 15 d 5 (by norm_num) (by norm_num) (by norm_num)

-- Tightness for D_6 in dimension 2n would give the exact value, given the
-- (open) upper bound; here we only assert the reduction compiles.
example (d : ℕ) (hupper : dihedralBUDim 6 d ≤ dihedralLowerBound 6 d) :
    dihedralBUDim 6 d = dihedralLowerBound 6 d :=
  dihedral_exact_of_upper 6 d (by norm_num) hupper

end BorsukUlamDihedralTight
