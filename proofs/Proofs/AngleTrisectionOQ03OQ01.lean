/-
  AngleTrisectionOQ03OQ01: Executable Constructibility Checker for Regular Polygons

  Extends the decidability results from AngleTrisectionOQ03 to a concrete executable
  program. The core `ngonConstructible : ℕ → Bool` function computes whether a regular
  n-gon is constructible by compass and straightedge, and its correctness is proved
  against the Gauss-Wantzel theorem.

  Key contributions:
  - `ngonConstructible : ℕ → Bool` — Bool-valued decision function (proved correct)
  - `constructibleNgons : ℕ → List ℕ` — enumerates all constructible polygons up to a bound
  - Verified enumeration: `constructibleNgons 100 = [3, 4, 5, 6, 8, ...]` (24 polygons)
  - Fermat prime checks: all five known Fermat primes yield constructible polygons
  - #eval commands demonstrate the program computing concrete answers

  Dependencies:
  - AngleTrisection.lean: IsConstructible, Wantzel's theorem
  - AngleTrisectionOQ02OQ03.lean: TotientIsPow2, IsConstructibleNgon, gauss_wantzel_theorem
  - AngleTrisectionOQ03.lean: decidable_totientIsPow2 instance
-/

import Mathlib
import Proofs.AngleTrisection
import Proofs.AngleTrisectionOQ02OQ03
import Proofs.AngleTrisectionOQ03

open AngleTrisection AngleTrisectionOQ02OQ03 AngleTrisectionOQ03

namespace AngleTrisectionOQ03OQ01

/-
## Part I: Computable Decision Functions

We define Bool-valued versions of the constructibility predicates.
Unlike Prop-valued predicates, these can be used in `#eval`, `if`-expressions,
and `List.filter`/`List.filterMap` operations.
-/

/-- Bool-valued decision function for n-gon constructibility.
    A regular n-gon is constructible iff φ(n) is a power of 2 (Gauss-Wantzel). -/
def ngonConstructible (n : ℕ) : Bool := decide (TotientIsPow2 n)

/-- ngonConstructible agrees with TotientIsPow2 for all n. -/
theorem ngonConstructible_totient (n : ℕ) :
    ngonConstructible n = true ↔ TotientIsPow2 n :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- ngonConstructible correctly decides constructibility for n ≥ 3 (via Gauss-Wantzel). -/
theorem ngonConstructible_correct (n : ℕ) (hn : 3 ≤ n) :
    ngonConstructible n = true ↔ IsConstructibleNgon n := by
  rw [ngonConstructible_totient]
  exact (gauss_wantzel_theorem n hn).symm

/-- Enumerate all constructible regular n-gons from 3 to bound (inclusive). -/
def constructibleNgons (bound : ℕ) : List ℕ :=
  (List.range (bound - 2)).filterMap fun i =>
    let n := i + 3
    if ngonConstructible n then some n else none

/-
## Part II: Program Evaluation

`#eval` runs the decision procedure on specific inputs,
demonstrating that this is an executable program, not just a proof.
-/

-- Basic polygons
#eval ngonConstructible 3    -- true:  equilateral triangle   φ(3) = 2 = 2¹
#eval ngonConstructible 4    -- true:  square                 φ(4) = 2 = 2¹
#eval ngonConstructible 5    -- true:  regular pentagon       φ(5) = 4 = 2²
#eval ngonConstructible 6    -- true:  regular hexagon        φ(6) = 2 = 2¹
#eval ngonConstructible 7    -- false: regular heptagon       φ(7) = 6  (not 2^k)
#eval ngonConstructible 8    -- true:  regular octagon        φ(8) = 4 = 2²
#eval ngonConstructible 9    -- false: regular nonagon        φ(9) = 6  (not 2^k)
#eval ngonConstructible 10   -- true:  regular decagon        φ(10) = 4 = 2²

-- Gauss's 17-gon (constructible, discovered 1796)
#eval ngonConstructible 17   -- true: φ(17) = 16 = 2⁴

-- 257-gon (Fermat prime, Richelot & Schwendenwein 1832)
#eval ngonConstructible 257  -- true: φ(257) = 256 = 2⁸

-- Enumerate constructible polygons in ranges
#eval constructibleNgons 50
-- Expected: [3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, 24, 30, 32, 34, 40, 48]

#eval constructibleNgons 100
-- Expected: [3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, 24, 30, 32, 34,
--            40, 48, 51, 60, 64, 68, 80, 85, 96]

/-
## Part III: Verified Enumeration

We use `native_decide` to formally verify the complete list of constructible
regular n-gons up to n = 100. This is a machine-checked correctness certificate
for the decision procedure.
-/

/-- The 24 constructible regular n-gons with 3 ≤ n ≤ 100.
    These are exactly n = 2^a × p₁ × ··· × pₖ where p₁,...,pₖ are distinct
    Fermat primes from {3, 5, 17} (the Fermat primes ≤ 100). -/
theorem constructible_upto_100 :
    constructibleNgons 100 =
    [3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, 24, 30, 32, 34,
     40, 48, 51, 60, 64, 68, 80, 85, 96] := by
  native_decide

/-- There are exactly 24 constructible regular n-gons with 3 ≤ n ≤ 100. -/
theorem count_constructible_upto_100 : (constructibleNgons 100).length = 24 := by
  simp [constructible_upto_100]

/-
## Part IV: Fermat Prime Verification

The five known Fermat primes 3, 5, 17, 257, 65537 all yield constructible polygons.
For each Fermat prime p = 2^(2^k) + 1, the totient φ(p) = p - 1 = 2^(2^k), a power of 2.
-/

theorem fermat3_constructible  : ngonConstructible 3     = true := by decide
theorem fermat5_constructible  : ngonConstructible 5     = true := by decide
theorem fermat17_constructible : ngonConstructible 17    = true := by decide
theorem fermat257_constructible : ngonConstructible 257  = true := by native_decide
theorem fermat65537_constructible : ngonConstructible 65537 = true := by native_decide

/-- All five known Fermat primes yield constructible regular polygons. -/
theorem all_known_fermat_primes_constructible :
    ngonConstructible 3 = true ∧ ngonConstructible 5 = true ∧
    ngonConstructible 17 = true ∧ ngonConstructible 257 = true ∧
    ngonConstructible 65537 = true :=
  ⟨fermat3_constructible, fermat5_constructible, fermat17_constructible,
   fermat257_constructible, fermat65537_constructible⟩

/-
## Part V: Structural Consequences

Simple deductions connecting the Bool function to the mathematical structure.
-/

/-- If a regular n-gon is constructible, then φ(n) is a power of 2. -/
theorem constructible_totient_pow2 (n : ℕ) (h : ngonConstructible n = true) :
    TotientIsPow2 n :=
  (ngonConstructible_totient n).mp h

/-- The constructible n-gons form a decidable subset of ℕ:
    for each n ≥ 3, we can compute whether the n-gon is constructible. -/
theorem ngon_constructibility_computable (n : ℕ) (hn : 3 ≤ n) :
    Decidable (IsConstructibleNgon n) :=
  decidable_of_iff (ngonConstructible n = true) (ngonConstructible_correct n hn)

end AngleTrisectionOQ03OQ01
