import Mathlib
import Proofs.BurnsideCountingOQ03
import Proofs.BurnsideCountingOQ05

/-
# Burnside Assembly: the Dihedral Bracelet Count for Odd Cycles

`BurnsideCountingOQ03` counts the colorings of an `n`-cycle fixed by a **rotation**
(`∑_{r} k^{gcd(r,n)}`, the Pólya sum, with divisor form `∑_{d∣n} φ(n/d) k^d`), and
`BurnsideCountingOQ05` counts those fixed by a **reflection** of an odd cycle
(`k^{(n+1)/2}` per reflection).  This file *assembles* the two pieces into the
fixed-point total for the full **dihedral** group `D_n` (`n = 2m+1`) and reads off the
number of inequivalent **bracelets** (dihedral necklaces) as the Burnside average
`(rotation total + reflection total) / |D_n|`, `|D_n| = 2n`.

For an odd cycle all `n` reflections are conjugate (each through one vertex) and fix
`k^{m+1}` colorings, so the reflection total is `n · k^{m+1}`.  Hence

  dihedral total  =  ∑_{r<n} k^{gcd(r,n)}  +  n · k^{m+1}
                  =  ∑_{d∣n} φ(n/d) k^d   +  n · k^{m+1}

and the bracelet count is this divided by `2n`.

## Main results

General (any odd `n = 2m+1`, any `k`):
* `reflectionTotal_eq_card` — the reflection total is `n` copies of the OQ05 count.
* `dihedralTotal_divisor_form` — the assembled total in divisor-sum closed form (via OQ03).

Worked odd cases with fully closed forms in `k` (the polynomial `totals` by `ring`,
the integral bracelet counts by an exact divisibility):
* `dihedralTotal_three` / `bracelet_three` — `n = 3`: total `k(k+1)(k+2)`, bracelet count
  the tetrahedral number `C(k+2,3)`.
* `dihedralTotal_five` / `bracelet_five` — `n = 5`: total `k(k²+1)(k²+4)`, bracelet count
  `k(k²+1)(k²+4)/10`.
* numeric checks `bracelet_three_two = 4`, `bracelet_five_two = 8`, `bracelet_three_three = 10`.

Everything is machine-checked with `ring`, `omega`, `decide`, and the two sibling
identities — no axioms, no `native_decide`, no `sorry`.  The remaining step of
identifying `braceletCount` with the literal orbit count of `DihedralGroup n` acting on
colorings (Mathlib's `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) is the
natural next child.
-/

namespace BurnsideCountingOQ05OQ02

open Finset

/-- Total colorings fixed across all `n` rotations of an `n`-cycle (the Pólya sum). -/
def rotationTotal (n k : ℕ) : ℕ := ∑ r : Fin n, k ^ Nat.gcd r.val n

/-- Total colorings fixed across all `2m+1` reflections of an odd `(2m+1)`-cycle.  Each of
the `2m+1` reflections fixes `k^(m+1)` colorings (`BurnsideCountingOQ05`). -/
def reflectionTotal (m k : ℕ) : ℕ := (2 * m + 1) * k ^ (m + 1)

/-- The Burnside fixed-point total for the dihedral group `D_n` (`n = 2m+1`) acting on
`k`-colorings of the cycle: rotations plus reflections.  Dividing by `|D_n| = 2(2m+1)`
gives the bracelet count. -/
def dihedralTotal (m k : ℕ) : ℕ := rotationTotal (2 * m + 1) k + reflectionTotal m k

/-- The number of inequivalent bracelets: the Burnside average over `|D_n| = 2(2m+1)`. -/
def braceletCount (m k : ℕ) : ℕ := dihedralTotal m k / (2 * (2 * m + 1))

/-- Provenance: the reflection total is exactly `2m+1` copies of the OQ05 reflection count
`k^(m+1)` (`= Fintype.card` of the reflection-invariant colorings). -/
theorem reflectionTotal_eq_card (m k : ℕ) :
    reflectionTotal m k =
      (2 * m + 1) * Fintype.card {c : ZMod (2 * m + 1) → Fin k // ∀ i, c (-i) = c i} := by
  rw [reflectionTotal, BurnsideCountingOQ05.card_reflectionInvariant]

/-- The assembled dihedral total, definitionally rotations plus reflections. -/
theorem dihedralTotal_eq (m k : ℕ) :
    dihedralTotal m k = rotationTotal (2 * m + 1) k + (2 * m + 1) * k ^ (m + 1) := rfl

/-- **Assembled dihedral fixed-point total, divisor-sum closed form.**  Combining the OQ03
Pólya divisor identity for the rotations with the OQ05 reflection count gives, for every
odd `n = 2m+1` and every `k`,
`dihedralTotal = ∑_{d∣n} φ(n/d) k^d + n · k^{m+1}`. -/
theorem dihedralTotal_divisor_form (m k : ℕ) :
    dihedralTotal m k =
      (∑ d ∈ Nat.divisors (2 * m + 1), Nat.totient ((2 * m + 1) / d) * k ^ d)
        + (2 * m + 1) * k ^ (m + 1) := by
  rw [dihedralTotal_eq]
  unfold rotationTotal
  rw [BurnsideCountingOQ03.polya_sum_identity (2 * m + 1) k (by omega)]

/-! ### Worked odd case `n = 3` (`m = 1`). -/

/-- Rotation total for the triangle: `k^3 + 2k` (identity fixes `k^3`, the two nontrivial
rotations fix `k` each). -/
theorem rotationTotal_three (k : ℕ) : rotationTotal 3 k = k ^ 3 + 2 * k := by
  simp only [rotationTotal, Fin.sum_univ_three]
  norm_num [show Nat.gcd (0 : Fin 3).val 3 = 3 from rfl,
    show Nat.gcd (1 : Fin 3).val 3 = 1 from rfl,
    show Nat.gcd (2 : Fin 3).val 3 = 1 from rfl]
  ring

/-- Assembled dihedral total for the triangle: `k(k+1)(k+2)`. -/
theorem dihedralTotal_three (k : ℕ) : dihedralTotal 1 k = k * (k + 1) * (k + 2) := by
  rw [dihedralTotal_eq, rotationTotal_three]
  ring

/-- `6 = |D₃|` divides the triangle total (three consecutive integers), so the bracelet
count is an integer. -/
theorem bracelet_three_dvd (k : ℕ) : 6 ∣ dihedralTotal 1 k := by
  rw [dihedralTotal_three]
  have h6 : ∀ r : ZMod 6, r * (r + 1) * (r + 2) = 0 := by decide
  have : ((k * (k + 1) * (k + 2) : ℕ) : ZMod 6) = 0 := by
    push_cast; exact h6 (k : ZMod 6)
  exact (ZMod.natCast_eq_zero_iff _ 6).mp this

/-- **Bracelet count for the triangle.**  `6 · braceletCount = k(k+1)(k+2)`; the count is
`k(k+1)(k+2)/6`, the tetrahedral number `C(k+2,3)`. -/
theorem bracelet_three (k : ℕ) : 6 * braceletCount 1 k = dihedralTotal 1 k := by
  have hd : (2 * (2 * 1 + 1)) = 6 := by norm_num
  unfold braceletCount
  rw [hd]
  exact Nat.mul_div_cancel' (bracelet_three_dvd k)

/-! ### Worked odd case `n = 5` (`m = 2`). -/

/-- Rotation total for the pentagon: `k^5 + 4k`. -/
theorem rotationTotal_five (k : ℕ) : rotationTotal 5 k = k ^ 5 + 4 * k := by
  simp only [rotationTotal, Fin.sum_univ_five]
  norm_num [show Nat.gcd (0 : Fin 5).val 5 = 5 from rfl,
    show Nat.gcd (1 : Fin 5).val 5 = 1 from rfl,
    show Nat.gcd (2 : Fin 5).val 5 = 1 from rfl,
    show Nat.gcd (3 : Fin 5).val 5 = 1 from rfl,
    show Nat.gcd (4 : Fin 5).val 5 = 1 from rfl]
  ring

/-- Assembled dihedral total for the pentagon: `k(k²+1)(k²+4) = k^5 + 5k^3 + 4k`. -/
theorem dihedralTotal_five (k : ℕ) :
    dihedralTotal 2 k = k * (k ^ 2 + 1) * (k ^ 2 + 4) := by
  rw [dihedralTotal_eq, rotationTotal_five]
  ring

/-- `10` divides the pentagon total, so the bracelet count is an integer. -/
theorem bracelet_five_dvd (k : ℕ) : 10 ∣ dihedralTotal 2 k := by
  rw [dihedralTotal_five]
  -- k(k²+1)(k²+4) ≡ 0 (mod 10) for all k, checked on residues mod 10.
  have h10 : ∀ r : ZMod 10, r * (r ^ 2 + 1) * (r ^ 2 + 4) = 0 := by decide
  have : ((k * (k ^ 2 + 1) * (k ^ 2 + 4) : ℕ) : ZMod 10) = 0 := by
    push_cast
    exact h10 (k : ZMod 10)
  exact (ZMod.natCast_eq_zero_iff _ 10).mp this

/-- **Bracelet count for the pentagon.**  `10 · braceletCount = k(k²+1)(k²+4)`. -/
theorem bracelet_five (k : ℕ) : 10 * braceletCount 2 k = dihedralTotal 2 k := by
  have hd : (2 * (2 * 2 + 1)) = 10 := by norm_num
  unfold braceletCount
  rw [hd]
  exact Nat.mul_div_cancel' (bracelet_five_dvd k)

/-! ### Numeric sanity checks (bracelet counts). -/

/-- `4` binary bracelets of length `3`. -/
theorem bracelet_three_two : braceletCount 1 2 = 4 := by decide

/-- `10` ternary bracelets of length `3`. -/
theorem bracelet_three_three : braceletCount 1 3 = 10 := by decide

/-- `8` binary bracelets of length `5`. -/
theorem bracelet_five_two : braceletCount 2 2 = 8 := by decide

end BurnsideCountingOQ05OQ02
