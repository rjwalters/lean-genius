/-
Hilbert's 10th Problem over ℚ — OQ-01-OQ-02: the affine stabilizer of ℤ ⊂ ℚ.

Parent: `Proofs.Hilbert10OQ01OQ02` (namespace `Hilbert10Rationals`).  That file
develops the affine action `affinePullback a b S = { q | a·q + b ∈ S }` of the
affine group of ℚ on subsets `S ⊆ ℚ`, proving it is a group action and a
Boolean-algebra homomorphism, and that each of the four definability classes
(Σ₁/Π₁/Σ₂/Π₂) is an *invariant subset* of the action.

Those results are about the definability **class** being preserved.  This file
records the complementary fact about the specific set `IntSubset = ℤ` itself:
which affine reparametrizations fix `ℤ` *setwise* (not just its class).  The
answer is the integer **infinite dihedral group** `ℤ ⋊ {±1}` sitting inside the
affine group of ℚ:

  * `affinePullback_one_intCast_fixesInt`  — integer translations `q ↦ q + n`
                                             (`n : ℤ`) fix `ℤ`;
  * `affinePullback_negOne_intCast_fixesInt` — integer glide-reflections
                                             `q ↦ -q + n` (`n : ℤ`) fix `ℤ`;
  * `affinePullback_neg_fixesInt`          — the reflection `q ↦ -q` fixes `ℤ`;
  * `affinePullback_two_ne_int`            — **dilation `q ↦ 2q` does NOT fix `ℤ`**
                                             (`½` escapes), so the stabilizer is a
                                             proper subgroup — the linear part must
                                             be a unit of `ℤ`, i.e. `±1`.

These are the exact symmetries of the lattice `ℤ` inside `ℚ`.  They explain,
concretely, why the general affine-invariance theorems of the parent
(`int_diophantine_iff_affinePullback_diophantine` etc.) never simplify the OPEN
Σ₁ question: only the `±1`-scaling integer-translation subgroup actually returns
`ℤ` to itself; every other affine map moves `ℤ` to a genuinely different (if
equidefinable) subset such as `½ℤ`.

All results are `0`-sorry and do not invoke the parent's `koenigsmann_2016`
axiom.  (`affinePullback` and `IntSubset` are pure definitions.)
-/

import Mathlib
import Proofs.Hilbert10OQ01OQ02

namespace Hilbert10OQ01OQ02IntStabilizer

open Hilbert10Rationals

/-- **Integer translations fix `ℤ`.**  For `n : ℤ`, pulling `IntSubset` back
    along `q ↦ q + n` returns `IntSubset`: `q + n ∈ ℤ ⟺ q ∈ ℤ` because `n ∈ ℤ`. -/
theorem affinePullback_one_intCast_fixesInt (n : ℤ) :
    affinePullback 1 (n : ℚ) IntSubset = IntSubset := by
  funext q
  simp only [affinePullback, IntSubset, one_mul]
  apply propext
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z - n, by push_cast; linarith⟩
  · rintro ⟨z, hz⟩
    exact ⟨z + n, by push_cast; linarith⟩

/-- **Integer glide-reflections fix `ℤ`.**  For `n : ℤ`, pulling `IntSubset` back
    along `q ↦ -q + n` returns `IntSubset`: `-q + n ∈ ℤ ⟺ q ∈ ℤ`. -/
theorem affinePullback_negOne_intCast_fixesInt (n : ℤ) :
    affinePullback (-1) (n : ℚ) IntSubset = IntSubset := by
  funext q
  simp only [affinePullback, IntSubset, neg_one_mul]
  apply propext
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨n - z, by push_cast; linarith⟩
  · rintro ⟨z, hz⟩
    exact ⟨n - z, by push_cast; linarith⟩

/-- **The reflection `q ↦ -q` fixes `ℤ`.**  The `n = 0` case of
    `affinePullback_negOne_intCast_fixesInt`: `ℤ` is symmetric about the origin. -/
theorem affinePullback_neg_fixesInt :
    affinePullback (-1) 0 IntSubset = IntSubset := by
  simpa using affinePullback_negOne_intCast_fixesInt 0

/-- **Dilation `q ↦ 2q` does NOT fix `ℤ`.**  The point `½` satisfies `2·½ = 1 ∈ ℤ`
    but `½ ∉ ℤ`, so `affinePullback 2 0 IntSubset` strictly contains `IntSubset`
    (it is `½ℤ`).  Hence the affine stabilizer of `ℤ` is a *proper* subgroup: the
    linear coefficient must be a unit of `ℤ` (`±1`), never `2`. -/
theorem affinePullback_two_ne_int :
    affinePullback 2 0 IntSubset ≠ IntSubset := by
  intro h
  have hmem : affinePullback 2 0 IntSubset (1 / 2) := by
    simp only [affinePullback, IntSubset]
    exact ⟨1, by norm_num⟩
  rw [h] at hmem
  obtain ⟨z, hz⟩ := hmem
  have h2 : (2 * z : ℤ) = 1 := by
    have hq : ((2 * z : ℤ) : ℚ) = 1 := by push_cast; linarith
    exact_mod_cast hq
  omega

end Hilbert10OQ01OQ02IntStabilizer
