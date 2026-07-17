/-
# The content (gcd) is a complete `SLₙ(ℤ)`-invariant of an integer vector

Research: bezout-identity-oq-01-oq-02-oq-02

The companion modules prove the *transitivity* (sufficiency) side of the
`SLₙ(ℤ)`-action on integer vectors: `BezoutIdentityOQ01OQ02OQ02` records that
`SLₙ(ℤ)` preserves **primitivity** (`isPrimitive_mulVec_iff`), and the descent
modules `…Descent` / `…Transitive` construct, for a primitive `v`, a matrix
`U ∈ SLₙ(ℤ)` with `U ·ᵥ v = e₀`, so *any two primitive vectors lie in one orbit*.

This file supplies the complementary **invariance** (necessity) side, the input a
complete-invariant statement of the orbit structure needs: the entire **content**
of a vector — the set of integers dividing every coordinate, i.e. the `gcd` of the
entries — is unchanged by the `SLₙ(ℤ)`-action. Primitivity (`gcd = 1`) is only the
extreme case; the same argument preserves *every* common divisor at once.

## What is proved (0 axioms, 0 sorries)

* `dvd_mulVec` — the atomic fact: **any** integer matrix `M` sends a common divisor
  of `v` to a common divisor of `M ·ᵥ v`, since each coordinate of `M ·ᵥ v` is an
  integer combination `∑ⱼ Mᵢⱼ vⱼ` of the entries of `v`.
* `common_dvd_mulVec_iff` — for `A ∈ SLₙ(ℤ)` the common divisors of `A ·ᵥ v` are
  *exactly* those of `v` (both directions, the reverse via `A⁻¹`). This is the
  content-level strengthening of `isPrimitive_mulVec_iff`, which is its `d`-a-unit
  special case.
* `sameOrbit_common_dvd_eq` — two vectors in the same `SLₙ(ℤ)`-orbit have the
  identical set of common divisors: the content is an orbit invariant.
* `IsPrimitive.common_dvd_isUnit` — the primitive case: a primitive vector has only
  units as common divisors (`gcd = 1`), recovering primitivity as *trivial content*
  and matching the invariance above with the transitivity of the companion modules.

Combined with the companion transitivity results, the content is therefore a
*complete* invariant of the `SLₙ(ℤ)`-orbit on the primitive locus.

All results are fully machine-checked with no new axioms, on top of Mathlib and the
primitive-vector layer `BezoutIdentityOQ01OQ02OQ02`.
-/
import Mathlib
import Proofs.BezoutIdentityOQ01OQ02OQ02

namespace BezoutPrimitive

open Matrix

variable {n : ℕ}

/-- **A matrix carries common divisors forward.** If an integer `d` divides every
coordinate of `v`, it divides every coordinate of `M ·ᵥ v` for *any* integer matrix
`M`: the `i`-th coordinate `∑ⱼ Mᵢⱼ vⱼ` is an integer combination of the entries of
`v`. No unimodularity is needed for this direction. -/
theorem dvd_mulVec (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) (d : ℤ)
    (h : ∀ i, d ∣ v i) : ∀ i, d ∣ (M *ᵥ v) i := by
  intro i
  rw [mulVec, dotProduct]
  exact Finset.dvd_sum (fun j _ => Dvd.dvd.mul_left (h j) (M i j))

/-- **`SLₙ(ℤ)` preserves the content.** For `A ∈ SLₙ(ℤ)`, an integer `d` divides
every coordinate of `A ·ᵥ v` iff it divides every coordinate of `v`: the two vectors
have the same set of common divisors, hence the same `gcd`. The forward direction is
`dvd_mulVec` applied to `A⁻¹` (using `A⁻¹ · (A · v) = v`); the reverse is
`dvd_mulVec` applied to `A`. This is the content-level generalisation of
`isPrimitive_mulVec_iff` — that lemma is the special case where the common divisors
are forced to be units. -/
theorem common_dvd_mulVec_iff (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (v : Fin n → ℤ) (d : ℤ) :
    (∀ i, d ∣ ((A : Matrix (Fin n) (Fin n) ℤ) *ᵥ v) i) ↔ (∀ i, d ∣ v i) := by
  constructor
  · intro h
    have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) *ᵥ ((A : Matrix (Fin n) (Fin n) ℤ) *ᵥ v) = v := by
      rw [mulVec_mulVec]
      have hAA : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) * (A : Matrix (Fin n) (Fin n) ℤ) = 1 := by
        simp [adjugate_mul]
      rw [hAA, one_mulVec]
    rw [← hinv]
    exact dvd_mulVec _ _ d h
  · exact dvd_mulVec _ v d

/-- **The content is an orbit invariant.** If `v` and `w` lie in the same
`SLₙ(ℤ)`-orbit — `A ·ᵥ v = w` for some `A ∈ SLₙ(ℤ)` — then they have the *identical*
set of common divisors, so the same `gcd`. Together with the companion transitivity
(any two primitive vectors share an orbit), the content is a complete invariant of
the action. -/
theorem sameOrbit_common_dvd_eq {v w : Fin n → ℤ}
    (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (hA : (A : Matrix (Fin n) (Fin n) ℤ) *ᵥ v = w) (d : ℤ) :
    (∀ i, d ∣ v i) ↔ (∀ i, d ∣ w i) := by
  rw [← hA]; exact (common_dvd_mulVec_iff A v d).symm

/-- **Primitive means trivial content.** A primitive vector `v` (one with an integer
dual `w`, `w ⬝ᵥ v = 1`) has only units as common divisors: if `d ∣ vᵢ` for every `i`
then `d ∣ w ⬝ᵥ v = 1`, so `d` is a unit. This is the `gcd = 1` reading of
primitivity; combined with `common_dvd_mulVec_iff` it re-exhibits the
primitivity-preservation `isPrimitive_mulVec_iff` as the content-invariance
specialised to the trivial content. -/
theorem IsPrimitive.common_dvd_isUnit {v : Fin n → ℤ} (hv : IsPrimitive v)
    {d : ℤ} (hd : ∀ i, d ∣ v i) : IsUnit d := by
  obtain ⟨w, hw⟩ := hv
  have : d ∣ (1 : ℤ) := by
    rw [← hw, dotProduct]
    exact Finset.dvd_sum (fun j _ => Dvd.dvd.mul_left (hd j) (w j))
  exact isUnit_of_dvd_one this

end BezoutPrimitive
