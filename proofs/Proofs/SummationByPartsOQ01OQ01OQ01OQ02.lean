import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-
# The general discrete Abel transform (summation by parts) over a commutative ring

## What This Proves

For **any** commutative ring `R`, **any** two sequences `f, G : ℕ → R`, and
**any** `n : ℕ`, with no side hypotheses whatsoever,

    ∑_{k<n} f k · (G (k+1) − G k)
      = f n · G n − f 0 · G 0 − ∑_{k<n} (f (k+1) − f k) · G (k+1).        (A)

This is the **general discrete Abel summation by parts**.  Writing
`Δh k = h (k+1) − h k` for the forward difference, identity (A) reads

    ∑ f · ΔG = (boundary term `f·G`) − ∑ Δf · G(·+1),

the exact discrete analogue of integration by parts `∫ f dG = fG − ∫ G df`.
Here `G` plays the role of an *antidifference* (a discrete antiderivative) of the
weight `g := ΔG`, so (A) transforms a sum weighted by `g = ΔG` into a sum
weighted by the forward difference `Δf` of the other factor, plus an explicit
boundary term.

## Why This Is the Right Object

The parent entry `SummationByPartsOQ01OQ01OQ01` proves the *geometric* special
case — the hypothesis-free recursion

    (r − 1) · ∑_{k<n} f k · rᵏ = f n · rⁿ − f 0 − ∑_{k<n} (f (k+1) − f k) · r^{k+1}.

That parent recorded as an open question whether *"an analogous hypothesis-free
recursion holds for a non-geometric base sequence … a general discrete Abel
transform `∑ f·g = boundary − ∑ Δf·G(·+1)` packaged for reuse over a commutative
ring."*  Identity (A) **is** that transform, and it is strictly more general: the
geometric recursion is the single instance `G k = rᵏ`.  Indeed with `G k = rᵏ`,

    G (k+1) − G k = r^{k+1} − rᵏ = rᵏ (r − 1),

so the left side of (A) becomes `(r − 1) · ∑ f k · rᵏ` and (A) collapses to the
parent identity verbatim (see `geom_weighted_recursion_of_abel`).  We also read
off the pure telescoping identity `∑ ΔG = G n − G 0` as the `f ≡ 1` instance
(`sum_diff_telescope`).

## Relationship to Mathlib

Mathlib has `Finset.sum_range_by_parts`, which is the same principle but stated
with `g` primitive and `G j := ∑_{i<j} g i` its partial sum, using awkward `n−1`
indexing.  Identity (A) is the cleaner *two-sequence* formulation requested by the
open question: an **arbitrary** antidifference `G` with clean `n` indexing and a
symmetric `f n G n − f 0 G 0` boundary.  It is proved here from scratch by a short
induction, so the entry is self-contained and does not route through the Mathlib
lemma.

## Method

Induction on `n`.  The base case `n = 0` is `simp`.  The step peels the top term
off both finite sums with `Finset.sum_range_succ`, substitutes the induction
hypothesis, and the remaining identity in the atoms `f m`, `f (m+1)`, `f 0`,
`G m`, `G (m+1)`, `G 0` is polynomial and closed by `ring` (the leftover sum
appears as a common opaque atom on both sides and cancels).

## Tags

summation-by-parts, abel-summation, abel-transform, finite-differences,
discrete-integration-by-parts, telescoping, commutative-ring
-/

namespace SummationByPartsOQ01OQ01OQ01OQ02

open Finset

/-- **The general discrete Abel transform (A).**
Over any commutative ring, for any sequences `f, G` and any `n`,
`∑_{k<n} f k · (G (k+1) − G k) = f n · G n − f 0 · G 0 − ∑_{k<n} (f (k+1) − f k) · G (k+1)`.
No hypotheses: both sides are polynomials in the sequence values. -/
theorem abel_summation {R : Type*} [CommRing R] (f G : ℕ → R) (n : ℕ) :
    ∑ k ∈ range n, f k * (G (k + 1) - G k)
      = f n * G n - f 0 * G 0
        - ∑ k ∈ range n, (f (k + 1) - f k) * G (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ (fun k => f k * (G (k + 1) - G k)), ih,
        Finset.sum_range_succ (fun k => (f (k + 1) - f k) * G (k + 1))]
      ring

/-- **Order-swapped form.** Rearranging (A) isolates the difference-weighted sum:
`∑_{k<n} (f (k+1) − f k) · G (k+1) = f n · G n − f 0 · G 0 − ∑_{k<n} f k · (G (k+1) − G k)`.
This is the same identity read as "move the boundary term across", exhibiting the
symmetry between differencing `f` and differencing `G`. -/
theorem abel_summation_swap {R : Type*} [CommRing R] (f G : ℕ → R) (n : ℕ) :
    ∑ k ∈ range n, (f (k + 1) - f k) * G (k + 1)
      = f n * G n - f 0 * G 0
        - ∑ k ∈ range n, f k * (G (k + 1) - G k) := by
  have h := abel_summation f G n
  linear_combination h

/-- **Telescoping (bottom of the ladder).** Taking `f ≡ 1` makes every forward
difference `Δf` vanish, so (A) collapses to the telescoping sum
`∑_{k<n} (G (k+1) − G k) = G n − G 0`. -/
theorem sum_diff_telescope {R : Type*} [CommRing R] (G : ℕ → R) (n : ℕ) :
    ∑ k ∈ range n, (G (k + 1) - G k) = G n - G 0 := by
  have h := abel_summation (fun _ => (1 : R)) G n
  simpa using h

/-- **Recovery of the parent's geometric recursion.** Specialising the
antidifference to the geometric weight `G k = rᵏ` gives `G (k+1) − G k = rᵏ (r−1)`,
so the general Abel transform (A) collapses to the parent entry's hypothesis-free
identity `(r − 1)·∑_{k<n} f k · rᵏ = f n · rⁿ − f 0 − ∑_{k<n} (f (k+1) − f k)·r^{k+1}`.
This exhibits the parent geometric recursion as the single instance `G = (· ↦ rᵏ)`
of the general transform. -/
theorem geom_weighted_recursion_of_abel {R : Type*} [CommRing R] (f : ℕ → R)
    (r : R) (n : ℕ) :
    (r - 1) * ∑ k ∈ range n, f k * r ^ k
      = f n * r ^ n - f 0 - ∑ k ∈ range n, (f (k + 1) - f k) * r ^ (k + 1) := by
  have h := abel_summation f (fun k => r ^ k) n
  simp only [pow_zero, mul_one] at h
  rw [Finset.mul_sum]
  have e : ∀ k, (r - 1) * (f k * r ^ k) = f k * (r ^ (k + 1) - r ^ k) := by
    intro k; rw [pow_succ]; ring
  simp_rw [e]
  rw [h]

end SummationByPartsOQ01OQ01OQ01OQ02
