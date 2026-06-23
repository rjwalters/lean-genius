import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-
# Finite Taylor–Abel expansion via iterated discrete integration by parts

## What This Proves

Over **any** commutative ring `R`, fix a sequence `f : ℕ → R` and a *tower of
antidifferences* `G : ℕ → ℕ → R` linked by the single hypothesis

    G (d+1) (k+1) − G (d+1) k = G d (k+1)        for all `d k`.        (hG)

Writing `Δh k = h (k+1) − h k` for the forward difference and `Δ^[d]` for its
`d`-fold iterate, the main theorem `discrete_taylor_abel` is the closed
`D`-fold identity

    ∑_{k<n} f k · G 0 (k+1)
      = ∑_{d<D} (−1)^d · ( Δ^[d] f n · G (d+1) n − Δ^[d] f 0 · G (d+1) 0 )
        + (−1)^D · ∑_{k<n} Δ^[D] f k · G D (k+1).                      (T)

This is the discrete mirror of repeated integration by parts building a
Taylor-with-remainder series

    ∫ f dG = ∑_{d<D} (−1)^d [ f^{(d)} G_{(d+1)} ] ± ∫ f^{(D)} G_{(D)} :

each layer trades one forward difference off `f` onto the next antidifference of
`G`, paying an alternating boundary term `[Δ^[d] f · G (d+1)]_0^n`, and after `D`
layers a remainder sum `∑ Δ^[D] f · G D (·+1)` is left.

## Why This Is the Right Object

The parent entry `SummationByPartsOQ01OQ01OQ01OQ02` proves the **single-step**
discrete Abel transform over a commutative ring,

    ∑_{k<n} a k · (B (k+1) − B k)
      = a n · B n − a 0 · B 0 − ∑_{k<n} (a (k+1) − a k) · B (k+1).      (A)

It recorded as an open question whether the transform could be *iterated* into a
finite discrete Taylor–Abel series.  Identity (T) is exactly that iteration:
`discrete_taylor_abel` is proved by induction on the depth `D`, with each step
applying (A) once (lemma `step`) to peel the top remainder, increment the
alternating sign, and append one boundary term.  The hypothesis (hG) is the
precise antidifference relation under which the boundary terms land cleanly at
the *fixed* endpoints `0` and `n` (no shift accumulation) and the remainder
reproduces the same shape one level up — the property that makes the recursion
`R d = bd d − R (d+1)` close.

The base case `D = 0` of (T) is the trivial identity (empty boundary sum, the
remainder *is* the left-hand side), and the `D = 1` case is the parent transform
(A) verbatim.  The corollary `discrete_taylor_abel_of_fdiff_eq_zero` records the
payoff: when `Δ^[D] f = 0` (a discrete polynomial of degree `< D`) the remainder
vanishes and the expansion **terminates** as a finite alternating sum of boundary
terms — the discrete finite Taylor formula.

## Method

`fdiff` is the forward difference; `fdiff^[d]` its iterate via `Function.iterate`.
The single-step recursion `step` rewrites `G d (k+1)` as the difference
`G (d+1) (k+1) − G (d+1) k` using (hG), applies the parent transform (A) with
`a := Δ^[d] f`, `B := G (d+1)`, and recognises the resulting difference of
`Δ^[d] f` as `Δ^[d+1] f` (`Function.iterate_succ_apply'`).  The main induction
on `D` then telescopes the alternating sum with `Finset.sum_range_succ`,
`pow_succ`, and `ring`.

## Tags

summation-by-parts, abel-summation, abel-transform, discrete-taylor,
finite-differences, iterated-integration-by-parts, telescoping, commutative-ring
-/

namespace SummationByPartsOQ01OQ01OQ01OQ02OQ01

open Finset

variable {R : Type*} [CommRing R]

/-- The forward difference operator `Δh k = h (k+1) − h k`. -/
def fdiff (h : ℕ → R) : ℕ → R := fun k => h (k + 1) - h k

@[simp] lemma fdiff_apply (h : ℕ → R) (k : ℕ) : fdiff h k = h (k + 1) - h k := rfl

/-- One unfolding of the iterated forward difference:
`Δ^[d+1] = Δ ∘ Δ^[d]`. -/
lemma fdiff_iterate_succ (f : ℕ → R) (d : ℕ) :
    fdiff^[d + 1] f = fdiff (fdiff^[d] f) :=
  Function.iterate_succ_apply' fdiff d f

/-- **The single-step discrete Abel transform (A)** — the parent entry's
identity, reproved here from scratch so this file is self-contained.
Over any commutative ring, for any sequences `a, B` and any `n`,
`∑_{k<n} a k · (B (k+1) − B k) = a n · B n − a 0 · B 0 − ∑_{k<n} (a (k+1) − a k) · B (k+1)`. -/
theorem abel_summation (a B : ℕ → R) (n : ℕ) :
    ∑ k ∈ range n, a k * (B (k + 1) - B k)
      = a n * B n - a 0 * B 0
        - ∑ k ∈ range n, (a (k + 1) - a k) * B (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ (fun k => a k * (B (k + 1) - B k)), ih,
        Finset.sum_range_succ (fun k => (a (k + 1) - a k) * B (k + 1))]
      ring

/-- **One layer of the iteration.** Under the antidifference hypothesis (hG),
applying the single-step transform (A) at depth `d` peels one boundary term and
drops the remainder from depth `d` to depth `d+1`:
`∑_{k<n} Δ^[d] f k · G d (k+1) = Δ^[d] f n · G (d+1) n − Δ^[d] f 0 · G (d+1) 0 − ∑_{k<n} Δ^[d+1] f k · G (d+1) (k+1)`. -/
theorem step (f : ℕ → R) (G : ℕ → ℕ → R)
    (hG : ∀ d k, G (d + 1) (k + 1) - G (d + 1) k = G d (k + 1)) (n d : ℕ) :
    ∑ k ∈ range n, (fdiff^[d] f) k * G d (k + 1)
      = (fdiff^[d] f) n * G (d + 1) n - (fdiff^[d] f) 0 * G (d + 1) 0
        - ∑ k ∈ range n, (fdiff^[d + 1] f) k * G (d + 1) (k + 1) := by
  have key := abel_summation (fdiff^[d] f) (G (d + 1)) n
  have hL : ∑ k ∈ range n, (fdiff^[d] f) k * G d (k + 1)
      = ∑ k ∈ range n, (fdiff^[d] f) k * (G (d + 1) (k + 1) - G (d + 1) k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hG d k]
  have hR : ∑ k ∈ range n, (fdiff^[d + 1] f) k * G (d + 1) (k + 1)
      = ∑ k ∈ range n, ((fdiff^[d] f) (k + 1) - (fdiff^[d] f) k) * G (d + 1) (k + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [fdiff_iterate_succ, fdiff_apply]
  rw [hL, hR]
  exact key

/-- **Finite Taylor–Abel expansion (T).** Iterating the single-step transform
`D` times along the antidifference tower `G` (linked by `hG`) gives an
alternating sum of boundary terms plus a remainder sum:
`∑_{k<n} f k · G 0 (k+1) = ∑_{d<D} (−1)^d (Δ^[d] f n · G (d+1) n − Δ^[d] f 0 · G (d+1) 0) + (−1)^D ∑_{k<n} Δ^[D] f k · G D (k+1)`. -/
theorem discrete_taylor_abel (f : ℕ → R) (G : ℕ → ℕ → R)
    (hG : ∀ d k, G (d + 1) (k + 1) - G (d + 1) k = G d (k + 1)) (n D : ℕ) :
    ∑ k ∈ range n, f k * G 0 (k + 1)
      = (∑ d ∈ range D, (-1) ^ d *
            ((fdiff^[d] f) n * G (d + 1) n - (fdiff^[d] f) 0 * G (d + 1) 0))
        + (-1) ^ D * ∑ k ∈ range n, (fdiff^[D] f) k * G D (k + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [ih, Finset.sum_range_succ, step f G hG n D, pow_succ]
      ring

/-- **The expansion terminates for discrete polynomials.** If the `D`-th forward
difference of `f` vanishes (i.e. `f` is a discrete polynomial of degree `< D`),
the remainder term in `discrete_taylor_abel` drops out and the Taylor–Abel
expansion is a finite alternating sum of boundary terms. -/
theorem discrete_taylor_abel_of_fdiff_eq_zero (f : ℕ → R) (G : ℕ → ℕ → R)
    (hG : ∀ d k, G (d + 1) (k + 1) - G (d + 1) k = G d (k + 1)) (n D : ℕ)
    (hf : fdiff^[D] f = 0) :
    ∑ k ∈ range n, f k * G 0 (k + 1)
      = ∑ d ∈ range D, (-1) ^ d *
          ((fdiff^[d] f) n * G (d + 1) n - (fdiff^[d] f) 0 * G (d + 1) 0) := by
  rw [discrete_taylor_abel f G hG n D, hf]
  simp

/-- **Specialisation to `D = 1`: recovery of the single-step transform.**
The depth-one Taylor–Abel expansion is exactly the parent's Abel transform (A)
applied to the first antidifference `G 1`. -/
theorem discrete_taylor_abel_one (f : ℕ → R) (G : ℕ → ℕ → R)
    (hG : ∀ d k, G (d + 1) (k + 1) - G (d + 1) k = G d (k + 1)) (n : ℕ) :
    ∑ k ∈ range n, f k * G 0 (k + 1)
      = f n * G 1 n - f 0 * G 1 0
        - ∑ k ∈ range n, (f (k + 1) - f k) * G 1 (k + 1) := by
  have h := discrete_taylor_abel f G hG n 1
  simp only [Finset.sum_range_one, pow_zero, pow_one, one_mul, neg_one_mul,
    Function.iterate_zero, Function.iterate_one, id_eq, zero_add, fdiff_apply] at h
  rw [h]
  ring

end SummationByPartsOQ01OQ01OQ01OQ02OQ01
