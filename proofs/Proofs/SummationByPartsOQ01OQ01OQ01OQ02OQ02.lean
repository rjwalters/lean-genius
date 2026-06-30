import Mathlib

/-
# The discrete Abel transform is biadditive: summation by parts over any ring or module

## What This Proves

The parent entry `SummationByPartsOQ01OQ01OQ01OQ02` proved the general discrete
**Abel summation by parts** over a *commutative* ring `R`: for `f, G : ℕ → R`,

    ∑_{k<n} f k · (G (k+1) − G k)
      = f n · G n − f 0 · G 0 − ∑_{k<n} (f (k+1) − f k) · G (k+1).        (A)

Its second open question asked whether (A) survives the loss of commutativity —
whether it extends "to a non-commutative ring or to a bimodule-valued pairing
`f k · (G (k+1) − G k)` where `f` and `G` take values in different modules,
provided the multiplication order is fixed."

This file answers that question affirmatively in the sharpest possible form.
The single fact the parent's `ring`-closed induction actually used is that the
product is **biadditive** — additive in each argument separately.  So we replace
the product by an *arbitrary* biadditive pairing

    p : A →+ B →+ M           (p (a₁+a₂) = p a₁ + p a₂,  p a (b₁+b₂) = p a b₁ + p a b₂)

between three abelian groups, and prove the master identity

    ∑_{k<n} p (f k) (G (k+1) − G k)
      = p (f n) (G n) − p (f 0) (G 0) − ∑_{k<n} p (f (k+1) − f k) (G (k+1)).   (A')

Commutativity, associativity, and even a ring structure on the *value* side are
all irrelevant: only the fixed left-to-right order `p (f ·) (G ·)` matters.

## Consequences

Three specialisations recover and strengthen the classical statements:

* `abel_summation_ring` — taking `p = AddMonoidHom.mul` gives (A) over **any**
  ring `R`, *dropping the commutativity hypothesis* the parent required.  The
  parent needed `CommRing` only because it discharged the algebra with `ring`;
  the identity itself never used it.
* `abel_summation_smul` — taking `p = `(scalar action) gives the **module-valued**
  Abel transform: `f : ℕ → R` a ring of scalars and `G : ℕ → M` valued in a left
  `R`-module, with pairing `f k • G k`.  This is the "bimodule-valued pairing"
  the open question asked for: `f` and `G` live in genuinely different objects.
* `abel_summation_swap_biadditive` — the order-swapped form, isolating the
  difference-weighted sum, exactly as in the parent.

## Method

Induction on `n`, identical in shape to the parent's.  The base case is `simp`.
The step peels the top term off both finite sums with `Finset.sum_range_succ` and
substitutes the induction hypothesis; the parent then closed with `ring`, but
here the leftover identity lives in the abelian group `M`, so we expand every
`p _ (b₁ − b₂)` and `p (a₁ − a₂) _` with `map_sub` (biadditivity) and close with
`abel`.  Replacing `ring` by `map_sub` + `abel` is precisely the move that frees
the identity from commutativity.

## Tags

summation-by-parts, abel-summation, abel-transform, biadditive, bilinear,
non-commutative-ring, module, finite-differences, discrete-integration-by-parts
-/

namespace SummationByPartsOQ01OQ01OQ01OQ02OQ02

open Finset

/-- **The biadditive discrete Abel transform (A′).**
For any biadditive pairing `p : A →+ B →+ M` between abelian groups and any
sequences `f : ℕ → A`, `G : ℕ → B`,

    ∑_{k<n} p (f k) (G (k+1) − G k)
      = p (f n) (G n) − p (f 0) (G 0) − ∑_{k<n} p (f (k+1) − f k) (G (k+1)).

No commutativity, associativity, or ring structure on the value group `M` is
used — only that `p` is additive in each slot separately and the order
`p (f ·) (G ·)` is fixed. -/
theorem abel_summation_biadditive
    {A B M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
    (p : A →+ B →+ M) (f : ℕ → A) (G : ℕ → B) (n : ℕ) :
    ∑ k ∈ range n, p (f k) (G (k + 1) - G k)
      = p (f n) (G n) - p (f 0) (G 0)
        - ∑ k ∈ range n, p (f (k + 1) - f k) (G (k + 1)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ (fun k => p (f k) (G (k + 1) - G k)), ih,
        Finset.sum_range_succ (fun k => p (f (k + 1) - f k) (G (k + 1)))]
      simp only [map_sub, AddMonoidHom.sub_apply]
      abel

/-- **Order-swapped form.** Rearranging (A′) isolates the difference-weighted
sum, exhibiting the symmetry between differencing `f` and differencing `G`:

    ∑_{k<n} p (f (k+1) − f k) (G (k+1))
      = p (f n) (G n) − p (f 0) (G 0) − ∑_{k<n} p (f k) (G (k+1) − G k). -/
theorem abel_summation_swap_biadditive
    {A B M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
    (p : A →+ B →+ M) (f : ℕ → A) (G : ℕ → B) (n : ℕ) :
    ∑ k ∈ range n, p (f (k + 1) - f k) (G (k + 1))
      = p (f n) (G n) - p (f 0) (G 0)
        - ∑ k ∈ range n, p (f k) (G (k + 1) - G k) := by
  have h := abel_summation_biadditive p f G n
  rw [h]; abel

/-- **Abel summation over an arbitrary ring (commutativity dropped).**
Specialising the biadditive pairing to ring multiplication `p = AddMonoidHom.mul`
gives the parent's identity (A) over **any** ring `R` — the parent's `CommRing`
hypothesis was an artefact of closing the algebra with `ring` and is not needed:

    ∑_{k<n} f k * (G (k+1) − G k) = f n * G n − f 0 * G 0 − ∑_{k<n} (f (k+1) − f k) * G (k+1).

The product order `f * G` is fixed throughout, which is all the identity requires. -/
theorem abel_summation_ring {R : Type*} [Ring R] (f G : ℕ → R) (n : ℕ) :
    ∑ k ∈ range n, f k * (G (k + 1) - G k)
      = f n * G n - f 0 * G 0
        - ∑ k ∈ range n, (f (k + 1) - f k) * G (k + 1) := by
  have h := abel_summation_biadditive (AddMonoidHom.mul (R := R)) f G n
  simpa only [AddMonoidHom.mul_apply] using h

/-- **Module-valued Abel summation (the bimodule pairing).**
Taking `p` to be the scalar action gives the discrete Abel transform where the
weight sequence `G` lives in a left `R`-module `M`, genuinely different from the
ring of multipliers `f`:

    ∑_{k<n} f k • (G (k+1) − G k) = f n • G n − f 0 • G 0 − ∑_{k<n} (f (k+1) − f k) • G (k+1).

This is the "different modules, fixed multiplication order" extension requested
by the parent's open question. -/
theorem abel_summation_smul {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (G : ℕ → M) (n : ℕ) :
    ∑ k ∈ range n, f k • (G (k + 1) - G k)
      = f n • G n - f 0 • G 0
        - ∑ k ∈ range n, (f (k + 1) - f k) • G (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ (fun k => f k • (G (k + 1) - G k)), ih,
        Finset.sum_range_succ (fun k => (f (k + 1) - f k) • G (k + 1))]
      simp only [smul_sub, sub_smul]
      abel

end SummationByPartsOQ01OQ01OQ01OQ02OQ02
