import Mathlib

/-
# The iterated biadditive Abel transform: a finite Taylor–Abel expansion

## What This Proves

The parent entry `SummationByPartsOQ01OQ01OQ01OQ02OQ02` proved the **single-step
biadditive Abel transform**: for a biadditive pairing `p : A →+ B →+ M` between
abelian groups and sequences `f : ℕ → A`, `G : ℕ → B`,

    ∑_{k<n} p (f k) (G (k+1) − G k)
      = p (f n) (G n) − p (f 0) (G 0) − ∑_{k<n} p (f (k+1) − f k) (G (k+1)).   (A')

Its first open question asked whether (A′) **iterates against a tower of
antidifferences to a finite Taylor–Abel expansion** in the module-valued setting,
with `Δᵈf` the iterated forward difference and the remainder a biadditive pairing
of `Δᴰf` against the top antidifference.

This file answers that affirmatively. Running summation by parts `D` times turns
a single biadditive sum into a finite alternating sum of boundary terms — one per
order `0 ≤ j < D` — plus a single remainder pairing the `D`-th forward difference
of `f` against the `D`-th antidifference of the weight tower:

    ∑_{k<n} p (f k) (H₀(k+1))
      = ∑_{j<D} (−1)ʲ ( p (Δʲf n) (H_{j+1} n) − p (Δʲf 0) (H_{j+1} 0) )
        + (−1)ᴰ ∑_{k<n} p (Δᴰf k) (H_D(k+1)).                                   (T)

This is the discrete, module-valued analogue of the Taylor formula obtained from
**iterated integration by parts**: the finite sum of boundary contributions plays
the role of the Taylor polynomial, and the last sum is the integral remainder.

## The tower hypothesis

The forward-difference operator `Δf k = f(k+1) − f k` is recorded symmetrically on
both sides of the pairing.  We carry a **difference tower** `F` for the left
argument and an **antidifference tower** `H` for the right argument:

* `F (j+1) k = F j (k+1) − F j k`           — `F j = Δʲ(F 0)`, the iterated forward difference;
* `H (j+1) (k+1) − H (j+1) k = H j (k+1)`    — `H (j+1)` is an antidifference of the *shifted* weight `k ↦ H j (k+1)`.

The shift in the antidifference relation is exactly what makes the recursion
**uniform**: each Abel step produces a remainder of the form `∑ p (· ) (H·(k+1))`,
identical in shape to the term it consumed, so the transform closes on itself and
the induction on the order `D` is immediate.  (An *un*shifted antidifference
`ΔH_{j+1} = H_j` would iterate cleanly only at the first step.)

## Consequences

* `taylor_abel_iterate` — the same identity with the left tower instantiated to the
  genuine iterated forward difference `F j = Δʲf` (`fdiff^[j] f`).
* `taylor_abel_smul` — the **module-valued** form (`p = `scalar action): `f` a sequence
  of scalars in a ring `R`, the weight tower valued in an `R`-module `M`.
* `taylor_abel_ring` — the form over an arbitrary (not necessarily commutative) ring,
  via `p = AddMonoidHom.mul`.
* `taylor_abel_order_two` — the explicit second-order expansion, the discrete
  analogue of `∫ f g = [f G₁] − [Δf G₂] + ∫ Δ²f G₂`.

## Method

Induction on the order `D`.  The base case `D = 0` is the trivial identity
`S = S`.  The step applies the parent's single-step transform
`abel_summation_biadditive` once to the order-`d` remainder, rewrites the two
difference relations with the tower hypotheses, and reconciles the alternating
signs with `Finset.sum_range_succ`, `pow_succ`, and `abel`.  No commutativity,
associativity, or ring structure on the value group is used — only biadditivity
of `p` and the abelian-group structure of `M`.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

namespace SummationByPartsOQ01OQ01OQ01OQ02OQ02OQ01

open Finset

/-! ### Forward difference -/

/-- The forward difference operator `Δf k = f (k+1) − f k`. -/
def fdiff {A : Type*} [Sub A] (f : ℕ → A) : ℕ → A := fun k => f (k + 1) - f k

@[simp] lemma fdiff_apply {A : Type*} [Sub A] (f : ℕ → A) (k : ℕ) :
    fdiff f k = f (k + 1) - f k := rfl

/-- Unfolding one step of the iterated forward difference:
`Δ^{d+1} f k = Δᵈf (k+1) − Δᵈf k`. -/
lemma fdiff_iterate_succ {A : Type*} [Sub A] (f : ℕ → A) (d k : ℕ) :
    (fdiff^[d + 1] f) k = (fdiff^[d] f) (k + 1) - (fdiff^[d] f) k := by
  rw [Function.iterate_succ_apply']
  rfl

/-! ### The single-step biadditive Abel transform (parent result, re-proved) -/

/-- **The single-step biadditive Abel transform (A′).**
For any biadditive pairing `p : A →+ B →+ M` between abelian groups and sequences
`f : ℕ → A`, `G : ℕ → B`,

    ∑_{k<n} p (f k) (G (k+1) − G k)
      = p (f n) (G n) − p (f 0) (G 0) − ∑_{k<n} p (f (k+1) − f k) (G (k+1)).

Re-proved here so the file is self-contained; this is the parent entry's master
identity. -/
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

/-! ### The iterated transform: a finite Taylor–Abel expansion -/

/-- **Finite Taylor–Abel expansion (T).**
Let `p : A →+ B →+ M` be biadditive between abelian groups, `F` the *left*
difference tower and `H` the *right* antidifference tower, satisfying

* `hF : ∀ j k, F (j+1) k = F j (k+1) − F j k`         (so `F j = Δʲ(F 0)`), and
* `hH : ∀ j k, H (j+1) (k+1) − H (j+1) k = H j (k+1)`  (each `H (j+1)` antidifferences the shift of `H j`).

Then for every length `n` and order `D`,

    ∑_{k<n} p (F 0 k) (H 0 (k+1))
      = ∑_{j<D} (−1)ʲ ( p (F j n) (H_{j+1} n) − p (F j 0) (H_{j+1} 0) )
        + (−1)ᴰ ∑_{k<n} p (F D k) (H D (k+1)).

The finite alternating sum is the Taylor polynomial; the last term is the
order-`D` remainder pairing the `D`-th difference of the left tower against the
`D`-th antidifference of the right tower. -/
theorem taylor_abel_biadditive
    {A B M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
    (p : A →+ B →+ M) (F : ℕ → ℕ → A) (H : ℕ → ℕ → B)
    (hF : ∀ j k, F (j + 1) k = F j (k + 1) - F j k)
    (hH : ∀ j k, H (j + 1) (k + 1) - H (j + 1) k = H j (k + 1))
    (n D : ℕ) :
    ∑ k ∈ range n, p (F 0 k) (H 0 (k + 1))
      = (∑ j ∈ range D, ((-1 : ℤ) ^ j) •
            (p (F j n) (H (j + 1) n) - p (F j 0) (H (j + 1) 0)))
        + ((-1 : ℤ) ^ D) • ∑ k ∈ range n, p (F D k) (H D (k + 1)) := by
  induction D with
  | zero => simp
  | succ d ih =>
      -- One Abel step on the order-`d` remainder.
      have key :
          ∑ k ∈ range n, p (F d k) (H d (k + 1))
            = p (F d n) (H (d + 1) n) - p (F d 0) (H (d + 1) 0)
              - ∑ k ∈ range n, p (F (d + 1) k) (H (d + 1) (k + 1)) := by
        have habel := abel_summation_biadditive p (F d) (H (d + 1)) n
        -- rewrite both difference relations via the tower hypotheses
        have hL : ∀ k, p (F d k) (H (d + 1) (k + 1) - H (d + 1) k)
            = p (F d k) (H d (k + 1)) := fun k => by rw [hH d k]
        have hR : ∀ k, p (F d (k + 1) - F d k) (H (d + 1) (k + 1))
            = p (F (d + 1) k) (H (d + 1) (k + 1)) := fun k => by rw [hF d k]
        rw [Finset.sum_congr rfl (fun k _ => hL k),
            Finset.sum_congr rfl (fun k _ => hR k)] at habel
        exact habel
      -- Reconcile signs with the inductive hypothesis.
      rw [Finset.sum_range_succ, ih, key, smul_sub, pow_succ]
      simp only [mul_comm, mul_smul, neg_one_smul, smul_neg]
      abel

/-! ### The iterated-forward-difference form -/

/-- **Taylor–Abel expansion with the genuine iterated forward difference.**
Specialising the left tower to `F j = Δʲf = fdiff^[j] f`:

    ∑_{k<n} p (f k) (H 0 (k+1))
      = ∑_{j<D} (−1)ʲ ( p (Δʲf n) (H_{j+1} n) − p (Δʲf 0) (H_{j+1} 0) )
        + (−1)ᴰ ∑_{k<n} p (Δᴰf k) (H D (k+1)). -/
theorem taylor_abel_iterate
    {A B M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
    (p : A →+ B →+ M) (f : ℕ → A) (H : ℕ → ℕ → B)
    (hH : ∀ j k, H (j + 1) (k + 1) - H (j + 1) k = H j (k + 1))
    (n D : ℕ) :
    ∑ k ∈ range n, p (f k) (H 0 (k + 1))
      = (∑ j ∈ range D, ((-1 : ℤ) ^ j) •
            (p ((fdiff^[j] f) n) (H (j + 1) n) - p ((fdiff^[j] f) 0) (H (j + 1) 0)))
        + ((-1 : ℤ) ^ D) • ∑ k ∈ range n, p ((fdiff^[D] f) k) (H D (k + 1)) := by
  have hF : ∀ j k, (fdiff^[j + 1] f) k = (fdiff^[j] f) (k + 1) - (fdiff^[j] f) k :=
    fun j k => fdiff_iterate_succ f j k
  have := taylor_abel_biadditive p (fun j => fdiff^[j] f) H hF hH n D
  simpa using this

/-! ### Module-valued and ring specialisations -/

/-- **Module-valued Taylor–Abel expansion.**
With the pairing the scalar action `r • m`, `f : ℕ → R` a sequence of scalars in a
ring `R` and the weight tower `H` valued in a left `R`-module `M`:

    ∑_{k<n} f k • H 0 (k+1)
      = ∑_{j<D} (−1)ʲ ( Δʲf n • H_{j+1} n − Δʲf 0 • H_{j+1} 0 )
        + (−1)ᴰ ∑_{k<n} Δᴰf k • H D (k+1).

This is the "different modules, fixed multiplication order" iterated transform: the
multipliers `f` and the weights `H` live in genuinely different objects. -/
theorem taylor_abel_smul
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (H : ℕ → ℕ → M)
    (hH : ∀ j k, H (j + 1) (k + 1) - H (j + 1) k = H j (k + 1))
    (n D : ℕ) :
    ∑ k ∈ range n, (f k) • H 0 (k + 1)
      = (∑ j ∈ range D, ((-1 : ℤ) ^ j) •
            ((fdiff^[j] f) n • H (j + 1) n - (fdiff^[j] f) 0 • H (j + 1) 0))
        + ((-1 : ℤ) ^ D) • ∑ k ∈ range n, (fdiff^[D] f) k • H D (k + 1) := by
  have := taylor_abel_iterate (smulAddHom R M) f H hH n D
  simpa only [smulAddHom_apply] using this

/-- **Taylor–Abel expansion over an arbitrary ring** (commutativity not required).
Taking the pairing to be ring multiplication `p = AddMonoidHom.mul`:

    ∑_{k<n} f k * H 0 (k+1)
      = ∑_{j<D} (−1)ʲ ( Δʲf n * H_{j+1} n − Δʲf 0 * H_{j+1} 0 )
        + (−1)ᴰ ∑_{k<n} Δᴰf k * H D (k+1). -/
theorem taylor_abel_ring
    {R : Type*} [Ring R] (f : ℕ → R) (H : ℕ → ℕ → R)
    (hH : ∀ j k, H (j + 1) (k + 1) - H (j + 1) k = H j (k + 1))
    (n D : ℕ) :
    ∑ k ∈ range n, f k * H 0 (k + 1)
      = (∑ j ∈ range D, ((-1 : ℤ) ^ j) •
            ((fdiff^[j] f) n * H (j + 1) n - (fdiff^[j] f) 0 * H (j + 1) 0))
        + ((-1 : ℤ) ^ D) • ∑ k ∈ range n, (fdiff^[D] f) k * H D (k + 1) := by
  have := taylor_abel_iterate (AddMonoidHom.mul (R := R)) f H hH n D
  simpa only [AddMonoidHom.mul_apply] using this

/-! ### The explicit second-order expansion -/

/-- **Second-order Taylor–Abel expansion** (`D = 2`), the discrete analogue of
integrating by parts twice:

    ∑_{k<n} p (f k) (H 0 (k+1))
      = ( p (f n) (H 1 n) − p (f 0) (H 1 0) )
        − ( p (Δf n) (H 2 n) − p (Δf 0) (H 2 0) )
        + ∑_{k<n} p (Δ²f k) (H 2 (k+1)). -/
theorem taylor_abel_order_two
    {A B M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
    (p : A →+ B →+ M) (f : ℕ → A) (H : ℕ → ℕ → B)
    (hH : ∀ j k, H (j + 1) (k + 1) - H (j + 1) k = H j (k + 1))
    (n : ℕ) :
    ∑ k ∈ range n, p (f k) (H 0 (k + 1))
      = (p (f n) (H 1 n) - p (f 0) (H 1 0))
        - (p ((fdiff f) n) (H 2 n) - p ((fdiff f) 0) (H 2 0))
        + ∑ k ∈ range n, p ((fdiff^[2] f) k) (H 2 (k + 1)) := by
  have := taylor_abel_iterate p f H hH n 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    neg_one_sq, Function.iterate_one, Function.iterate_zero, id_eq, one_smul,
    zero_add, neg_one_smul] at this ⊢
  rw [this]
  abel

end SummationByPartsOQ01OQ01OQ01OQ02OQ02OQ01
