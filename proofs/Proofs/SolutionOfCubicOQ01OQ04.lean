import Proofs.SolutionOfCubicOQ01
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The Tschirnhaus Shift as a Bijection of Root Multisets (Solution of Cubic, OQ-01-OQ-04)

## What This Proves

The parent entry `SolutionOfCubicOQ01` (`solution-of-cubic-oq-01`) reduces the general
cubic `a x³ + b x² + c x + d` to the **depressed** cubic `t³ + p t + q` via the Tschirnhaus
shift `x = t − b/(3a)`, and proves the reduction *pointwise*: it carries individual roots of
the depressed cubic to roots of the general cubic and back
(`general_root_of_depressed_root` / `depressed_root_of_general_root`).

This entry **promotes that pointwise bijection to the level of the entire root multiset and
the polynomial factorization**.  Working with the actual polynomials

  `generalCubicPoly a b c d = C a · X³ + C b · X² + C c · X + C d`   (the general cubic), and
  `depressedCubic p q       = X³ + C p · X + C q`                    (the parent's depressed cubic),

we show:

* `generalCubicPoly_roots` — **the root multiset bijection**:
  `(generalCubicPoly a b c d).roots = (depressedCubic p q).roots.map (· − b/(3a))`.
  Every root of the depressed cubic, *with its multiplicity*, is shifted by `−b/(3a)` to a
  root of the general cubic, and this exhausts the general cubic's roots.  This is the
  multiplicity-aware strengthening of the parent's pointwise statement.

* `generalCubicPoly_factorization` — **the factorization mirror**:
  `generalCubicPoly a b c d = C a · ∏_{t ∈ (depressedCubic p q).roots} (X − C (t − b/(3a)))`.
  The general cubic factors as the leading coefficient times the product of the shifted linear
  factors coming from the depressed cubic's roots.

* `generalCubicPoly_roots_card` — the shift preserves the number of roots (counted with
  multiplicity): the two root multisets have equal cardinality.

## Key Infrastructure

The technical heart is `roots_comp_X_sub_C`: composing a polynomial with the shift `X ↦ X − C s`
translates its root multiset by `+s`,
  `(p.comp (X − C s)).roots = p.roots.map (· + s)`,
proved over an arbitrary commutative ring via Mathlib's
`Polynomial.rootMultiplicity_eq_rootMultiplicity` and `Polynomial.count_roots`.  The cubic
statements then follow from the polynomial identity `generalCubicPoly.comp (X − C s) = C a · depressedCubic`
(itself transferred from the parent's evaluation identity `generalCubicEval_shift` via
`Polynomial.funext`), together with `roots_C_mul` and `C_leadingCoeff_mul_prod_multiset_X_sub_C`.

## Proof Techniques

`Polynomial.funext` to lift the parent's *evaluation* identity to a *polynomial* identity;
multiplicity bookkeeping (`count_roots`, `rootMultiplicity_eq_rootMultiplicity`,
`Multiset.count_map_eq_count'`) for the shift-roots lemma; the splitting factorization over the
algebraically closed field `ℂ` for the factorization statement.  Everything is over `ℂ`,
matching the parent, and is `0`-axiom.
-/

namespace SolutionOfCubicOQ04

open Complex Polynomial SolutionOfCubic SolutionOfCubicOQ01

/-! ## Part 0: A shift-of-variable lemma for root multisets

Composing with the linear shift `X ↦ X − C s` translates the entire root multiset by `+s`.
This holds over any commutative ring with no zero divisors; we only need it over `ℂ`. -/

/-- The multiplicity of `a` as a root of `p.comp (X − C s)` equals the multiplicity of `a − s`
as a root of `p`. -/
theorem rootMultiplicity_comp_X_sub_C (p : ℂ[X]) (s a : ℂ) :
    rootMultiplicity a (p.comp (X - C s)) = p.rootMultiplicity (a - s) := by
  rw [rootMultiplicity_eq_rootMultiplicity (p := p.comp (X - C s)) (t := a), comp_assoc]
  have hxs : (X - C s).comp (X + C a) = X + C (a - s) := by
    rw [sub_comp, X_comp, C_comp, C_sub]; ring
  rw [hxs, ← rootMultiplicity_eq_rootMultiplicity]

/-- **Shift of variable on root multisets.** Composing a polynomial with `X − C s` translates
its root multiset by `+s`:  `(p.comp (X − C s)).roots = p.roots.map (· + s)`. -/
theorem roots_comp_X_sub_C (p : ℂ[X]) (s : ℂ) :
    (p.comp (X - C s)).roots = p.roots.map (· + s) := by
  classical
  have hinj : Function.Injective (· + s) := fun a b h => by simpa using h
  ext a
  rw [count_roots, rootMultiplicity_comp_X_sub_C, ← count_roots]
  conv_rhs => rw [show a = (a - s) + s from by ring]
  exact (Multiset.count_map_eq_count' (· + s) p.roots hinj (a - s)).symm

/-! ## Part 1: The general cubic as a polynomial

The parent works with the *evaluation function* `generalCubicEval`.  Here we package the same
data as an honest `Polynomial ℂ` so we can talk about its `roots` multiset and factorization. -/

/-- The general cubic `a x³ + b x² + c x + d` as a polynomial in `ℂ[X]`. -/
noncomputable def generalCubicPoly (a b c d : ℂ) : ℂ[X] :=
  C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

/-- Evaluating `generalCubicPoly` reproduces the parent's `generalCubicEval`. -/
theorem generalCubicPoly_eval (a b c d x : ℂ) :
    (generalCubicPoly a b c d).eval x = generalCubicEval a b c d x := by
  simp [generalCubicPoly, generalCubicEval, eval_add, eval_mul, eval_pow, eval_C, eval_X]

/-- The Tschirnhaus shift as a **polynomial identity**: substituting `X ↦ X − b/(3a)` into the
general cubic yields `a` times the parent's depressed cubic.  This lifts the parent's
*evaluation* identity `generalCubicEval_shift` to an identity of polynomials, using that `ℂ`
is infinite (`Polynomial.funext`). -/
theorem generalCubicPoly_comp_shift (a b c d : ℂ) (ha : a ≠ 0) :
    (generalCubicPoly a b c d).comp (X - C (b / (3 * a)))
      = C a * depressedCubic (depressedP a b c) (depressedQ a b c d) := by
  apply Polynomial.funext
  intro x
  rw [eval_comp, eval_sub, eval_X, eval_C, generalCubicPoly_eval, eval_mul, eval_C]
  exact generalCubicEval_shift a b c d x ha

/-! ## Part 2: The root-multiset bijection -/

/-- **Root multiset bijection.** The Tschirnhaus shift `t ↦ t − b/(3a)` carries the root
multiset of the depressed cubic — with multiplicities — onto the root multiset of the general
cubic.  This is the multiplicity-aware promotion of the parent's pointwise root correspondence. -/
theorem generalCubicPoly_roots (a b c d : ℂ) (ha : a ≠ 0) :
    (generalCubicPoly a b c d).roots
      = (depressedCubic (depressedP a b c) (depressedQ a b c d)).roots.map
          (· - b / (3 * a)) := by
  set s := b / (3 * a) with hs
  set D := depressedCubic (depressedP a b c) (depressedQ a b c d) with hD
  -- composing the general cubic with the shift gives `C a * D`
  have hcomp : (generalCubicPoly a b c d).comp (X - C s) = C a * D :=
    generalCubicPoly_comp_shift a b c d ha
  -- so its root multiset is `D.roots`, but it is also `G.roots.map (· + s)`
  have h2 : ((generalCubicPoly a b c d).comp (X - C s)).roots
      = (generalCubicPoly a b c d).roots.map (· + s) := roots_comp_X_sub_C _ s
  rw [hcomp, roots_C_mul D ha] at h2
  -- `h2 : D.roots = G.roots.map (· + s)`; invert the shift
  rw [h2, Multiset.map_map]
  simp

/-- The Tschirnhaus shift preserves the number of roots counted with multiplicity. -/
theorem generalCubicPoly_roots_card (a b c d : ℂ) (ha : a ≠ 0) :
    Multiset.card (generalCubicPoly a b c d).roots
      = Multiset.card (depressedCubic (depressedP a b c) (depressedQ a b c d)).roots := by
  rw [generalCubicPoly_roots a b c d ha, Multiset.card_map]

/-! ## Part 3: The factorization mirror -/

/-- The general cubic has degree `3`. -/
theorem generalCubicPoly_natDegree (a b c d : ℂ) (ha : a ≠ 0) :
    (generalCubicPoly a b c d).natDegree = 3 := by
  unfold generalCubicPoly
  compute_degree!

/-- The leading coefficient of the general cubic is `a`. -/
theorem generalCubicPoly_leadingCoeff (a b c d : ℂ) (ha : a ≠ 0) :
    (generalCubicPoly a b c d).leadingCoeff = a := by
  rw [leadingCoeff, generalCubicPoly_natDegree a b c d ha]
  simp [generalCubicPoly, coeff_add, coeff_C_mul, coeff_X_pow]

/-- **Factorization mirror.** The general cubic factors as its leading coefficient `a` times the
product of the linear factors obtained by shifting each root of the depressed cubic by `−b/(3a)`:

  `generalCubicPoly a b c d = C a · ∏_{t ∈ depressedCubic.roots} (X − C (t − b/(3a)))`. -/
theorem generalCubicPoly_factorization (a b c d : ℂ) (ha : a ≠ 0) :
    generalCubicPoly a b c d
      = C a * ((depressedCubic (depressedP a b c) (depressedQ a b c d)).roots.map
          (fun t => X - C (t - b / (3 * a)))).prod := by
  have hcard : Multiset.card (generalCubicPoly a b c d).roots
      = (generalCubicPoly a b c d).natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hfact := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [generalCubicPoly_leadingCoeff a b c d ha] at hfact
  rw [← hfact, generalCubicPoly_roots a b c d ha, Multiset.map_map]
  rfl

/-! ## Part 4: Sanity checks -/

-- The shift lemma applied to the depressed↦general direction recovers the parent's pointwise
-- statement at the level of root membership.
example (a b c d t : ℂ) (ha : a ≠ 0)
    (ht : t ∈ (depressedCubic (depressedP a b c) (depressedQ a b c d)).roots) :
    (t - b / (3 * a)) ∈ (generalCubicPoly a b c d).roots := by
  rw [generalCubicPoly_roots a b c d ha]
  exact Multiset.mem_map_of_mem _ ht

#check @generalCubicPoly_roots
#check @generalCubicPoly_factorization

end SolutionOfCubicOQ04
