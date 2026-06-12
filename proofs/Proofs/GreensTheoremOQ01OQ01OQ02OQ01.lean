/-
  n-Dimensional `intervalIntegral_swap` via `Measure.pi`
  (greens-theorem-oq-01-oq-01-oq-02-oq-01)

  ## Open question

  The parent `Proofs.GreensTheoremOQ01OQ01OQ02` settles the 2D
  interval-integral swap as a standalone Mathlib-pluggable lemma.
  This open question asks for the n-dim lift:

      ∫ x₀ in a 0..b 0, ⋯ ∫ xₙ₋₁ in a (n-1)..b (n-1), f x
        = ∫ x_{σ 0} in a (σ 0)..b (σ 0), ⋯ f x

  for any permutation `σ : Equiv.Perm (Fin n)`, integrating against
  `MeasureTheory.Measure.pi (fun i => volume.restrict (Set.uIcc (a i) (b i)))`.

  ## Status

  * S2 (researcher-4): Define `iteratedIntervalIntegral` recursively on
    `Fin n` via the natural-number induction principle on `n`.  Total
    definition, 0 sorries.  State `iteratedIntervalIntegral_two`.
  * S3 (researcher-4): Close `iteratedIntervalIntegral_two` via
    structural-recursion unfolding plus a `Fin.cons` ↔ indicator-form
    bridge on `Fin 2`.
  * S4 (researcher-10): State `iteratedIntervalIntegral_swap_succ`, the
    adjacent-coordinate swap invariance theorem.  This is the inductive
    building block for the general permutation invariance — every
    `σ : Equiv.Perm (Fin n)` is a product of adjacent transpositions,
    so `swap_succ` lifts to `_perm` (S5+).  Strategic `sorry`; proof
    strategy documented inline (Fin.induction on i; base case reduces
    to parent's 2D `intervalIntegral_swap`).
  * S5 (researcher-2): Repair the Mathlib v4.26.0 migration drift that
    had left this file failing to build — the applied interval bounds
    `a 0 .. b 0` now require parenthesisation `(a 0)..(b 0)` (the bare
    form mis-parsed as the set-integral region), and the `n = 2`
    integrand-equality step uses `congrArg`/`funext` in place of the
    `congr 1` that no longer reduces cleanly.  Add the sorry-free API
    primitives the deferred swap proof needs: `iteratedIntervalIntegral_succ`
    (outer-coordinate unfolding), `iteratedIntervalIntegral_zero`
    (base point), and `iteratedIntervalIntegral_congr` (pointwise
    substitution under the iterated integral).

  Sorries: 1 (on `iteratedIntervalIntegral_swap_succ`, S4 SCAFFOLD)
  Axioms: 0
-/

import Proofs.GreensTheoremOQ01OQ01OQ02
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

open MeasureTheory intervalIntegral Set

namespace GreensTheoremOQ01OQ01OQ02OQ01

/-- **n-fold iterated interval integral.**

Defined by structural recursion on `n : ℕ`.  At `n = 0`, the integrand
is evaluated at the unique element `Fin.elim0 : Fin 0 → ℝ`.  At `n + 1`,
the outermost coordinate is integrated over `a 0 .. b 0`, and the
remaining `n` integrations recurse on the tail `a ∘ Fin.succ`,
`b ∘ Fin.succ` with the integrand re-shaped by `Fin.cons`.

This is the n-dim analog of the parent file's iterated
`∫ x in a 0..b 0, ∫ y in a 1..b 1, f (x, y)` form (2D).  The S3+
iterations will prove permutation invariance under
`Equiv.Perm (Fin n)`. -/
noncomputable def iteratedIntervalIntegral :
    ∀ {n : ℕ}, (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, _, _, f => f Fin.elim0
  | _ + 1, a, b, f =>
      ∫ x₀ in (a 0)..(b 0),
        iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
          (fun rest => f (Fin.cons x₀ rest))

/-- **Unfolding lemma.** The `(n+1)`-fold iterated interval integral peels
off its outermost coordinate, integrating over `a 0 .. b 0` while the
remaining `n` coordinates recurse on the tails `a ∘ Fin.succ`,
`b ∘ Fin.succ`. Definitional, but exposed as a named rewrite target so
downstream proofs (notably the swap-invariance induction) need not
re-derive the structural recursion each time. -/
theorem iteratedIntervalIntegral_succ {n : ℕ}
    (a b : Fin (n + 1) → ℝ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = ∫ x₀ in (a 0)..(b 0),
          iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
            (fun rest => f (Fin.cons x₀ rest)) := rfl

/-- **Zero-dimensional base.** The empty iterated integral is the integrand
evaluated at the unique point `Fin.elim0 : Fin 0 → ℝ`. Definitional. -/
@[simp] theorem iteratedIntervalIntegral_zero
    (a b : Fin 0 → ℝ) (f : (Fin 0 → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f = f Fin.elim0 := rfl

/-- **Pointwise congruence.** Iterated interval integrals of integrands that
agree everywhere are equal. Proved by induction on `n`, peeling one
coordinate at a time with `intervalIntegral.integral_congr`.

This is the basic substitution principle the permutation-invariance proofs
rely on when re-shaping the integrand through `Fin.cons` (the deferred
`iteratedIntervalIntegral_swap_succ` base case needs exactly this to bridge
the `Fin.cons` form against the parent's 2D `intervalIntegral_swap`). -/
theorem iteratedIntervalIntegral_congr :
    ∀ {n : ℕ} (a b : Fin n → ℝ) {f g : (Fin n → ℝ) → ℝ},
      (∀ v, f v = g v) →
      iteratedIntervalIntegral a b f = iteratedIntervalIntegral a b g
  | 0, _, _, _, _, h => h _
  | n + 1, a, b, f, g, h => by
      rw [iteratedIntervalIntegral_succ a b f, iteratedIntervalIntegral_succ a b g]
      refine intervalIntegral.integral_congr (fun x₀ _ => ?_)
      exact iteratedIntervalIntegral_congr (a ∘ Fin.succ) (b ∘ Fin.succ)
        (fun rest => h (Fin.cons x₀ rest))

/-- **Specialisation to `n = 2` matches the parent's iterated form.**

Unfolding `iteratedIntervalIntegral` for `n = 2` twice yields

  `∫ x in a 0..b 0, ∫ y in a 1..b 1, f (Fin.cons x (Fin.cons y Fin.elim0))`.

The Fin-vector form `Fin.cons x (Fin.cons y Fin.elim0)` is pointwise
equal to `fun i => if i = 0 then x else y` for `i : Fin 2`: `fin_cases`
on `i` reduces both sides to the same scalar on each branch.

The two `∫` bounds line up by reduction: `(a ∘ Fin.succ) 0 = a 1`
and `(b ∘ Fin.succ) 0 = b 1` hold by `rfl` (function composition plus
`Fin.succ (0 : Fin 1) = (1 : Fin 2)`).  Hence the LHS is
definitionally the iterated form above, and the two integrals are
equal by `intervalIntegral.integral_congr` applied twice. -/
theorem iteratedIntervalIntegral_two
    (a b : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = ∫ x in (a 0)..(b 0), ∫ y in (a 1)..(b 1),
          f (fun i => if i = 0 then x else y) := by
  -- Reduce LHS by structural recursion at `n = 2`, `n = 1`, `n = 0`.
  show ∫ x in (a 0)..(b 0), ∫ y in (a 1)..(b 1),
         f (Fin.cons x (Fin.cons y Fin.elim0))
       = _
  -- Two interval-integrals agree if the integrands agree pointwise on
  -- their respective `uIcc`s; here in fact they agree everywhere.
  refine intervalIntegral.integral_congr ?_
  intro x _
  refine intervalIntegral.integral_congr ?_
  intro y _
  -- Reduce to equality of the two integrand functions on `Fin 2 → ℝ`.
  refine congrArg f ?_
  funext i
  fin_cases i <;> simp

/-- **S4 SCAFFOLD: Adjacent-coordinate swap invariance.**

For an integrand `f : (Fin (n+1) → ℝ) → ℝ` and any `i : Fin n`, swapping
the `i`-th and `(i+1)`-th coordinates — i.e. transposing `i.castSucc`
with `i.succ` in `Fin (n+1)` — preserves the iterated interval integral,
provided we relabel the bounds `a` and `b` and permute the input to `f`
accordingly.

This is the inductive building block for the eventual general
permutation invariance: every `σ : Equiv.Perm (Fin (n+1))` is a product
of adjacent transpositions (the simple-reflection generators of the
symmetric group; cf. `Equiv.Perm.swap_induction_on'`), so
`iteratedIntervalIntegral_swap_succ` lifts to the full
`iteratedIntervalIntegral_perm` (deferred to S5+).

The continuity hypothesis `_hf : Continuous f` is a clean sufficient
condition that subsumes the measurability and integrability obligations
of the parent's 2D `intervalIntegral_swap` after restriction to the
compact box `∏ i, Set.uIcc (a i) (b i)`.  Weaker hypotheses
(only joint measurability + product-measure integrability) are possible
but obscure the inductive structure; S5 may refine.

**Proof strategy (deferred to S5/S6).** `Fin.induction` on `i`:

* **Base case** (`i = 0`): two structural-recursion unfoldings of
  `iteratedIntervalIntegral` at the outermost coordinates rewrite both
  sides into the curried form
  `∫ x in a 0..b 0, ∫ y in a 1..b 1, F x y rest` (LHS) versus the
  variable-swapped curried form (RHS).  Apply the parent's
  `Proofs.GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap` after a
  `Fin.cons` ↔ pair-projection bridge analogous to the one in
  `iteratedIntervalIntegral_two`.
* **Inductive step** (`i = j.succ`): the outermost integral over
  `a 0 .. b 0` is untouched by the swap (the transposed indices
  `j.succ.castSucc` and `j.succ.succ` are both ≥ 1 in `Fin (n+1)`); a
  single application of `intervalIntegral.integral_congr` brings the
  swap inside the outer integral, and the IH at `j` (one dimension
  smaller) closes the inner integral.

Estimated S5 size to discharge: ~80-120 lines including the
`Fin.cons`-pair bridge in the base case. -/
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (_hf : Continuous f) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ)) := by
  sorry

end GreensTheoremOQ01OQ01OQ02OQ01
