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

  ## S2 (this iteration)

  Lay the foundation:
  * Define `iteratedIntervalIntegral` recursively on `Fin n` via the
    natural-number induction principle on `n`.  Total definition,
    0 sorries.
  * State the `n = 2` specialisation that recovers the parent's
    iterated form.  Sorry-bearing — proof deferred to S3.

  Per `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-01/state.md`
  S2 next-action specification.

  Sorries: 1 (`iteratedIntervalIntegral_two`)
  Axioms: 0
-/

import Proofs.GreensTheoremOQ01OQ01OQ02
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fin
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
      ∫ x₀ in a 0 .. b 0,
        iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
          (fun rest => f (Fin.cons x₀ rest))

/-- **Specialisation to `n = 2` matches the parent's iterated form.**

Unfolding `iteratedIntervalIntegral` for `n = 2` twice yields

  `∫ x in a 0..b 0, ∫ y in a 1..b 1, f (Fin.cons x (Fin.cons y Fin.elim0))`.

The Fin-vector form `Fin.cons x (Fin.cons y Fin.elim0)` is canonically
equal to `fun i => if i = 0 then x else y` for `i : Fin 2`, since
`Fin 2` has only the two values `0` and `1` and the two forms agree
on each.  The proof bridges these forms via `funext` + case analysis
on `i : Fin 2`.

Proof deferred to S3 — the recursive `simp` unfolding plus the
`Fin.cons` ↔ indicator-form bridge is straightforward but several
lines; S2's job is to fix the statement.  S3 will close this. -/
theorem iteratedIntervalIntegral_two
    (a b : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = ∫ x in a 0 .. b 0, ∫ y in a 1 .. b 1,
          f (fun i => if i = 0 then x else y) := by
  sorry

end GreensTheoremOQ01OQ01OQ02OQ01
