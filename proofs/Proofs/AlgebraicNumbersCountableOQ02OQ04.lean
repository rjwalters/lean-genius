import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.Computability.Primrec
import Mathlib.Computability.Partrec
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable

/-
# Countability of Computable Real Numbers

## Open Question (algebraic-numbers-countable-oq-02-oq-04)

Prove that the set of *computable* real numbers is countable.

A real number is **computable** if there exists a Turing machine that, given
`n : ℕ`, outputs a rational `q n : ℚ` such that the sequence `q 0, q 1, q 2, ...`
converges to it. This formalizes the intuition that the "describable" reals form
a countable subfamily of ℝ: each is named by a finite Turing-machine description,
and finite descriptions form a countable set.

The set of computable reals sits between algebraic and ℝ in the cardinality
hierarchy:

    ℚ  ⊊  algebraic  ⊊  computable  ⊊  ℝ
    ↑          ↑              ↑       ↑
    ℵ₀         ℵ₀             ℵ₀      𝔠

Both ℚ ⊊ algebraic ⊊ computable are strict (computable contains transcendentals
like π and e), but all three are countable. The final inclusion is strict by
cardinality (computable is countable but ℝ has cardinality 𝔠).

## Main Result (SCAFFOLD)

`computable_reals_countable` (sorry, S1 scaffold): the set
`{r : ℝ | IsComputable r}` is countable.

## Proof Strategy (deferred to future iterations)

The proof rests on three Mathlib facts:

1. **Code countability**: `Nat.Partrec.Code` (the type of recursive program codes)
   is `Encodable`, hence its underlying type is countable.

2. **Code completeness**: every `Computable f : ℕ → ℚ` has an underlying recursive
   code in `Nat.Partrec.Code`. (Equivalently, every TM has a Gödel number.)

3. **Image of countable is countable** (`Set.Countable.image`): combining 1 and 2,
   the "limit-of-eval" map from `Nat.Partrec.Code` onto computable reals
   exhibits the latter as the image of a countable set.

Defining `decodeReal : Nat.Partrec.Code → Option ℝ` to send each code to the
limit of its rational sequence (when defined) yields the surjection onto
computable reals.

## Status

- **S1** (this PR): SCAFFOLD — `IsComputable` definition + main theorem statement
  with `sorry`. No additional axioms; strategy documented.
- **S2+**: implement the `Nat.Partrec.Code` ↔ `Computable` ↔ ℝ pipeline and
  discharge the `sorry`.

## References

- Mathlib `Computable`: `Mathlib.Computability.Partrec`
- Mathlib `Nat.Partrec.Code`: `Mathlib.Computability.PartrecCode`
- Pour-El & Richards, *Computability in Analysis and Physics* (1989)
- Weihrauch, *Computable Analysis: An Introduction* (2000)
- Turing, "On Computable Numbers" (1936) — the original definition

Tags: set-theory, cardinality, real-analysis, computability, computable-analysis
-/

namespace AlgebraicNumbersCountableOQ02OQ04

open Cardinal Filter

/-- A real number `r` is **computable** if there exists a `Computable` function
    `f : ℕ → ℚ` (in Mathlib's `Computable` sense) such that the real-valued
    sequence `(f n : ℝ)` converges to `r`.

    Equivalently: there is a Turing machine that, on input `n`, halts and
    outputs a rational approximation `q_n`, with the sequence `q_0, q_1, q_2, ...`
    converging to `r`. The Turing-machine description is the "name" of `r`. -/
def IsComputable (r : ℝ) : Prop :=
  ∃ f : ℕ → ℚ, Computable f ∧ Tendsto (fun n => (f n : ℝ)) atTop (nhds r)

/-- **Main Theorem (SCAFFOLD — sorry)**: The set of computable real numbers is
    countable.

    Proof strategy (to be filled in by future iterations):

    * Every `Computable f : ℕ → ℚ` arises from a recursive code in
      `Nat.Partrec.Code` (Mathlib: `Computable` is defined in terms of `Partrec`
      and partial recursive functions admit codes via `Nat.Partrec.Code.exists`).
    * `Nat.Partrec.Code` is an `Encodable` inductive type, hence its underlying
      type is `Countable`.
    * The image of a countable set under any function is countable
      (`Set.Countable.image`). Sending each code to the limit of its rational
      evaluations gives a surjection from a countable set onto the computable
      reals.

    Hence the set is countable. -/
theorem computable_reals_countable :
    Set.Countable {r : ℝ | IsComputable r} := by
  sorry

/-- **Cardinal form**: the cardinality of the computable reals is at most ℵ₀.

    Direct consequence of `computable_reals_countable` via
    `le_aleph0_iff_set_countable`. -/
theorem card_computable_reals_le_aleph0 :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) ≤ ℵ₀ :=
  le_aleph0_iff_set_countable.mpr computable_reals_countable

end AlgebraicNumbersCountableOQ02OQ04
