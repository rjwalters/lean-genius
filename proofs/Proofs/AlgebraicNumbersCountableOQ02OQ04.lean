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

/-! ## S2 — Lower bound: every rational is computable

The upper bound `card_computable_reals_le_aleph0` rests on the main `sorry`.
The lower bound `ℵ₀ ≤ #{r | IsComputable r}` is unconditional: it follows
from the embedding `ℚ ↪ {r | IsComputable r}` via `q ↦ (q : ℝ)`, witnessed
by the constant rational sequence.

This S2 deliverable adds, with no new axioms or sorries:

* `rat_isComputable q : IsComputable (q : ℝ)` — every rational is a computable
  real, via the constant sequence `fun _ => q`. Uses `Computable.const`
  (with `Primcodable ℚ` from `Mathlib.Data.Rat.Denumerable`) and
  `tendsto_const_nhds`.
* Specialisations to ℕ, ℤ, 0, 1.
* `aleph0_le_card_computable_reals : ℵ₀ ≤ #{r | IsComputable r}` — cardinal
  lower bound. The injection `ℚ → {r | IsComputable r}` sends `q ↦ ⟨(q : ℝ), …⟩`;
  injectivity uses `Rat.cast` injectivity on ℝ; the count uses `Cardinal.mk_rat`.
* `card_computable_reals_eq_aleph0` — exact ℵ₀ equality, contingent only on
  the main `sorry` (no new assumptions).
-/

/-- **S2 lemma**: every rational real is computable, witnessed by the constant
    sequence `fun _ => q`.

    *Proof*. Take `f := fun _ => q`. Then `Computable f` is
    `Computable.const q` (uses `Primcodable ℚ` via
    `Mathlib.Data.Rat.Denumerable`), and the limit of `(f n : ℝ)` is just
    `tendsto_const_nhds`. -/
theorem rat_isComputable (q : ℚ) : IsComputable (q : ℝ) :=
  ⟨fun _ => q, Computable.const q, tendsto_const_nhds⟩

/-- **S2 lemma** — every integer is computable, via `rat_isComputable` and the
    integer-to-rational cast `(n : ℤ) → (n : ℚ) → (n : ℝ)`. -/
theorem int_isComputable (n : ℤ) : IsComputable (n : ℝ) := by
  have h := rat_isComputable (n : ℚ)
  simpa using h

/-- **S2 lemma** — every natural number is computable. -/
theorem nat_isComputable (n : ℕ) : IsComputable (n : ℝ) := by
  have h := rat_isComputable (n : ℚ)
  simpa using h

/-- **S2 lemma** — zero is computable. -/
theorem zero_isComputable : IsComputable (0 : ℝ) := by
  simpa using rat_isComputable 0

/-- **S2 lemma** — one is computable. -/
theorem one_isComputable : IsComputable (1 : ℝ) := by
  simpa using rat_isComputable 1

/-- **S2 main result — cardinal lower bound**: there are at least ℵ₀ computable
    real numbers.

    *Proof*. The map `ι : ℚ → {r : ℝ | IsComputable r}` defined by
    `q ↦ ⟨(q : ℝ), rat_isComputable q⟩` is injective: if
    `ι q₁ = ι q₂` then their underlying real values are equal, and
    `Rat.cast` is injective on ℝ. Hence `#ℚ ≤ #{r | IsComputable r}`,
    and `Cardinal.mk_rat : #ℚ = ℵ₀` finishes. -/
theorem aleph0_le_card_computable_reals :
    ℵ₀ ≤ (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) := by
  let ι : ℚ → ({r : ℝ | IsComputable r} : Set ℝ) :=
    fun q => ⟨(q : ℝ), rat_isComputable q⟩
  have hinj : Function.Injective ι := by
    intro q₁ q₂ hq
    have hv : ((q₁ : ℝ)) = ((q₂ : ℝ)) := by
      have := congrArg Subtype.val hq
      simpa [ι] using this
    exact_mod_cast hv
  have hcard : (#ℚ : Cardinal) ≤ #({r : ℝ | IsComputable r} : Set ℝ) :=
    Cardinal.mk_le_of_injective hinj
  simpa [Cardinal.mk_rat] using hcard

/-! ## Exact ℵ₀ equality (contingent on the main `sorry`)

Combining the (sorry-dependent) upper bound with the unconditional lower
bound yields the exact cardinality.
-/

/-- **Conditional corollary**: once `computable_reals_countable` is discharged
    (target of S3+), the computable reals have cardinality exactly ℵ₀.

    This statement adds no new assumptions — it is a pure consequence of
    `card_computable_reals_le_aleph0` (currently rests on the main `sorry`)
    and `aleph0_le_card_computable_reals` (unconditional, S2). -/
theorem card_computable_reals_eq_aleph0 :
    (#({r : ℝ | IsComputable r} : Set ℝ) : Cardinal) = ℵ₀ :=
  le_antisymm card_computable_reals_le_aleph0 aleph0_le_card_computable_reals

end AlgebraicNumbersCountableOQ02OQ04
