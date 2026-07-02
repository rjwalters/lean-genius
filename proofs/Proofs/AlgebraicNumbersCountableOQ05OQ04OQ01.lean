import Mathlib

/-
# The Exact Cardinality of the Algebraic Elements is `max #K ℵ₀`

## Open Question OQ-05-OQ-04-OQ-01

The parent entry `AlgebraicNumbersCountableOQ05OQ04` proves the sharp *countability*
characterization for a field extension `L / K`:

  `{x : L | IsAlgebraic K x}` is countable  ↔  the base field `K` is countable.

Its open question asks whether this coarse (countable / uncountable) dichotomy can be
upgraded to an **exact cardinal formula**:

> Can the characterization be upgraded to exact cardinality —
> `#{x : L | IsAlgebraic K x} = max (#K) ℵ₀` whenever `L` contains the algebraic
> closure of `K` — recovering both the countable and uncountable regimes as the two
> cases of a single cardinal formula?  (Mathlib's `Algebra.IsAlgebraic.cardinalMk_le_max`
> gives one inequality.)

## The sharp answer

The answer is **yes**, with the natural hypothesis pinned down: it is enough that the
ambient field `L` be **algebraically closed** (`IsAlgClosed L`), which is exactly the
statement that `L` contains an algebraic closure of `K`.  Under this hypothesis

  `#{x : L | IsAlgebraic K x} = max (#K) ℵ₀`.

Note the hypothesis is genuinely needed: with `L = K` a finite field the algebraic set is
just `K`, of finite cardinality `#K`, whereas `max (#K) ℵ₀ = ℵ₀`.  The formula only holds
once `L` is large enough to hold the whole (infinite) algebraic closure — which
`IsAlgClosed L` guarantees.

## Proof architecture

The algebraic elements form the *relative algebraic closure* `algebraicClosure K L`, an
intermediate field whose carrier is exactly `{x : L | IsAlgebraic K x}`
(`mem_algebraicClosure_iff`).  Write `A := algebraicClosure K L`.

* **Upper bound** `#A ≤ max (#K) ℵ₀`:  `A` is algebraic over `K`
  (`algebraicClosure.isAlgebraic`), so this is Mathlib's
  `Algebra.IsAlgebraic.cardinalMk_le_max` — the one inequality the open question already
  had in hand.

* **Lower bound** `max (#K) ℵ₀ ≤ #A`, split into two:
  * `#K ≤ #A`:  the base field embeds into `A` through the injective `algebraMap`.
  * `ℵ₀ ≤ #A`:  when `L` is algebraically closed, `A` is an *absolute* algebraic closure
    of `K` (`algebraicClosure.isAlgClosure`), hence itself algebraically closed, hence
    **infinite** — an algebraically closed field is never finite.

`le_antisymm` assembles the two bounds into the exact formula.

## Recovering both regimes, and the parent

* Countable regime: `K = ℚ` (or any countable field) gives `#K = ℵ₀`, so the algebraic
  numbers in `ℂ` have cardinality `max ℵ₀ ℵ₀ = ℵ₀` — the classical countability of the
  algebraic numbers, now as an *exact* count.
* Uncountable regime: `K = ℝ` gives `#K = 𝔠 > ℵ₀`, so the elements of `ℂ` algebraic over
  `ℝ` number exactly `𝔠` — the sharp form of the parent's `p`-adic-style obstruction.

Both are the two cases `max (#K) ℵ₀ = #K` and `= ℵ₀` of one formula.

## Axioms: 0 | Sorries: 0
-/

namespace AlgebraicNumbersCountableOQ05OQ04OQ01

open Cardinal

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-! ### Upper bound (Mathlib's inequality, restated on the algebraic set) -/

/-- **Upper bound.**  The algebraic elements of any field extension `L / K` number at most
`max (#K) ℵ₀`.  This is Mathlib's `Algebra.IsAlgebraic.cardinalMk_le_max` applied to the
relative algebraic closure `algebraicClosure K L`, whose carrier is exactly the algebraic
set.  It is the single inequality the open question already had available. -/
theorem cardinalMk_algebraicClosure_le :
    #(algebraicClosure K L) ≤ max (#K) ℵ₀ :=
  Algebra.IsAlgebraic.cardinalMk_le_max K (algebraicClosure K L)

/-! ### Lower bounds -/

/-- The base field embeds into its relative algebraic closure via the (injective)
`algebraMap`, so `#K ≤ #(algebraicClosure K L)`. -/
theorem cardinalMk_le_algebraicClosure :
    #K ≤ #(algebraicClosure K L) :=
  Cardinal.mk_le_of_injective
    (FaithfulSMul.algebraMap_injective K (algebraicClosure K L))

/-- **Infinitude of the algebraic set.**  When `L` is algebraically closed, the relative
algebraic closure `algebraicClosure K L` is an *absolute* algebraic closure of `K`
(`algebraicClosure.isAlgClosure`), hence itself algebraically closed, hence infinite. -/
instance [IsAlgClosed L] : IsAlgClosed (algebraicClosure K L) :=
  IsAlgClosure.isAlgClosed K

theorem aleph0_le_cardinalMk_algebraicClosure [IsAlgClosed L] :
    ℵ₀ ≤ #(algebraicClosure K L) :=
  Cardinal.aleph0_le_mk (algebraicClosure K L)

/-! ### The exact cardinal formula -/

/-- **The exact cardinality, on the relative algebraic closure.**  If `L` is algebraically
closed then the relative algebraic closure of `K` in `L` has cardinality exactly
`max (#K) ℵ₀`. -/
theorem cardinalMk_algebraicClosure_eq_max [IsAlgClosed L] :
    #(algebraicClosure K L) = max (#K) ℵ₀ :=
  le_antisymm cardinalMk_algebraicClosure_le
    (max_le cardinalMk_le_algebraicClosure aleph0_le_cardinalMk_algebraicClosure)

/-- The relative algebraic closure and the algebraic set have the same elements, hence the
same cardinality. -/
theorem cardinalMk_setOf_eq_algebraicClosure :
    #{x : L | IsAlgebraic K x} = #(algebraicClosure K L) :=
  Cardinal.mk_congr (Equiv.subtypeEquivRight fun _ => (mem_algebraicClosure_iff).symm)

/-- **Main result (OQ-05-OQ-04-OQ-01).**  For a field extension `L / K` with `L`
algebraically closed, the set of elements of `L` algebraic over `K` has cardinality exactly

  `#{x : L | IsAlgebraic K x} = max (#K) ℵ₀`.

This upgrades the parent's countable/uncountable dichotomy to a single exact cardinal
formula, with the two regimes appearing as `max (#K) ℵ₀ = #K` and `= ℵ₀`. -/
theorem cardinalMk_setOf_isAlgebraic_eq_max [IsAlgClosed L] :
    #{x : L | IsAlgebraic K x} = max (#K) ℵ₀ := by
  rw [cardinalMk_setOf_eq_algebraicClosure, cardinalMk_algebraicClosure_eq_max]

/-! ### The absolute algebraic closure

The same formula for Mathlib's absolute construction `AlgebraicClosure K` — the whole type
is algebraic over `K`, so the algebraic set is everything. -/

/-- **Absolute form.**  The (absolute) algebraic closure of `K` has cardinality exactly
`max (#K) ℵ₀`.  This is the special case `L = AlgebraicClosure K` of the main result. -/
theorem cardinalMk_algebraicClosure_type_eq_max :
    #(AlgebraicClosure K) = max (#K) ℵ₀ :=
  le_antisymm (Algebra.IsAlgebraic.cardinalMk_le_max K (AlgebraicClosure K))
    (max_le
      (Cardinal.mk_le_of_injective (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)))
      (Cardinal.aleph0_le_mk (AlgebraicClosure K)))

/-! ### Worked instances: both regimes of the single formula -/

section Examples

/-- **Countable regime.**  The algebraic numbers (elements of `ℂ` algebraic over `ℚ`) number
exactly `ℵ₀`: here `max (#ℚ) ℵ₀ = max ℵ₀ ℵ₀ = ℵ₀`.  This is the classical countability of
the algebraic numbers, sharpened to an exact count. -/
example : #{x : ℂ | IsAlgebraic ℚ x} = ℵ₀ := by
  rw [cardinalMk_setOf_isAlgebraic_eq_max, Cardinal.mkRat, max_self]

/-- **Uncountable regime.**  The elements of `ℂ` algebraic over `ℝ` number exactly the
continuum `𝔠`: here `#ℝ = 𝔠 ≥ ℵ₀`, so `max (#ℝ) ℵ₀ = 𝔠`.  (Indeed every element of `ℂ` is
algebraic over `ℝ`, of degree at most `2`.)  This is the sharp form of the parent's
uncountable obstruction. -/
example : #{x : ℂ | IsAlgebraic ℝ x} = 𝔠 := by
  rw [cardinalMk_setOf_isAlgebraic_eq_max, Cardinal.mk_real,
    max_eq_left (Cardinal.aleph0_le_continuum)]

end Examples

end AlgebraicNumbersCountableOQ05OQ04OQ01
