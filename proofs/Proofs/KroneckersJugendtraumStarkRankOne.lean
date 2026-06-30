import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.Tactic

/-
# Kronecker's Jugendtraum (Hilbert's 12th), rank-one Stark units

## What this file contains

Hilbert's 12th problem (Kronecker's *Jugendtraum*) asks for explicit generators of the
abelian extensions of a number field `K`. Solved for `K = ℚ` (Kronecker–Weber, roots of
unity) and for imaginary quadratic `K` (complex multiplication), the general case is the
domain of the **Stark conjectures**. Their best-tested instance — the *rank-one abelian
Stark conjecture* — applies precisely when the relevant unit rank is `1`, and predicts that
`L'(0, χ)` is a rational multiple of a single logarithm `log |ε|` of one algebraic unit `ε`,
the **Stark unit**.

This file isolates and machine-checks the *structural* fact that makes that statement
meaningful: in unit rank `1`, the regulator of `K` — in general an `(r × r)` determinant of
logarithms of a fundamental system of units — collapses to a single archimedean logarithm
of the fundamental (Stark) unit `ε`.

It does **not** address the open problem of computing Stark units effectively.

## Main results

* `rank_eq_one_iff_card_infinitePlace_eq_two`: the rank-one Stark hypothesis `rank K = 1`
  is equivalent to `K` having exactly two infinite places — the real quadratic fields
  `(r₁, r₂) = (2, 0)` and the mixed-signature cubics `(r₁, r₂) = (1, 1)`.

* `regulator_eq_single_log_of_rank_eq_one`: when `rank K = 1`, there is an infinite place
  `w` and a unit `ε` (the fundamental Stark unit) with
  `regulator K = mult w * |log (w ε)|` — a single archimedean logarithm.

## Proof strategy

Both results specialize Mathlib's general Dirichlet/regulator machinery.
The rank characterization is `rank K = #(InfinitePlace K) − 1` plus `omega`.
The collapse transports the `Unique (Fin (rank K))` instance (since `rank K = 1`) along
`equivFinRank` to make the place-index type a singleton, then applies `Matrix.det_unique`
to reduce the determinant in `regulator_eq_det` to its single entry.
-/

open NumberField NumberField.Units NumberField.InfinitePlace
open scoped NumberField

namespace KroneckersJugendtraumStarkRankOne

variable (K : Type*) [Field K] [NumberField K]

/-- **Rank one ⟺ two infinite places.**
By Dirichlet's unit theorem the unit rank of `K` is `#(InfinitePlace K) − 1`, so the
rank-one Stark hypothesis `rank K = 1` holds exactly when `K` has two infinite places. -/
theorem rank_eq_one_iff_card_infinitePlace_eq_two :
    rank K = 1 ↔ Fintype.card (InfinitePlace K) = 2 := by
  rw [rank]
  omega

/-- **The rank-one regulator is a single logarithm.**
When `rank K = 1`, the regulator of `K` collapses from a determinant of logarithms to a
single archimedean logarithm `mult w * |log (w ε)|` of the fundamental (Stark) unit
`ε = fundSystem K i`. This is the precise linear-algebra fact behind the rank-one abelian
Stark conjecture's statement that `L'(0, χ)` is a rational multiple of one `log |ε|`. -/
theorem regulator_eq_single_log_of_rank_eq_one (hrank : rank K = 1) :
    ∃ (w : InfinitePlace K) (ε : (𝓞 K)ˣ),
      regulator K = (mult w : ℝ) * |Real.log (w (ε : K))| := by
  classical
  -- `Fin (rank K)` is a singleton because `rank K = 1` …
  haveI huniqFin : Unique (Fin (rank K)) := by rw [hrank]; infer_instance
  -- … and transporting along `equivFinRank` makes the place-index type a singleton too.
  haveI huniq : Unique {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀ K} :=
    (equivFinRank K).symm.unique
  -- The single place and the fundamental (Stark) unit it indexes.
  refine ⟨(default : {w : InfinitePlace K // w ≠ dirichletUnitTheorem.w₀ K}).val,
    fundSystem K ((equivFinRank K).symm default), ?_⟩
  -- Express the regulator as a 1×1 determinant and read off its single entry.
  rw [regulator_eq_det K (dirichletUnitTheorem.w₀ K) (equivFinRank K).symm,
    Matrix.det_unique, Matrix.of_apply, abs_mul, Nat.abs_cast]

end KroneckersJugendtraumStarkRankOne
