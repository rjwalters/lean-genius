import Mathlib

/-!
# Denumerability of Rationals OQ-07: the algebraic reals as a `Σ` over `ℚ[X]`

OQ-06 isolated the cardinal fact behind algebraic countability: the polynomial
ring is countably infinite, `#(ℚ[X]) = ℵ₀`.  This entry turns that fact into the
*explicit* mechanism that makes the **algebraic real numbers** countable.

The gallery already records `#{x : ℝ // IsAlgebraic ℚ x} = ℵ₀` once, but only as a
black-box one-liner (`Algebraic.cardinalMk_of_countable_of_charZero`).  What is
*not* recorded anywhere is the structural reason: every algebraic real is a root of
some `p ∈ ℚ[X]`, each such `p` has only finitely many roots, and there are only
`ℵ₀`-many polynomials.  Concretely there is an injection

`{x : ℝ // IsAlgebraic ℚ x}  ↪  Σ p : ℚ[X], (p.rootSet ℝ)`            (sending `x ↦ (minpoly ℚ x, x)`),

and the right-hand `Σ` is a countable union (indexed by `ℚ[X]`, an `ℵ₀` set) of the
*finite* root fibers `p.rootSet ℝ`, hence itself has cardinality `≤ ℵ₀`.

This file makes both halves explicit:

* `cardinalMk_sigma_rootSet_le` : `#(Σ p : ℚ[X], p.rootSet ℝ) ≤ ℵ₀`
  — the finite-fiber/`ℵ₀`-many-polynomials count, feeding `#(ℚ[X]) = ℵ₀` (OQ-06).
* `algebraicReal_inject_sigma` : the injection of the algebraic reals into that `Σ`.
* `cardinalMk_algebraic_reals_le_sigma` : `#{x // IsAlgebraic ℚ x} ≤ #(Σ …)`.
* `cardinalMk_algebraic_reals` : `#{x : ℝ // IsAlgebraic ℚ x} = ℵ₀`, derived from the
  explicit `Σ` bound together with the lower bound `ℵ₀ ≤ #(algebraic reals)`.

The same `Σ`-over-`ℚ[X]` decomposition works verbatim for `ℂ`; we record the complex
count as well.  No axioms beyond Lean's foundational core, no sorries.
-/

namespace DenumerabilityRationalsOQ07

open Cardinal Polynomial

/-- **`#(ℚ[X]) = ℵ₀`** (the OQ-06 fact, reproved inline so this entry is standalone).
By `Polynomial.cardinalMk_eq_max`, `#(ℚ[X]) = max #ℚ ℵ₀`, and `#ℚ = ℵ₀`. -/
theorem cardinalMk_polynomial_rat : #(ℚ[X]) = ℵ₀ := by
  rw [Polynomial.cardinalMk_eq_max, mk_eq_aleph0 ℚ, max_self]

/-- The `Σ`-over-`ℚ[X]` of root fibers in a field `K` algebraic-friendly over `ℚ`
has cardinality `≤ ℵ₀`: it is a sum, indexed by the countable set `ℚ[X]`, of the
**finite** root sets `p.rootSet K`.  This is the structural count behind algebraic
countability. -/
theorem cardinalMk_sigma_rootSet_le
    (K : Type) [Field K] [CharZero K] :
    #(Σ p : ℚ[X], (p.rootSet K)) ≤ ℵ₀ := by
  -- `#(Σ p, p.rootSet K) = ∑_{p : ℚ[X]} #(p.rootSet K)`.
  rw [mk_sigma]
  -- Each fiber is finite, so `#(p.rootSet K) ≤ ℵ₀`; bound the sum by the constant `ℵ₀`.
  calc
    (sum fun p : ℚ[X] => #(p.rootSet K))
        ≤ sum fun _ : ℚ[X] => ℵ₀ :=
          sum_le_sum _ _ fun p => ((p.rootSet_finite K).lt_aleph0).le
    _ = #(ℚ[X]) * ℵ₀ := sum_const' _ _
    _ = ℵ₀ * ℵ₀ := by rw [cardinalMk_polynomial_rat]
    _ = ℵ₀ := aleph0_mul_aleph0

/-- The injection of algebraic reals into the `Σ`-over-`ℚ[X]`: an algebraic `x`
is a root of its minimal polynomial `minpoly ℚ x`, so `x ↦ (minpoly ℚ x, x)` lands in
the fiber over `minpoly ℚ x` and is injective (the second coordinate recovers `x`). -/
theorem algebraicReal_inject_sigma :
    ∃ f : {x : ℝ // IsAlgebraic ℚ x} → Σ p : ℚ[X], (p.rootSet ℝ),
      Function.Injective f := by
  refine ⟨fun x => ⟨minpoly ℚ (x : ℝ), (x : ℝ), ?_⟩, ?_⟩
  · -- `x ∈ (minpoly ℚ x).rootSet ℝ`.
    have hInt : IsIntegral ℚ (x : ℝ) := (isAlgebraic_iff_isIntegral.mp x.2)
    exact mem_rootSet.mpr ⟨minpoly.ne_zero hInt, minpoly.aeval ℚ (x : ℝ)⟩
  · -- Injective: the underlying real value is recovered from the second coordinate.
    intro a b h
    have h2 := congrArg (fun s : Σ p : ℚ[X], (p.rootSet ℝ) => (s.2 : ℝ)) h
    exact Subtype.ext h2

/-- `#{x : ℝ // IsAlgebraic ℚ x} ≤ #(Σ p : ℚ[X], p.rootSet ℝ)` from the injection. -/
theorem cardinalMk_algebraic_reals_le_sigma :
    #{x : ℝ // IsAlgebraic ℚ x} ≤ #(Σ p : ℚ[X], (p.rootSet ℝ)) := by
  obtain ⟨f, hf⟩ := algebraicReal_inject_sigma
  exact mk_le_of_injective hf

/-- **Lower bound `ℵ₀ ≤ #{x : K // IsAlgebraic ℚ x}`** for any characteristic-zero
field `K`: the natural numbers inject into the algebraic elements via `n ↦ (n : K)`
(each natural is algebraic, being a root of `X - n`), and `Nat.cast` is injective in
characteristic zero, so `ℵ₀ = #ℕ ≤ #(algebraic elements)`. -/
theorem aleph0_le_cardinalMk_algebraic
    (K : Type) [Field K] [CharZero K] :
    ℵ₀ ≤ #{x : K // IsAlgebraic ℚ x} := by
  rw [← mk_nat]
  refine mk_le_of_injective (f := fun n : ℕ => ⟨(n : K), isAlgebraic_nat n⟩) ?_
  intro a b h
  have h2 : (a : K) = (b : K) :=
    congrArg (fun s : {x : K // IsAlgebraic ℚ x} => (s : K)) h
  exact_mod_cast h2

/-- **The algebraic reals are countable through the explicit `Σ`-over-`ℚ[X]`:**
`#{x : ℝ // IsAlgebraic ℚ x} ≤ ℵ₀`. -/
theorem cardinalMk_algebraic_reals_le :
    #{x : ℝ // IsAlgebraic ℚ x} ≤ ℵ₀ :=
  cardinalMk_algebraic_reals_le_sigma.trans (cardinalMk_sigma_rootSet_le ℝ)

/-- **`#{x : ℝ // IsAlgebraic ℚ x} = ℵ₀`.** The explicit `Σ` bound gives `≤ ℵ₀`; the
algebraic reals contain `ℚ` (indeed all of `ℕ`), giving the reverse `ℵ₀ ≤`. -/
theorem cardinalMk_algebraic_reals :
    #{x : ℝ // IsAlgebraic ℚ x} = ℵ₀ :=
  le_antisymm cardinalMk_algebraic_reals_le (aleph0_le_cardinalMk_algebraic ℝ)

/-- The complex algebraic numbers satisfy the same `Σ`-over-`ℚ[X]` bound. -/
theorem cardinalMk_algebraic_complex_le :
    #{x : ℂ // IsAlgebraic ℚ x} ≤ ℵ₀ := by
  -- Same injection (into the complex root fibers) and the same finite-fiber count.
  have hsig :
      #{x : ℂ // IsAlgebraic ℚ x} ≤ #(Σ p : ℚ[X], (p.rootSet ℂ)) := by
    refine mk_le_of_injective (f := fun x => ⟨minpoly ℚ (x : ℂ), (x : ℂ), ?_⟩) ?_
    · have hInt : IsIntegral ℚ (x : ℂ) := (isAlgebraic_iff_isIntegral.mp x.2)
      exact mem_rootSet.mpr ⟨minpoly.ne_zero hInt, minpoly.aeval ℚ (x : ℂ)⟩
    · intro a b h
      have h2 := congrArg (fun s : Σ p : ℚ[X], (p.rootSet ℂ) => (s.2 : ℂ)) h
      exact Subtype.ext h2
  exact hsig.trans (cardinalMk_sigma_rootSet_le ℂ)

/-- **`#{x : ℂ // IsAlgebraic ℚ x} = ℵ₀`.** -/
theorem cardinalMk_algebraic_complex :
    #{x : ℂ // IsAlgebraic ℚ x} = ℵ₀ :=
  le_antisymm cardinalMk_algebraic_complex_le (aleph0_le_cardinalMk_algebraic ℂ)

end DenumerabilityRationalsOQ07
