import Mathlib
import Proofs.AlgebraicNumbersCountableOQ05

/-
# Algebraic Numbers Countable — OQ-05-OQ-01: An Explicit Height-Stratum Bound

## Open Question (algebraic-numbers-countable-oq-05-oq-01)

Can we make Cantor's height enumeration **explicit**? That is, produce a *computable*
bijection `ℕ ↔ (real algebraic numbers)` driven by the height function. The construction
enumerates, height by height, the finitely many algebraic reals of each height; a genuine
computable enumeration needs to know *how many* live in each stratum, and to bound the work
done at each stage.

## What this file adds over the parent `AlgebraicNumbersCountableOQ05`

The parent proves each height stratum is **finite** (`finite_polys_of_height`) — abstractly,
as the range of a reconstruction map. To make the enumeration *explicit* we need a concrete
**quantitative** handle: an a-priori closed-form bound on the size of each stratum.

This file supplies exactly that, at the polynomial level:

> **`ncard_boundedHeight_le`** — the number of integer polynomials of Cantor height `≤ h`
> is at most `(2h+1)^(h+1)`.

The bound is the explicit count of the coefficient grid: a height-`≤h` polynomial has degree
`≤ h` (so at most `h+1` coefficients) and every coefficient lies in `{-h, …, h}` (a set of
`2h+1` integers). Hence the polynomial is pinned down by a point of the finite grid
`{-h,…,h}^{h+1}`, of which there are `(2h+1)^(h+1)`. We realise this as an explicit injection
`encHeight` into `Fin (h+1) → Fin (2h+1)` and read off the cardinality bound.

This is the first quantitative ingredient of an explicit height enumeration: it says the
stratum-`h` search terminates after inspecting at most `(2h+1)^(h+1)` candidate polynomials.

## Status

Explicit polynomial-stratum bound: complete, 0 sorries, 0 axioms. The full computable
bijection `ℕ ↔ algebraic reals` (assembling the strata in order and deduplicating shared
roots) remains open future work.
-/

namespace AlgebraicNumbersCountableOQ05OQ01

open Polynomial AlgebraicNumbersCountableOQ05

/-- **Explicit grid encoding of a bounded-height polynomial.** A polynomial of Cantor height
`≤ h` is sent to the tuple of its first `h+1` coefficients, each shifted into `Fin (2h+1)`
via `c ↦ (c + h).toNat` (well-defined because `|c| ≤ h`, so `c + h ∈ {0,…,2h}`). -/
def encHeight (h : ℕ) (x : {p : Polynomial ℤ // cantorHeight p ≤ h}) :
    Fin (h + 1) → Fin (2 * h + 1) :=
  fun i => ⟨(x.1.coeff i.val + (h : ℤ)).toNat, by
    have hb : (x.1.coeff i.val).natAbs ≤ h := cantorHeight_coeff_le x.2 i.val
    omega⟩

/-- The grid encoding is **injective**: a height-`≤h` polynomial is determined by its first
`h+1` coefficients (all higher coefficients vanish, since the degree is `≤ h`), and the shift
`c ↦ (c + h).toNat` is injective on `{-h,…,h}`. -/
theorem encHeight_injective (h : ℕ) : Function.Injective (encHeight h) := by
  intro x y hxy
  apply Subtype.ext
  ext n
  by_cases hn : n ≤ h
  · have hval := congrArg Fin.val (congrFun hxy ⟨n, Nat.lt_succ_of_le hn⟩)
    simp only [encHeight] at hval
    have hbp : (x.1.coeff n).natAbs ≤ h := cantorHeight_coeff_le x.2 n
    have hbq : (y.1.coeff n).natAbs ≤ h := cantorHeight_coeff_le y.2 n
    omega
  · rw [coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (cantorHeight_degree_le x.2) (by omega : h < n)),
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (cantorHeight_degree_le y.2) (by omega : h < n))]

/-- **Explicit height-stratum bound.** The number of integer polynomials of Cantor height
`≤ h` is at most `(2h+1)^(h+1)`: each is a point of the coefficient grid `{-h,…,h}^{h+1}`. -/
theorem ncard_boundedHeight_le (h : ℕ) :
    {p : Polynomial ℤ | cantorHeight p ≤ h}.ncard ≤ (2 * h + 1) ^ (h + 1) := by
  rw [← Nat.card_coe_set_eq]
  calc Nat.card ↥{p : Polynomial ℤ | cantorHeight p ≤ h}
      ≤ Nat.card (Fin (h + 1) → Fin (2 * h + 1)) :=
        Nat.card_le_card_of_injective _ (encHeight_injective h)
    _ = (2 * h + 1) ^ (h + 1) := by
        simp [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
          Finset.card_univ]

end AlgebraicNumbersCountableOQ05OQ01
