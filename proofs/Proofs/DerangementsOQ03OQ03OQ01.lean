/-
# Expected number of fixed points of a random permutation is `1`
  (derangements-oq-03-oq-03-oq-01)

## Open Question (OQ-01 of derangements-oq-03-oq-03)
The parent entry (`derangements-oq-03-oq-03`, *Derangement Permutation Matrices and
the 1/e Law*) packages a uniformly random `n × n` permutation matrix `σ.permMatrix ℝ`
and identifies its **trace** with the number of fixed points of `σ`
(`Matrix.trace_permutation`: `trace (σ.permMatrix ℝ) = (fixedPoints σ).ncard`).  The
derangement side of the story — the probability that the trace is *zero* — converges to
`1/e`.  The parent left open the complementary first-moment question:

> What is the **expected trace** of a random permutation matrix, i.e. the expected
> number of fixed points of a uniformly random permutation of `Fin n`?

## Answer: exactly `1`, for every `n ≥ 1`.

This is the classical "expected number of fixed points = 1" fact.  We prove it not by
linearity of indicators but through the **Cauchy–Frobenius / Burnside count**: summing the
number of fixed points of `σ` over *all* permutations equals the number of orbits of the
permutation action times the order of the group,

  `∑_{σ ∈ Sₙ} |Fix σ|  =  (#orbits) · |Sₙ|`.

The natural action of `Equiv.Perm (Fin n)` on `Fin n` is transitive for `n ≥ 1`, so there is
exactly **one** orbit, and the sum collapses to `1 · n! = n!`.  Dividing by the number of
permutations `|Sₙ| = n!` gives the expected value `1`.

The trace bridge from the parent turns this into a statement about permutation matrices:
the average trace of an `n × n` permutation matrix is `1`.

## Status
- `0` sorries, `0` axioms, no `native_decide`.
- Reuses the parent's `permMatrix`/trace layer and Mathlib's `Matrix.trace_permutation`.
- The only new analytic ingredient is the Burnside count
  `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` specialised to the transitive
  symmetric-group action, plus the orbit-count `= 1` from pretransitivity.
-/

import Mathlib
import Proofs.DerangementsOQ03OQ03

namespace DerangementsOQ03OQ03OQ01

open Equiv (Perm)
open scoped BigOperators

variable {n : ℕ}

/-- The orbit space of the symmetric-group action on `Fin n` is finite (it is a quotient of the
    finite type `Fin n`), so it carries a `Fintype` structure — needed to state the Burnside
    count and its orbit cardinality. -/
noncomputable instance instFintypeOrbitQuotient (n : ℕ) :
    Fintype (MulAction.orbitRel.Quotient (Perm (Fin n)) (Fin n)) :=
  Fintype.ofFinite _

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  The set of points fixed by `σ` *as a group element* is its fixed-point set
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Mathlib group-action notion `MulAction.fixedBy (Fin n) σ` (points moved nowhere by
    the permutation `σ` acting on `Fin n`) coincides with the dynamical fixed-point set
    `Function.fixedPoints σ`.  Both are `{x | σ x = x}`; the only content is unfolding the
    `Equiv.Perm` scalar action `σ • x = σ x`. -/
theorem fixedBy_eq_fixedPoints (σ : Perm (Fin n)) :
    MulAction.fixedBy (Fin n) σ = Function.fixedPoints σ := by
  ext x
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, Function.mem_fixedPoints,
    Function.IsFixedPt]

/-- The number of fixed points, counted with `Set.ncard` (as in the parent's trace formula),
    equals the `Fintype.card` of the group-action fixed set used by Burnside's lemma. -/
theorem ncard_fixedPoints_eq_card_fixedBy (σ : Perm (Fin n)) :
    (Function.fixedPoints σ).ncard = Fintype.card (MulAction.fixedBy (Fin n) σ) := by
  rw [← fixedBy_eq_fixedPoints, Set.ncard_eq_toFinset_card', Set.toFinset_card]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  The symmetric group acts transitively on `Fin n` — a single orbit
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For `n ≥ 1` the natural action of `Sₙ = Perm (Fin n)` on `Fin n` is transitive, hence has
    exactly one orbit. -/
theorem card_orbits_eq_one (n : ℕ) [NeZero n] :
    Fintype.card (MulAction.orbitRel.Quotient (Perm (Fin n)) (Fin n)) = 1 := by
  haveI : Nonempty (Fin n) := ⟨0⟩
  obtain ⟨u⟩ :=
    (MulAction.pretransitive_iff_unique_quotient_of_nonempty (G := Perm (Fin n))
      (α := Fin n)).mp inferInstance
  haveI := u
  exact Fintype.card_unique

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  The Burnside count — total fixed points over all permutations is `n!`
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Total fixed points = `n!`.**  Summed over *all* `n!` permutations of `Fin n`, the number
    of fixed points totals `n!`.  This is the Cauchy–Frobenius (Burnside) count
    `∑_σ |Fix σ| = (#orbits)·|Sₙ|` for the transitive symmetric-group action, where the single
    orbit makes the right side `1 · n! = n!`. -/
theorem sum_card_fixedBy (n : ℕ) [NeZero n] :
    ∑ σ : Perm (Fin n), Fintype.card (MulAction.fixedBy (Fin n) σ) = n.factorial := by
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Perm (Fin n)) (Fin n)
  rw [h, card_orbits_eq_one, one_mul, Fintype.card_perm, Fintype.card_fin]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  Trace bridge and the expected value
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Per-permutation trace = number of fixed points** (as a real number).  Specialisation of
    the parent's `Matrix.trace_permutation` recast through the Burnside fixed-set count. -/
theorem trace_permMatrix_eq_card_fixedBy (σ : Perm (Fin n)) :
    Matrix.trace (σ.permMatrix ℝ) = (Fintype.card (MulAction.fixedBy (Fin n) σ) : ℝ) := by
  rw [Matrix.trace_permutation, ncard_fixedPoints_eq_card_fixedBy]

/-- **Total trace over all permutation matrices = `n!`.**  Summing the trace of `σ.permMatrix ℝ`
    over all `σ ∈ Sₙ` gives `n!` (the Burnside count, transported through the trace bridge). -/
theorem sum_trace_permMatrix (n : ℕ) [NeZero n] :
    ∑ σ : Perm (Fin n), Matrix.trace (σ.permMatrix ℝ) = (n.factorial : ℝ) := by
  calc ∑ σ : Perm (Fin n), Matrix.trace (σ.permMatrix ℝ)
      = ∑ σ : Perm (Fin n), (Fintype.card (MulAction.fixedBy (Fin n) σ) : ℝ) :=
        Finset.sum_congr rfl (fun σ _ => trace_permMatrix_eq_card_fixedBy σ)
    _ = ((∑ σ : Perm (Fin n), Fintype.card (MulAction.fixedBy (Fin n) σ) : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
    _ = (n.factorial : ℝ) := by rw [sum_card_fixedBy]

/-- **Expected trace of a random permutation matrix is `1`.**  Averaging the trace over the
    `|Sₙ| = n!` permutation matrices (each equally likely) yields exactly `1`: the expected
    number of fixed points of a uniformly random permutation of `Fin n` is `1` for every
    `n ≥ 1`.  This is the first-moment companion of the parent's `1/e` derangement law. -/
theorem expected_trace_eq_one (n : ℕ) [NeZero n] :
    (∑ σ : Perm (Fin n), Matrix.trace (σ.permMatrix ℝ)) / (Fintype.card (Perm (Fin n)) : ℝ)
      = 1 := by
  rw [sum_trace_permMatrix, Fintype.card_perm, Fintype.card_fin,
    div_self (by exact_mod_cast Nat.factorial_ne_zero n)]

/-- The same statement with the denominator written explicitly as `n!`. -/
theorem expected_fixed_points_eq_one (n : ℕ) [NeZero n] :
    (∑ σ : Perm (Fin n), (Fintype.card (MulAction.fixedBy (Fin n) σ) : ℝ)) / (n.factorial : ℝ)
      = 1 := by
  rw [← Nat.cast_sum, sum_card_fixedBy, div_self (by exact_mod_cast Nat.factorial_ne_zero n)]

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @fixedBy_eq_fixedPoints
#check @sum_card_fixedBy
#check @sum_trace_permMatrix
#check @expected_trace_eq_one
#check @expected_fixed_points_eq_one

end DerangementsOQ03OQ03OQ01
