/-
  Bracketing the Product of Successive Minima by the Extreme Minima
  (minkowski-fundamental-theorem-oq-01-oq-01)

  Next step of `minkowski-fundamental-theorem-oq-01` (which built the successive
  minima infrastructure and stated, but left open, Minkowski's second theorem
  product bound `λ₀ λ₁ ⋯ λₙ₋₁ · vol(S) ≤ 2ⁿ · covolume(L)`).

  The parent file proved the *order structure* of the successive minima
  (`λ₀ ≤ λ₁ ≤ ⋯ ≤ λₙ₋₁`, when the minima are attained).  Here we turn that order
  structure into a quantitative statement about the **product** that appears in
  the second theorem: the geometric content of monotonicity is the bracketing

      λ₀ⁿ  ≤  ∏ᵢ λᵢ  ≤  λₙ₋₁ⁿ.

  In words: the geometric mean of the successive minima lies between the smallest
  and the largest minimum (stated in `n`-th power form to stay over ℝ and avoid
  real `n`-th roots).

  The payoff is that the deep, still-open product bound collapses to *single-
  minimum* bounds once it is granted.  Concretely:

  * If the second theorem upper bound holds, then  `λ₀ⁿ · vol(S) ≤ 2ⁿ covolume(L)`
    — a bound on the *first* minimum alone (`firstMinimum_pow_volume_le_*`).
  * If the second theorem lower bound holds, then
    `(2ⁿ/n!) covolume(L) ≤ λₙ₋₁ⁿ · vol(S)` — a bound on the *last* minimum alone
    (`lower_le_lastMinimum_pow_volume_*`).

  Everything here is proved with 0 sorries and 0 axioms, on top of the parent's
  custom `Lattice`/`ConvexBody` API.  The hypothesis throughout is that the
  successive minima are attained — formalised as the (smallest) admissible
  scaling set, that of the top index, being non-empty; by antitonicity this makes
  every admissible scaling set non-empty and hence the full chain λ₀ ≤ ⋯ ≤ λₙ₋₁
  available.

  HONEST SCOPE: the second theorem's product bound itself is NOT proved (its
  proof is the open analytic core requiring a basis realizing the minima).  What
  is delivered is the bracketing of the product by the extreme minima and the
  resulting reduction of the open bound to single-minimum statements.

  References:
  - Minkowski, Geometrie der Zahlen (1896)
  - Cassels, An Introduction to the Geometry of Numbers (1959), Ch. VIII
-/
import Mathlib
import Proofs.MinkowskiFundamentalTheorem
import Proofs.MinkowskiFundamentalTheoremOQ01

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace MinkowskiSecondTheoremBracket

open MinkowskiFundamentalTheorem MinkowskiSecondTheorem Set
open scoped Pointwise

variable (n : ℕ) [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE EXTREME INDICES OF `Fin n`
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The bottom index `0` of `Fin n` (well-defined since `n ≠ 0`). -/
def botIndex : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- The top index `n - 1` of `Fin n` (well-defined since `n ≠ 0`). -/
def topIndex : Fin n := ⟨n - 1, by have h := Nat.pos_of_ne_zero (NeZero.ne n); omega⟩

/-- The bottom index is below every index. -/
theorem botIndex_le (i : Fin n) : botIndex n ≤ i := by
  rw [Fin.le_def]; exact Nat.zero_le _

/-- The top index is above every index. -/
theorem le_topIndex (i : Fin n) : i ≤ topIndex n := by
  rw [Fin.le_def]
  have h := i.isLt
  show i.val ≤ n - 1
  omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: ATTAINMENT OF THE MINIMA AND THE FULL ORDER CHAIN
═══════════════════════════════════════════════════════════════════════════════ -/

/-- If the admissible-scaling set of the **top** index is non-empty, then so is
    the admissible-scaling set of every index (the top set is the smallest, by
    antitonicity of `admissibleScalings`). -/
theorem admissibleScalings_nonempty (L : Lattice n) (S : ConvexBody n)
    (h : (admissibleScalings n L S (topIndex n)).Nonempty) (i : Fin n) :
    (admissibleScalings n L S i).Nonempty :=
  h.mono (admissibleScalings_subset n L S (le_topIndex n i))

/-- Under attainment, the first minimum is a lower bound for every minimum:
    `λ₀ ≤ λᵢ`. -/
theorem firstMinimum_le (L : Lattice n) (S : ConvexBody n)
    (h : (admissibleScalings n L S (topIndex n)).Nonempty) (i : Fin n) :
    successiveMinimum n L S (botIndex n) ≤ successiveMinimum n L S i :=
  successiveMinimum_mono n L S (botIndex_le n i) (admissibleScalings_nonempty n L S h i)

/-- Under attainment, the last minimum is an upper bound for every minimum:
    `λᵢ ≤ λₙ₋₁`. -/
theorem le_lastMinimum (L : Lattice n) (S : ConvexBody n)
    (h : (admissibleScalings n L S (topIndex n)).Nonempty) (i : Fin n) :
    successiveMinimum n L S i ≤ successiveMinimum n L S (topIndex n) :=
  successiveMinimum_mono n L S (le_topIndex n i) h

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE PRODUCT, NON-NEGATIVE AND BRACKETED BY THE EXTREME MINIMA
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The product of the successive minima is non-negative. -/
theorem prod_successiveMinimum_nonneg (L : Lattice n) (S : ConvexBody n) :
    0 ≤ ∏ i : Fin n, successiveMinimum n L S i :=
  Finset.prod_nonneg (fun i _ => successiveMinimum_nonneg n L S i)

/-- **Lower bracket.**  The product of the successive minima dominates the
    `n`-th power of the first minimum: `λ₀ⁿ ≤ ∏ᵢ λᵢ`. -/
theorem firstMinimum_pow_le_prod (L : Lattice n) (S : ConvexBody n)
    (h : (admissibleScalings n L S (topIndex n)).Nonempty) :
    (successiveMinimum n L S (botIndex n)) ^ n ≤ ∏ i : Fin n, successiveMinimum n L S i := by
  have hconst : (successiveMinimum n L S (botIndex n)) ^ n
      = ∏ _i : Fin n, successiveMinimum n L S (botIndex n) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hconst]
  exact Finset.prod_le_prod (fun i _ => successiveMinimum_nonneg n L S (botIndex n))
    (fun i _ => firstMinimum_le n L S h i)

/-- **Upper bracket.**  The product of the successive minima is dominated by the
    `n`-th power of the last minimum: `∏ᵢ λᵢ ≤ λₙ₋₁ⁿ`. -/
theorem prod_le_lastMinimum_pow (L : Lattice n) (S : ConvexBody n)
    (h : (admissibleScalings n L S (topIndex n)).Nonempty) :
    ∏ i : Fin n, successiveMinimum n L S i ≤ (successiveMinimum n L S (topIndex n)) ^ n := by
  have hconst : (successiveMinimum n L S (topIndex n)) ^ n
      = ∏ _i : Fin n, successiveMinimum n L S (topIndex n) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hconst]
  exact Finset.prod_le_prod (fun i _ => successiveMinimum_nonneg n L S i)
    (fun i _ => le_lastMinimum n L S h i)

/-- **The bracketing, combined.**  `λ₀ⁿ ≤ ∏ᵢ λᵢ ≤ λₙ₋₁ⁿ`. -/
theorem extremeMinima_bracket (L : Lattice n) (S : ConvexBody n)
    (h : (admissibleScalings n L S (topIndex n)).Nonempty) :
    (successiveMinimum n L S (botIndex n)) ^ n ≤ ∏ i : Fin n, successiveMinimum n L S i
      ∧ ∏ i : Fin n, successiveMinimum n L S i ≤ (successiveMinimum n L S (topIndex n)) ^ n :=
  ⟨firstMinimum_pow_le_prod n L S h, prod_le_lastMinimum_pow n L S h⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: COLLAPSING THE SECOND THEOREM TO SINGLE-MINIMUM BOUNDS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The lower bound of Minkowski's second theorem, stated precisely:
    `(2ⁿ/n!) · covolume(L) ≤ λ₀ ⋯ λₙ₋₁ · vol(S)`.  Stated as a scaffold (the
    companion to the parent's `secondTheorem_upper_statement`); its proof is part
    of the open analytic core. -/
def secondTheorem_lower_statement (L : Lattice n) (S : ConvexBody n) [hv : HasVolume n S] : Prop :=
  ((2 : ℝ) ^ n / n.factorial) * L.covolume ≤ (∏ i : Fin n, successiveMinimum n L S i) * hv.volume

/-- **First-minimum consequence of the second theorem's upper bound.**
    Granting the (open) product bound `∏ᵢ λᵢ · vol(S) ≤ 2ⁿ covolume(L)`, the
    lower bracket `λ₀ⁿ ≤ ∏ᵢ λᵢ` collapses it to a bound on the first minimum
    alone:  `λ₀ⁿ · vol(S) ≤ 2ⁿ covolume(L)`. -/
theorem firstMinimum_pow_volume_le_of_secondTheorem (L : Lattice n) (S : ConvexBody n)
    [hv : HasVolume n S] (h : (admissibleScalings n L S (topIndex n)).Nonempty)
    (h_second : secondTheorem_upper_statement n L S) :
    (successiveMinimum n L S (botIndex n)) ^ n * hv.volume ≤ (2 : ℝ) ^ n * L.covolume := by
  have hstep : (successiveMinimum n L S (botIndex n)) ^ n * hv.volume
      ≤ (∏ i : Fin n, successiveMinimum n L S i) * hv.volume :=
    mul_le_mul_of_nonneg_right (firstMinimum_pow_le_prod n L S h) (le_of_lt hv.volume_pos)
  have h2 : (∏ i : Fin n, successiveMinimum n L S i) * hv.volume ≤ (2 : ℝ) ^ n * L.covolume :=
    h_second
  exact le_trans hstep h2

/-- **Last-minimum consequence of the second theorem's lower bound.**
    Granting the (open) lower bound `(2ⁿ/n!) covolume(L) ≤ ∏ᵢ λᵢ · vol(S)`, the
    upper bracket `∏ᵢ λᵢ ≤ λₙ₋₁ⁿ` collapses it to a bound on the last minimum
    alone:  `(2ⁿ/n!) covolume(L) ≤ λₙ₋₁ⁿ · vol(S)`. -/
theorem lower_le_lastMinimum_pow_volume_of_secondTheorem (L : Lattice n) (S : ConvexBody n)
    [hv : HasVolume n S] (h : (admissibleScalings n L S (topIndex n)).Nonempty)
    (h_lower : secondTheorem_lower_statement n L S) :
    ((2 : ℝ) ^ n / n.factorial) * L.covolume
      ≤ (successiveMinimum n L S (topIndex n)) ^ n * hv.volume := by
  have hstep : (∏ i : Fin n, successiveMinimum n L S i) * hv.volume
      ≤ (successiveMinimum n L S (topIndex n)) ^ n * hv.volume :=
    mul_le_mul_of_nonneg_right (prod_le_lastMinimum_pow n L S h) (le_of_lt hv.volume_pos)
  have h1 : ((2 : ℝ) ^ n / n.factorial) * L.covolume
      ≤ (∏ i : Fin n, successiveMinimum n L S i) * hv.volume := h_lower
  exact le_trans h1 hstep

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## Bracketing the product of successive minima  (oq-01-oq-01)

### What's proved (0 sorries, 0 axioms):
- `botIndex`, `topIndex` with `botIndex_le`, `le_topIndex`: the extreme indices
  of `Fin n` and their order positions.
- `admissibleScalings_nonempty`: attainment of the top minimum propagates to all
  minima (top admissible set ⊆ every admissible set).
- `firstMinimum_le` / `le_lastMinimum`: the full order chain λ₀ ≤ λᵢ ≤ λₙ₋₁.
- `prod_successiveMinimum_nonneg`: the product is non-negative.
- `firstMinimum_pow_le_prod` / `prod_le_lastMinimum_pow` / `extremeMinima_bracket`:
  the bracketing `λ₀ⁿ ≤ ∏ᵢ λᵢ ≤ λₙ₋₁ⁿ`.
- `firstMinimum_pow_volume_le_of_secondTheorem`: the second theorem's upper bound
  ⟹ `λ₀ⁿ · vol(S) ≤ 2ⁿ covolume(L)`.
- `lower_le_lastMinimum_pow_volume_of_secondTheorem`: the second theorem's lower
  bound ⟹ `(2ⁿ/n!) covolume(L) ≤ λₙ₋₁ⁿ · vol(S)`.

### Honest scope:
The product bound of Minkowski's second theorem is NOT proved here (it is the
open analytic core).  What is delivered is the order-theoretic bracketing of the
product by the extreme minima, and the reduction of the open product bound to
single-minimum statements.
-/

#check @botIndex
#check @topIndex
#check @firstMinimum_pow_le_prod
#check @prod_le_lastMinimum_pow
#check @extremeMinima_bracket
#check @firstMinimum_pow_volume_le_of_secondTheorem
#check @lower_le_lastMinimum_pow_volume_of_secondTheorem

end MinkowskiSecondTheoremBracket
