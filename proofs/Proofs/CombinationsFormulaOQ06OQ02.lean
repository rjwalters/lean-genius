import Mathlib
import Proofs.CombinationsFigurateTower

/-
# Polynomial Closed Forms for the Figurate Tower from a Single Identity

## Open Question (combinations-formula-oq-06, OQ-02)

The parent entry `combinations-formula-oq-06` formalized the general hockey-stick
identity and read off the triangular closed form `T_n = n(n+1)/2`.  The sibling
`combinations-formula-oq-06-oq-01` (`CombinationsFigurateTower`) packaged the whole
simplicial ladder `S(k, n) = C(n+k-1, k) = multichoose n k` and proved its recurrences
*uniformly in the dimension* `k`, but supplied a **polynomial closed form only for the
triangular case** `S(2, n) = n(n+1)/2` (`S_two_closed`).  Its stated open question asks:

> Can the closed forms for the higher figurate numbers (e.g. tetrahedral
> `n(n+1)(n+2)/6`) be derived inside Lean from the hockey-stick recurrence *without a
> separate induction*, mirroring the `n(n+1)/2` closed form obtained for the triangular
> case?

## Contribution

Yes.  A **single** factorial identity produces the closed form for every rung of the
tower at once, with no per-dimension induction:

  `factorial_mul_S`      —  `k ! * S(k, n) = n^{(k)}`  where `n^{(k)} = n(n+1)⋯(n+k-1)`
                            is the rising factorial `Nat.ascFactorial n k`;
  `factorial_mul_S_prod` —  the same with the rising factorial written explicitly as the
                            product `∏_{i<k} (n + i)`;
  `S_closed`             —  the division form `S(k, n) = n^{(k)} / k !`, valid uniformly.

The bridge is one rewrite: `S(k, n) = multichoose n k = C(n+k-1, k)`
(`Nat.multichoose_eq`) and `Nat.ascFactorial_eq_factorial_mul_choose'` already states
`n^{(k)} = k ! · C(n+k-1, k)`.  So the *entire* content of "the closed form" is a
divisibility fact (`k ! ∣ n^{(k)}`) that Mathlib supplies for free — no induction on `n`
or `k` is performed in this file.

Reading off the low rungs recovers antiquity's named numbers as instances of the one
theorem:

  `triangular_closed_form`  — `S(2, n) = n(n+1)/2`        (recovers the parent / `S_two_closed`)
  `tetrahedral_closed_form` — `S(3, n) = n(n+1)(n+2)/6`    (the open question's target)
  `pentatope_closed_form`   — `S(4, n) = n(n+1)(n+2)(n+3)/24`

Each is `rw [S_closed]` followed by evaluating the finite product and the factorial —
mechanical specialisation, exactly the "mirroring" the question asks for.

## Mathematical Context

The rising factorial `n^{(k)} = n(n+1)⋯(n+k-1)` is `k !` times the multiset coefficient,
so dividing by `k !` turns any figurate number into a degree-`k` polynomial in `n`.
Since the divisibility `k ! ∣ n^{(k)}` is a theorem about all `n, k` simultaneously
(`Nat.factorial_dvd_ascFactorial`), the closed forms for *all* dimensions follow from the
one identity `factorial_mul_S`; the induction that the parent used per dimension is
absorbed once and for all into that Mathlib divisibility lemma.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ06OQ02

open Finset CombinationsFigurateTower

/-- **The single closed-form identity.**  `k !` times the `k`-dimensional figurate number
    is the rising factorial `n^{(k)} = n(n+1)⋯(n+k-1)`:

      `k ! * S(k, n) = Nat.ascFactorial n k`.

    This holds for *every* dimension `k` at once and performs no induction — it is
    `S(k, n) = C(n+k-1, k)` fed into Mathlib's `ascFactorial_eq_factorial_mul_choose'`. -/
theorem factorial_mul_S (k n : ℕ) : k.factorial * S k n = n.ascFactorial k := by
  rw [S_def, Nat.multichoose_eq, ← Nat.ascFactorial_eq_factorial_mul_choose']

/-- The same identity with the rising factorial written out as the finite product
    `∏_{i < k} (n + i)`. -/
theorem factorial_mul_S_prod (k n : ℕ) :
    k.factorial * S k n = ∏ i ∈ range k, (n + i) := by
  rw [factorial_mul_S, Nat.ascFactorial_eq_prod_range]

/-- **The uniform closed form (division form).**  Every figurate number is the rising
    factorial divided by `k !`:  `S(k, n) = n^{(k)} / k !`.  One statement, all dimensions;
    the exactness of the division is Mathlib's `k ! ∣ n^{(k)}`. -/
theorem S_closed (k n : ℕ) : S k n = n.ascFactorial k / k.factorial := by
  rw [← factorial_mul_S k n, Nat.mul_div_cancel_left _ k.factorial_pos]

/-- **Triangular numbers.**  `S(2, n) = n(n+1)/2` — the `k = 2` slice, recovering the
    parent's `triangular_closed_form` (and the sibling's `S_two_closed`) as an instance of
    the single identity. -/
theorem triangular_closed_form (n : ℕ) : S 2 n = n * (n + 1) / 2 := by
  have h : 2 * S 2 n = n * (n + 1) := by
    have hp := factorial_mul_S_prod 2 n
    norm_num [Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial] at hp
    exact hp
  omega

/-- **Tetrahedral numbers.**  `S(3, n) = n(n+1)(n+2)/6` — the open question's headline
    target, obtained by specialising the single identity to `k = 3`. -/
theorem tetrahedral_closed_form (n : ℕ) : S 3 n = n * (n + 1) * (n + 2) / 6 := by
  have h : 6 * S 3 n = n * (n + 1) * (n + 2) := by
    have hp := factorial_mul_S_prod 3 n
    norm_num [Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial] at hp
    exact hp
  omega

/-- **Pentatope (4-simplex) numbers.**  `S(4, n) = n(n+1)(n+2)(n+3)/24` — the next rung,
    showing the closed form continues up the tower with no new induction. -/
theorem pentatope_closed_form (n : ℕ) :
    S 4 n = n * (n + 1) * (n + 2) * (n + 3) / 24 := by
  have h : 24 * S 4 n = n * (n + 1) * (n + 2) * (n + 3) := by
    have hp := factorial_mul_S_prod 4 n
    norm_num [Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial] at hp
    exact hp
  omega

/-- Sanity check: `S(3, 4) = 4·5·6/6 = 20`, the 4th tetrahedral number. -/
example : S 3 4 = 20 := by rw [tetrahedral_closed_form]

/-- Sanity check: `S(4, 3) = 3·4·5·6/24 = 15`, the 3rd pentatope number. -/
example : S 4 3 = 15 := by rw [pentatope_closed_form]

end CombinationsFormulaOQ06OQ02
