/-
  A quantitative lower bound on the counting function of ODD abundant numbers.

  A positive integer `n` is *abundant* when `σ(n) > 2n` (Mathlib's
  `Nat.Abundant`). The smallest odd abundant number is `945 = 3³·5·7`, and the
  sibling entry `AbundantOddInfiniteOQ03.lean` proves there are infinitely many
  odd abundant numbers by exhibiting the family

      945·1, 945·3, 945·5, 945·7, …  =  945·(2k+1)

  of odd abundant witnesses. Infinitude is a *qualitative* statement. This file
  answers the parent entry's SECOND open question by turning it into a
  *quantitative* lower bound on the counting function

      A(x) := #{ n ∈ [1, x] : n is odd and abundant }.

  The same odd-multiples family gives, for every `x`,

      x  <  1890 · A(x) + 945,

  equivalently `A(x) > x/1890 − 1/2`: the odd abundant numbers have positive
  lower density, at least `1/1890`. The witnesses `945·(2k+1)` with
  `2k+1 ≤ x/945` are `⌈(x/945)/2⌉ ≥ x/1890 − 1/2` distinct odd abundant numbers
  in `[1, x]`, and the map `k ↦ 945·(2k+1)` is injective, so they inject into
  the counted set.

  The constant `1/1890` is the density of the odd multiples of `945` and is not
  optimal (accounting for the other odd abundant seeds `1575`, `2205`, … and
  their overlaps would raise it); it is the honest bound obtained from the single
  seed `945`. The proof is axiom-free (no `sorry`, no `axiom`, no
  `native_decide`): it reuses the parent's `odd_abundant_945_mul` and
  `odd_mul_succ_injective`, an injective-image cardinality bound
  (`Finset.card_image_of_injective` + `Finset.card_le_card`), and `omega` for
  the division arithmetic.
-/
import Mathlib
import Proofs.AbundantOddInfiniteOQ03

namespace AbundantOddCountingOQ0302

open AbundantOddInfiniteOQ03

-- `Nat.Abundant` carries no registered `Decidable` instance, so the counting
-- filter below is defined classically. This only affects computability, not the
-- logical content: `#print axioms` still lists only the standard foundational
-- axioms (propext, Classical.choice, Quot.sound), never `sorryAx` or
-- `Lean.ofReduceBool`.
open Classical

/-- The counting function of odd abundant numbers up to `x`:
`A(x) = #{ n ∈ [1, x] : Odd n ∧ n.Abundant }`. -/
noncomputable def countOddAbundant (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => Odd n ∧ n.Abundant)).card

/-- **Quantitative lower bound on the odd-abundant counting function.**

For every `x`,

  `x < 1890 · countOddAbundant x + 945`,

i.e. the number of odd abundant integers in `[1, x]` is at least `x/1890 − 1/2`.

The proof injects the odd-multiples family `k ↦ 945·(2k+1)` restricted to
`k < (x/945 + 1)/2`. Each such witness is odd and abundant (`odd_abundant_945_mul`)
and lies in `[1, x]` because `2k+1 ≤ x/945`, so `945·(2k+1) ≤ 945·(x/945) ≤ x`.
The map is injective (`odd_mul_succ_injective`), so `(x/945 + 1)/2 ≤ countOddAbundant x`;
the closing inequality is division arithmetic (`omega`). -/
theorem odd_abundant_counting_lower_bound (x : ℕ) :
    x < 1890 * countOddAbundant x + 945 := by
  set M := x / 945 with hM
  set K := (M + 1) / 2 with hK
  -- The odd-multiples family `k ↦ 945·(2k+1)`, restricted to `k < K`, injects
  -- `Finset.range K` into the counted set. We realise it as an image.
  have hsub :
      (Finset.range K).image (fun k => 945 * (2 * k + 1)) ⊆
        (Finset.Icc 1 x).filter (fun n => Odd n ∧ n.Abundant) := by
    rw [Finset.image_subset_iff]
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨hodd, habun⟩ := odd_abundant_945_mul k
    rw [Finset.mem_filter, Finset.mem_Icc]
    -- `945·(2k+1) ≤ x`: from `k < K = (x/945+1)/2` and `945·(x/945) ≤ x`.
    exact ⟨⟨by omega, by omega⟩, hodd, habun⟩
  have hcardimg : ((Finset.range K).image (fun k => 945 * (2 * k + 1))).card = K := by
    rw [Finset.card_image_of_injective _ odd_mul_succ_injective, Finset.card_range]
  have hinj : K ≤ countOddAbundant x := by
    have h1 : ((Finset.range K).image (fun k => 945 * (2 * k + 1))).card
        ≤ countOddAbundant x := Finset.card_le_card hsub
    rwa [hcardimg] at h1
  -- Division arithmetic: `x < 945·(x/945) + 945` and `x/945 ≤ 2·((x/945+1)/2)`.
  omega

/-- **Positive lower density of the odd abundant numbers.**

Recasting `odd_abundant_counting_lower_bound` over `ℝ`: for every `x`,

  `x / 1890 − 1/2 < countOddAbundant x`.

So the odd abundant numbers have lower density at least `1/1890` — a positive
constant. This is the quantitative strengthening of the parent's infinitude
result `infinitely_many_odd_abundant`. -/
theorem odd_abundant_density_lower (x : ℕ) :
    (x : ℝ) / 1890 - 1 / 2 < countOddAbundant x := by
  have h := odd_abundant_counting_lower_bound x
  have hR : (x : ℝ) < 1890 * (countOddAbundant x : ℝ) + 945 := by exact_mod_cast h
  linarith

-- Confirms the result depends only on the standard foundational axioms
-- (propext, Classical.choice, Quot.sound) and NOT on `Lean.ofReduceBool`
-- (which `native_decide` would introduce) or `sorryAx`: the proof is axiom-free.
#print axioms odd_abundant_counting_lower_bound
#print axioms odd_abundant_density_lower

end AbundantOddCountingOQ0302
