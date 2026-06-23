import Mathlib

/-!
# Dyck words are counted by the Catalan numbers

A **Dyck word** of semilength `n` is a sequence of `n` up-steps `U` and `n`
down-steps `D` such that every prefix has at least as many `U`s as `D`s — the
balanced-bracket / lattice-path objects at the heart of enumerative
combinatorics.  Mathlib (`Mathlib/Combinatorics/Enumerative/DyckWord.lean`)
defines `DyckWord`, its `semilength`, and proves the headline counting theorem

  `DyckWord.card_dyckWord_semilength_eq_catalan :`
  `  Fintype.card { p : DyckWord // p.semilength = n } = catalan n`

via a bijection with rooted binary trees on `n` internal nodes.  This is the
*canonical combinatorial meaning* of the Catalan numbers, and it is genuinely
distinct from the sibling gallery entry `catalan-numbers-oq-01`, which is purely
about the arithmetic linear recurrence of `catalan` and never mentions Dyck
words.

What this file adds on top of the bare Mathlib statement:

* **Closed forms.** Combining the count with `catalan_eq_centralBinom_div`
  gives the explicit `C(2n, n) / (n+1)` count, together with its clean
  *division-free* integer form `(n + 1) · (#Dyck words) = centralBinom n`.
* **A length reformulation.** Phrasing the count by total length `2 * n`
  rather than semilength `n`, via the equivalence of the two predicates
  (`2 · semilength = length`).
* **Positivity from an explicit witness.** Mathlib has *no* `catalan_pos`
  lemma.  We supply one combinatorially: the fully nested word `Uⁿ Dⁿ`
  (`nest^[n] 0`) has semilength `n`, so the counted set is nonempty, hence
  `0 < catalan n`.
* **The Segner convolution recurrence, read on the counts themselves.**

Everything is over `ℕ`, fully machine-checked, 0 axioms, 0 sorries, no
`decide` / `native_decide`.
-/

open DyckWord

namespace DyckCatalanCount

/-- **Headline.** The number of Dyck words of semilength `n` is the `n`-th
Catalan number.  This is the combinatorial definition of `catalan`, exposed as
the entry point for this gallery item. -/
theorem card_semilength_eq_catalan (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n :=
  DyckWord.card_dyckWord_semilength_eq_catalan n

/-- **Closed form (with division).** The Dyck-word count equals the central
binomial coefficient divided by `n + 1`, i.e. `C(2n, n) / (n + 1)`. -/
theorem card_semilength_eq_centralBinom_div (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = n.centralBinom / (n + 1) := by
  rw [card_semilength_eq_catalan, catalan_eq_centralBinom_div]

/-- **Closed form (division-free).** The cleanest exact identity: `n + 1` times
the number of Dyck words of semilength `n` is exactly the central binomial
coefficient `C(2n, n)`.  This avoids the `ℕ`-division of the previous corollary
(the division there is exact precisely because of this identity). -/
theorem succ_mul_card_eq_centralBinom (n : ℕ) :
    (n + 1) * Fintype.card { p : DyckWord // p.semilength = n } = n.centralBinom := by
  rw [card_semilength_eq_catalan]
  exact succ_mul_catalan_eq_centralBinom n

/-- **Length reformulation.** Counting Dyck words by their *total length* `2 * n`
gives the same answer as counting by semilength `n`, namely `catalan n`.  The two
defining predicates agree because a Dyck word has length exactly twice its
semilength (`two_mul_semilength_eq_length`).  Stated with `Nat.card` so no
auxiliary `Fintype` instance on the length-indexed set is needed. -/
theorem card_length_eq_catalan (n : ℕ) :
    Nat.card { p : DyckWord // p.toList.length = 2 * n } = catalan n := by
  have e : { p : DyckWord // p.toList.length = 2 * n } ≃
      { p : DyckWord // p.semilength = n } :=
    Equiv.subtypeEquivRight fun p => by
      rw [← DyckWord.two_mul_semilength_eq_length]; omega
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_semilength_eq_catalan]

/-- The fully nested Dyck word `Uⁿ Dⁿ` — obtained by nesting the empty word `n`
times — has semilength `n`.  This is the explicit witness powering positivity. -/
theorem semilength_nest_iterate (n : ℕ) : (DyckWord.nest^[n] 0).semilength = n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', DyckWord.semilength_nest, ih]

/-- **Positivity of the count.** There is always at least one Dyck word of any
given semilength (the fully nested `Uⁿ Dⁿ`), so the counted set is nonempty. -/
theorem card_semilength_pos (n : ℕ) :
    0 < Fintype.card { p : DyckWord // p.semilength = n } := by
  rw [Fintype.card_pos_iff]
  exact ⟨⟨DyckWord.nest^[n] 0, semilength_nest_iterate n⟩⟩

/-- **`catalan n > 0`, proved combinatorially.** Mathlib does not provide a
positivity lemma for `catalan`; here it falls out of the existence of the nested
Dyck word of each semilength. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  rw [← card_semilength_eq_catalan]
  exact card_semilength_pos n

/-- **Segner convolution recurrence, read on the counts.** Splitting a nonempty
Dyck word at its first return to the axis decomposes it into an inside part of
semilength `i` and an outside part of semilength `n - i`; counting both pieces
gives the Catalan recurrence directly in terms of Dyck-word counts. -/
theorem card_semilength_succ (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n + 1 }
      = ∑ i : Fin (n + 1),
          Fintype.card { p : DyckWord // p.semilength = (i : ℕ) }
            * Fintype.card { p : DyckWord // p.semilength = n - (i : ℕ) } := by
  simp_rw [card_semilength_eq_catalan]
  exact catalan_succ n

/-! ### Small-case sanity ladder: `1, 1, 2, 5`. -/

example : Fintype.card { p : DyckWord // p.semilength = 0 } = 1 := by
  rw [card_semilength_eq_catalan, catalan_zero]

example : Fintype.card { p : DyckWord // p.semilength = 1 } = 1 := by
  rw [card_semilength_eq_catalan, catalan_one]

example : Fintype.card { p : DyckWord // p.semilength = 2 } = 2 := by
  rw [card_semilength_eq_catalan, catalan_two]

example : Fintype.card { p : DyckWord // p.semilength = 3 } = 5 := by
  rw [card_semilength_eq_catalan, catalan_three]

end DyckCatalanCount
