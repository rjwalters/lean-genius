/-
  **Exact minimality capstone: the smallest odd abundant number coprime to 3 is

      5391411025 = 5² · 7 · 11 · 13 · 17 · 19 · 23 · 29.**

  The open question `abundant-number-oq-02-oq-01` asks for the least element of

      S = { n | Odd n ∧ ¬ (3 ∣ n) ∧ Nat.Abundant n }.

  Two companion results, each proved axiom-free, together pin it down exactly:

  * **Membership (upper bound).**  `AbundantNumberOQ02OQ01.mem_odd_three_free_abundant`
    certifies that `5391411025` itself is odd, coprime to `3`, and abundant
    (`σ(5391411025) = 10799308800 > 10782822050 = 2·5391411025`, assembled from the
    eight tiny prime-power divisor sums via multiplicativity of `σ` — no
    `native_decide`).

  * **Lower bound (minimality).**  `AbundantNumberOQ02OQ01SevenPrimeExponents.`
    `odd_abundant_coprime_three_ge_witness` shows every odd abundant number coprime to
    `3` is `≥ 5391411025`.  This is the hard half: it is assembled from the squarefree
    bound (`≥ 33426748355`), the `ω ≥ 8` bound (`≥ 5391411025`), and the residual `ω = 7`
    analysis (`omega_seven_residual_ge_sharp`, which forces `25 ∣ n` and `49 ∣ n` on the
    four explicit prime supports `{5,7,11,13,17,19,q}`, `q ∈ {23,29,31,37}`, via a sharp
    rational Euler abundancy product).

  Combining them gives `IsLeast S 5391411025` — the complete resolution of the open
  question (both directions), which the individual companion files had only stated
  separately.  At the time `AbundantNumberOQ02OQ01.lean` was written its header still
  recorded minimality as "the open half"; that half is now closed, so this file ties the
  two together into the single headline statement.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01
import Proofs.AbundantNumberOQ02OQ01SevenPrimeExponents

namespace AbundantNumberOQ02OQ01Capstone

open Nat

/-- The set of odd abundant numbers coprime to `3` — the family the open question is about. -/
def OddThreeFreeAbundant : Set ℕ := {n : ℕ | Odd n ∧ ¬ (3 ∣ n) ∧ Nat.Abundant n}

/-- **Lower bound, repackaged.**  `5391411025` is a lower bound for every odd abundant
number coprime to `3` (the minimality half, from `odd_abundant_coprime_three_ge_witness`). -/
theorem witness_mem_lowerBounds :
    5391411025 ∈ lowerBounds OddThreeFreeAbundant := by
  rintro m ⟨hodd, h3, hab⟩
  exact AbundantNumberOQ02OQ01SevenPrimeExponents.odd_abundant_coprime_three_ge_witness
    hodd h3 hab

/-- **Exact minimality (both directions).**  The least odd abundant number coprime to `3`
is exactly `5391411025 = 5²·7·11·13·17·19·23·29`:

    `IsLeast { n | Odd n ∧ ¬ (3 ∣ n) ∧ Nat.Abundant n } 5391411025`.

The membership half is `AbundantNumberOQ02OQ01.mem_odd_three_free_abundant`; the lower-bound
half is `witness_mem_lowerBounds` (built on `odd_abundant_coprime_three_ge_witness`). -/
theorem isLeast_oddThreeFreeAbundant :
    IsLeast OddThreeFreeAbundant 5391411025 :=
  ⟨AbundantNumberOQ02OQ01.mem_odd_three_free_abundant, witness_mem_lowerBounds⟩

/-- **Explicit two-sided statement.**  `5391411025` is in the family, and nothing smaller is:
every odd abundant number coprime to `3` is `≥ 5391411025`, with equality attained. -/
theorem smallest_odd_abundant_coprime_three :
    (Odd 5391411025 ∧ ¬ (3 ∣ 5391411025) ∧ Nat.Abundant 5391411025) ∧
    (∀ m : ℕ, Odd m → ¬ (3 ∣ m) → Nat.Abundant m → 5391411025 ≤ m) :=
  ⟨AbundantNumberOQ02OQ01.mem_odd_three_free_abundant,
   fun _ hodd h3 hab =>
     AbundantNumberOQ02OQ01SevenPrimeExponents.odd_abundant_coprime_three_ge_witness hodd h3 hab⟩

#check @isLeast_oddThreeFreeAbundant

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms isLeast_oddThreeFreeAbundant

end AbundantNumberOQ02OQ01Capstone
