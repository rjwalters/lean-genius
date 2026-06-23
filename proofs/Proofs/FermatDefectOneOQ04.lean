/-
  Fermat Defect-One — OQ-04: No Small Witnesses (a verified lower bound on M(n))

  Parent problem (`Proofs.FermatDefectOne`): does the Fermat defect
  $|a^n + b^n - c^n|$ ever equal exactly $1$ for a primitive nontrivial triple
  $2 \le a \le b < c$, $\gcd(a,b,c) = 1$? For $n = 3$ both signs are witnessed
  (`6^3 + 8^3 + 1 = 9^3` and `9^3 + 10^3 = 12^3 + 1`). For $n \ge 4$ existence is
  open, and the competing question (OQ-03) asks whether the minimal defect
  $M(n) := \min |a^n + b^n - c^n|$ over primitive nontrivial triples grows.

  This file (OQ-04) supplies the complementary computational evidence requested
  by the issue: a `decide`-style **no-small-witness** result. For each exponent
  $n \in \{4, 5, 6\}$ we certify, by `native_decide`, that **no** triple with
  $2 \le a \le b < c \le 100$ has defect one (either sign). Equivalently, within
  the box $c \le 100$ the minimal defect satisfies $M(n) \ge 2$ for these $n$.

  Two points make the statement clean:

  * **Primitivity is automatic for defect one.** If $a^n + b^n - c^n = \pm 1$ and
    $d = \gcd(a,b,c)$, then $d^n \mid \pm 1$, so $d = 1$. Hence the box-emptiness
    below is stated WITHOUT a gcd hypothesis (strictly stronger), and the
    primitive-witness corollaries follow immediately.

  * **$n = 3$ is genuinely different.** The box $c \le 100$ already contains the
    witness $(6,8,9)$ at $n = 3$, so the vanishing for $n \ge 4$ is not an
    artifact of the bound — it is an exponent effect (`defect_one_three_in_box`).

  Honesty note: each headline non-existence theorem is discharged by
  `native_decide`, which trusts the compiler's kernel reduction and therefore
  depends on the `Lean.ofReduceBool` axiom. These are finite certificates over a
  bounded box, not a proof of the (open) infinite statement.
-/

import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOne.OQ04

open FermatDefectOne

/-! ## Bounded non-existence of defect one (the `native_decide` core)

For each exponent `n`, the proposition below is a fully bounded statement over
`Nat` (`Nat.decidableBallLT` makes it decidable), checked by `native_decide`.
The shape `∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a → …` enumerates exactly the
admissible triples `2 ≤ a ≤ b < c ≤ 100`. -/

/-- No defect-one equation (either sign) holds at exponent `4` for any triple
with `2 ≤ a ≤ b < c ≤ 100`. -/
theorem no_defect_one_eqn_below_4 :
    ∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a →
      a ^ 4 + b ^ 4 + 1 ≠ c ^ 4 ∧ a ^ 4 + b ^ 4 ≠ c ^ 4 + 1 := by
  native_decide

/-- No defect-one equation (either sign) holds at exponent `5` for any triple
with `2 ≤ a ≤ b < c ≤ 100`. -/
theorem no_defect_one_eqn_below_5 :
    ∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a →
      a ^ 5 + b ^ 5 + 1 ≠ c ^ 5 ∧ a ^ 5 + b ^ 5 ≠ c ^ 5 + 1 := by
  native_decide

/-- No defect-one equation (either sign) holds at exponent `6` for any triple
with `2 ≤ a ≤ b < c ≤ 100`. -/
theorem no_defect_one_eqn_below_6 :
    ∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a →
      a ^ 6 + b ^ 6 + 1 ≠ c ^ 6 ∧ a ^ 6 + b ^ 6 ≠ c ^ 6 + 1 := by
  native_decide

/-! ## Box-emptiness without the primitivity hypothesis (strong form)

Restated with the natural ordering hypotheses up front. No `gcd` condition is
needed: defect one forces primitivity. -/

/-- Strong form, `n = 4`: every triple `2 ≤ a ≤ b < c ≤ 100` has defect `≠ 1`
(both signs), with no primitivity assumption. -/
theorem no_small_defect_one_4 (a b c : Nat)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b < c) (hc : c ≤ 100) :
    a ^ 4 + b ^ 4 + 1 ≠ c ^ 4 ∧ a ^ 4 + b ^ 4 ≠ c ^ 4 + 1 :=
  no_defect_one_eqn_below_4 c (by omega) b hbc a (by omega) ha

/-- Strong form, `n = 5`. -/
theorem no_small_defect_one_5 (a b c : Nat)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b < c) (hc : c ≤ 100) :
    a ^ 5 + b ^ 5 + 1 ≠ c ^ 5 ∧ a ^ 5 + b ^ 5 ≠ c ^ 5 + 1 :=
  no_defect_one_eqn_below_5 c (by omega) b hbc a (by omega) ha

/-- Strong form, `n = 6`. -/
theorem no_small_defect_one_6 (a b c : Nat)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b < c) (hc : c ≤ 100) :
    a ^ 6 + b ^ 6 + 1 ≠ c ^ 6 ∧ a ^ 6 + b ^ 6 ≠ c ^ 6 + 1 :=
  no_defect_one_eqn_below_6 c (by omega) b hbc a (by omega) ha

/-! ## Primitive-witness corollaries (parent `FermatDefectWitness` form)

These specialize the box-emptiness to the parent predicate, certifying that the
defect-one *existence* statement `FermatDefectExists n` has no solution with
`c ≤ 100` for `n ∈ {4, 5, 6}`. -/

/-- No primitive defect-one witness at exponent `4` has `c ≤ 100`. -/
theorem no_small_witness_4 (a b c : Nat) (hc : c ≤ 100) :
    ¬ FermatDefectWitness 4 a b c := by
  rintro ⟨ha, _, hbc, -, hdef⟩
  exact hdef.elim (no_small_defect_one_4 a b c ha (by omega) hbc hc).1
                  (no_small_defect_one_4 a b c ha (by omega) hbc hc).2

/-- No primitive defect-one witness at exponent `5` has `c ≤ 100`. -/
theorem no_small_witness_5 (a b c : Nat) (hc : c ≤ 100) :
    ¬ FermatDefectWitness 5 a b c := by
  rintro ⟨ha, _, hbc, -, hdef⟩
  exact hdef.elim (no_small_defect_one_5 a b c ha (by omega) hbc hc).1
                  (no_small_defect_one_5 a b c ha (by omega) hbc hc).2

/-- No primitive defect-one witness at exponent `6` has `c ≤ 100`. -/
theorem no_small_witness_6 (a b c : Nat) (hc : c ≤ 100) :
    ¬ FermatDefectWitness 6 a b c := by
  rintro ⟨ha, _, hbc, -, hdef⟩
  exact hdef.elim (no_small_defect_one_6 a b c ha (by omega) hbc hc).1
                  (no_small_defect_one_6 a b c ha (by omega) hbc hc).2

/-! ## The `n = 3` contrast

The bound `c ≤ 100` is not what kills the witnesses for `n ≥ 4`: at `n = 3` the
same box already contains one. -/

/-- At `n = 3` the box `c ≤ 100` DOES contain a primitive defect-one witness,
namely `(6, 8, 9)` with `6^3 + 8^3 + 1 = 9^3`. The vanishing for `n ≥ 4` is
therefore an exponent phenomenon, not an artifact of the bound. -/
theorem defect_one_three_in_box :
    ∃ a b c : Nat, c ≤ 100 ∧ FermatDefectWitness 3 a b c :=
  ⟨6, 8, 9, by norm_num, fermat_defect_three_neg⟩

end FermatDefectOne.OQ04
