/-
  Fermat Defect-One — OQ-03: does the minimal defect M(n) grow with n?

  Parent problem (`Proofs.FermatDefectOne`): does the Fermat defect
  $|a^n + b^n - c^n|$ ever equal exactly $1$ for a primitive nontrivial triple
  $2 \le a \le b < c$, $\gcd(a,b,c) = 1$?  At $n = 3$ both signs are witnessed;
  for $n \ge 4$ existence is open.  OQ-03 asks the *quantitative* companion
  question: does the **minimal defect**

  $$M(n) := \min \{\, |a^n + b^n - c^n| \;:\; 2 \le a \le b < c,\ \gcd(a,b,c)=1 \,\}$$

  grow with $n$?  Heuristically yes — the expected number of primitive triples of
  height $\le X$ with bounded defect scales like $X^{3-n}$, so $n = 3$ is critical
  (infinitely many defect-one triples) while $n \ge 4$ is convergent.  But the
  *global* $M(n)$ is out of reach (it bumps into the open existence question and
  abc/Fermat–Catalan finiteness).

  This file supplies the natural **finite, machine-checkable** handle: the
  box-restricted minimal defect

  $$m_N(n) := \min \{\, |a^n + b^n - c^n| \;:\; 2 \le a \le b < c \le N \,\}.$$

  The headline finding (all `native_decide`-certified, box $N = 100$):

  | $n$ | $m_{100}(n)$ | achiever | sign |
  |-----|--------------|----------|------|
  | 3   | 1            | $(6,8,9)$       | $6^3+8^3+1=9^3$        |
  | 4   | 46           | $(5,5,6)$       | $5^4+5^4+46=6^4$       |
  | 5   | 12           | $(13,16,17)$    | $13^5+16^5=17^5+12$    |
  | 6   | 601          | $(2,2,3)$       | $2^6+2^6+601=3^6$      |

  **The box proxy is non-monotone: $m_{100}(4) = 46 > 12 = m_{100}(5)$.**  The
  drop at $n = 5$ is caused by the genuinely small primitive near-miss
  $13^5 + 16^5 = 17^5 + 12$ (gcd$(13,16,17)=1$).  Consequently $M(n)$ growth, if
  true, is *not* visible in the obvious bounded computation and must be argued
  globally (abc / Fermat–Catalan), not by exhibiting a monotone finite minimum.

  Each minimum is certified as a *matching pair*: a `native_decide` lower bound
  (every box triple has defect $\ge K$) together with an explicit achiever
  (defect exactly $K$), so the box minimum is pinned to the exact value $K$.

  Honesty note: the lower bounds are discharged by `native_decide`, which trusts
  the compiler's kernel reduction and therefore depends on the `Lean.ofReduceBool`
  axiom.  These are finite certificates over the box $c \le 100$, not statements
  about the (open) global $M(n)$.
-/

import Mathlib
import Proofs.FermatDefectOne

namespace FermatDefectOne.OQ03

open FermatDefectOne

/-! ## Box-minimal-defect lower bounds (`native_decide` core)

For a triple `2 ≤ a ≤ b < c ≤ 100`, the defect is `|a^n + b^n - c^n|`.  Over
`Nat` the statement "defect `≥ K`" is the decidable disjunction
`a^n + b^n + K ≤ c^n ∨ c^n + K ≤ a^n + b^n`.  The bounded `∀` shape
`∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a → …` enumerates exactly the admissible
triples `2 ≤ a ≤ b < c ≤ 100`. -/

/-- Every box triple `2 ≤ a ≤ b < c ≤ 100` has defect `≥ 46` at exponent `4`. -/
theorem box_defect_ge_46_n4 :
    ∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a →
      a ^ 4 + b ^ 4 + 46 ≤ c ^ 4 ∨ c ^ 4 + 46 ≤ a ^ 4 + b ^ 4 := by
  native_decide

/-- Every box triple `2 ≤ a ≤ b < c ≤ 100` has defect `≥ 12` at exponent `5`. -/
theorem box_defect_ge_12_n5 :
    ∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a →
      a ^ 5 + b ^ 5 + 12 ≤ c ^ 5 ∨ c ^ 5 + 12 ≤ a ^ 5 + b ^ 5 := by
  native_decide

/-- Every box triple `2 ≤ a ≤ b < c ≤ 100` has defect `≥ 601` at exponent `6`. -/
theorem box_defect_ge_601_n6 :
    ∀ c < 101, ∀ b < c, ∀ a < b + 1, 2 ≤ a →
      a ^ 6 + b ^ 6 + 601 ≤ c ^ 6 ∨ c ^ 6 + 601 ≤ a ^ 6 + b ^ 6 := by
  native_decide

/-! ## Lower bounds in ordered-hypothesis form

Restated with the natural ordering hypotheses up front (no primitivity needed:
the bound is on the raw defect). -/

/-- `n = 4`: every box triple has `|a^4 + b^4 - c^4| ≥ 46`. -/
theorem box_min_defect_n4 (a b c : Nat)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b < c) (hc : c ≤ 100) :
    a ^ 4 + b ^ 4 + 46 ≤ c ^ 4 ∨ c ^ 4 + 46 ≤ a ^ 4 + b ^ 4 :=
  box_defect_ge_46_n4 c (by omega) b hbc a (by omega) ha

/-- `n = 5`: every box triple has `|a^5 + b^5 - c^5| ≥ 12`. -/
theorem box_min_defect_n5 (a b c : Nat)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b < c) (hc : c ≤ 100) :
    a ^ 5 + b ^ 5 + 12 ≤ c ^ 5 ∨ c ^ 5 + 12 ≤ a ^ 5 + b ^ 5 :=
  box_defect_ge_12_n5 c (by omega) b hbc a (by omega) ha

/-- `n = 6`: every box triple has `|a^6 + b^6 - c^6| ≥ 601`. -/
theorem box_min_defect_n6 (a b c : Nat)
    (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b < c) (hc : c ≤ 100) :
    a ^ 6 + b ^ 6 + 601 ≤ c ^ 6 ∨ c ^ 6 + 601 ≤ a ^ 6 + b ^ 6 :=
  box_defect_ge_601_n6 c (by omega) b hbc a (by omega) ha

/-! ## Achievers (the lower bounds are tight)

Each minimum is realised by an explicit primitive triple in the box, so
`m₁₀₀(n)` equals the bound above exactly. -/

/-- `n = 4` minimum achieved: `5^4 + 5^4 + 46 = 6^4` (defect exactly `46`,
negative sign), with `2 ≤ 5 ≤ 5 < 6 ≤ 100` and `gcd(gcd 5 5) 6 = 1`. -/
theorem achiever_n4 : (5 : Nat) ^ 4 + 5 ^ 4 + 46 = 6 ^ 4 := by norm_num

/-- `n = 5` minimum achieved: `13^5 + 16^5 = 17^5 + 12` (defect exactly `12`,
positive sign), with `2 ≤ 13 ≤ 16 < 17 ≤ 100` and `gcd(gcd 13 16) 17 = 1`.  This
small primitive near-miss is what makes the box minimum drop at `n = 5`. -/
theorem achiever_n5 : (13 : Nat) ^ 5 + 16 ^ 5 = 17 ^ 5 + 12 := by norm_num

/-- `n = 6` minimum achieved: `2^6 + 2^6 + 601 = 3^6` (defect exactly `601`,
negative sign). -/
theorem achiever_n6 : (2 : Nat) ^ 6 + 2 ^ 6 + 601 = 3 ^ 6 := by norm_num

/-- The achiever triple `(13, 16, 17)` at `n = 5` is admissible and primitive. -/
theorem achiever_n5_primitive :
    2 ≤ 13 ∧ (13 : Nat) ≤ 16 ∧ (16 : Nat) < 17 ∧
      Nat.gcd (Nat.gcd 13 16) 17 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  native_decide

/-! ## Headline: the box-minimal defect is non-monotone in `n`

`m₁₀₀(4) = 46` but `m₁₀₀(5) = 12`.  Since `46 > 12`, the bounded minimal defect
does **not** increase from `n = 4` to `n = 5`.  Any growth of the true global
`M(n)` is therefore invisible to the finite box proxy and must come from a global
argument (abc / Fermat–Catalan), not from a monotone finite minimum. -/

/-- **Non-monotonicity of the box-minimal defect.**

Witnessed concretely:

* at `n = 5` there is a primitive box triple of defect exactly `12`
  (the near-miss `13^5 + 16^5 = 17^5 + 12`), so `m₁₀₀(5) ≤ 12`; while
* at `n = 4` *every* box triple has defect `≥ 46`, so `m₁₀₀(4) ≥ 46`.

Hence `m₁₀₀(4) ≥ 46 > 12 ≥ m₁₀₀(5)`: the finite minimal defect drops as `n` goes
from `4` to `5`. -/
theorem box_min_defect_nonmonotone :
    (∃ a b c : Nat, 2 ≤ a ∧ a ≤ b ∧ b < c ∧ c ≤ 100 ∧
        a ^ 5 + b ^ 5 = c ^ 5 + 12) ∧
    (∀ a b c : Nat, 2 ≤ a → a ≤ b → b < c → c ≤ 100 →
        a ^ 4 + b ^ 4 + 46 ≤ c ^ 4 ∨ c ^ 4 + 46 ≤ a ^ 4 + b ^ 4) := by
  refine ⟨⟨13, 16, 17, by norm_num, by norm_num, by norm_num, by norm_num,
      achiever_n5⟩, ?_⟩
  intro a b c ha hab hbc hc
  exact box_min_defect_n4 a b c ha hab hbc hc

/-! ## Contrast with `n = 3`

At `n = 3` the box minimum is `1` — the defect-one witness `(6, 8, 9)` — so the
sequence of box minima begins `1, 46, 12, 601`.  The `n = 3` value is the only
`1`; for `n ≥ 4` the box minimum exceeds `1` (cf. `Proofs.FermatDefectOneOQ04`,
`no_small_witness_*`), but it is *not* monotone thereafter. -/

/-- At `n = 3` the box contains a defect-`1` (i.e. defect-one) primitive witness,
`(6, 8, 9)`, so `m₁₀₀(3) = 1`. -/
theorem box_min_defect_n3_is_one :
    ∃ a b c : Nat, c ≤ 100 ∧ FermatDefectWitness 3 a b c :=
  ⟨6, 8, 9, by norm_num, fermat_defect_three_neg⟩

end FermatDefectOne.OQ03
