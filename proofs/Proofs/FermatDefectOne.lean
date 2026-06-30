/-
  Fermat Defect-One Conjecture

  The Fermat equation $a^n + b^n - c^n = 0$ has no nontrivial solutions for
  $n > 2$ (Fermat's Last Theorem). This file investigates the very next
  question: can the "defect" be exactly $\pm 1$?

      $$ | a^n + b^n - c^n | = 1 $$

  A primitive, nontrivial witness is asked for: $2 \le a \le b < c$ and
  $\gcd(a, b, c) = 1$. To avoid signed-integer coercions, the absolute-value
  condition is expressed as a disjunction on `Nat`:

      $a^n + b^n + 1 = c^n$    (negative defect: $a^n+b^n-c^n = -1$)
      $a^n + b^n = c^n + 1$    (positive defect: $a^n+b^n-c^n = +1$)

  Benchmarks at $n = 3$ (both signs are witnessed):

      Negative: $6^3 + 8^3 + 1 = 216 + 512 + 1 = 729 = 9^3$, with $\gcd(6,8,9)=1$.
      Positive: $9^3 + 10^3 = 729 + 1000 = 1729 = 1728 + 1 = 12^3 + 1$,
                with $\gcd(9,10,12)=1$.

  The positive-defect witness is a near-cousin of the Ramanujan-Hardy taxicab
  number 1729 = 1^3 + 12^3 = 9^3 + 10^3.

  Both n=3 benchmarks are discharged in this file by `native_decide`. The
  headline conjecture for general $n \ge 3$ is left as `sorry`.

  Hierarchy from trivial to sharp (see gallery entry annotations):
    Level 0: trivial existence ($a = c, b = 1$ for any $n \ge 1$).
    Level 1: nontrivial defect-one existence ($2 \le a \le b < c$).
    Level 2: primitive nontrivial existence ($\gcd(a,b,c) = 1$).
    Level 3: signed primitive existence (both $\pm 1$ witnessed for every $n$).

  Connections:
    - Fermat's Last Theorem (FLT): the zero-defect case is impossible for $n > 2$.
    - Fermat-Catalan: $x^p + y^q = z^r$ with $1/p+1/q+1/r < 1$ has finitely many
      primitive solutions; defect-one is a Pillai-type offset of the diagonal case.
    - Pillai's conjecture: gaps between perfect powers.
-/

import Mathlib

namespace FermatDefectOne

/-! ## Predicates -/

/-- A primitive nontrivial Fermat defect-one witness for exponent `n`.

The bounds `2 ≤ a ≤ b < c` exclude the trivial Level-0 collapse
(`a = 1` or `a = c`). The primitivity condition `gcd (gcd a b) c = 1`
prevents scaling families from inflating a single solution. The defect
condition is the Nat-disjunction:

  `a^n + b^n + 1 = c^n` (negative defect, $a^n+b^n-c^n = -1$), OR
  `a^n + b^n = c^n + 1` (positive defect, $a^n+b^n-c^n = +1$).
-/
def FermatDefectWitness (n a b c : Nat) : Prop :=
  2 ≤ a ∧ a ≤ b ∧ b < c ∧
  Nat.gcd (Nat.gcd a b) c = 1 ∧
  (a ^ n + b ^ n + 1 = c ^ n ∨ a ^ n + b ^ n = c ^ n + 1)

/-- Existence of any primitive nontrivial defect-one witness at exponent `n`. -/
def FermatDefectExists (n : Nat) : Prop :=
  ∃ a b c : Nat, FermatDefectWitness n a b c

/-- Positive defect: $a^n + b^n - c^n = +1$ (Nat form: `a^n + b^n = c^n + 1`). -/
def FermatDefectPositive (n : Nat) : Prop :=
  ∃ a b c : Nat,
    2 ≤ a ∧ a ≤ b ∧ b < c ∧
    Nat.gcd (Nat.gcd a b) c = 1 ∧
    a ^ n + b ^ n = c ^ n + 1

/-- Negative defect: $a^n + b^n - c^n = -1$ (Nat form: `a^n + b^n + 1 = c^n`). -/
def FermatDefectNegative (n : Nat) : Prop :=
  ∃ a b c : Nat,
    2 ≤ a ∧ a ≤ b ∧ b < c ∧
    Nat.gcd (Nat.gcd a b) c = 1 ∧
    a ^ n + b ^ n + 1 = c ^ n

/-! ## Verified $n = 3$ benchmarks (both signs) -/

/-- Negative defect at $n = 3$: $6^3 + 8^3 + 1 = 9^3$.

Check: $216 + 512 + 1 = 729 = 9^3$. Primitivity: $\gcd(\gcd(6,8),9) = \gcd(2,9) = 1$.
Bounds: $2 \le 6 \le 8 < 9$. Discharged by `native_decide`. -/
theorem fermat_defect_three_neg : FermatDefectWitness 3 6 8 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · left; native_decide

/-- Positive defect at $n = 3$: $9^3 + 10^3 = 12^3 + 1$.

Check: $729 + 1000 = 1729 = 1728 + 1 = 12^3 + 1$. Primitivity:
$\gcd(\gcd(9,10),12) = \gcd(1,12) = 1$. Bounds: $2 \le 9 \le 10 < 12$.
This is the Ramanujan-Hardy taxicab number $1729 = 1^3 + 12^3 = 9^3 + 10^3$
shifted by one. Discharged by `native_decide`. -/
theorem fermat_defect_three_pos : FermatDefectWitness 3 9 10 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · right; native_decide

/-- $n = 3$ admits a primitive nontrivial defect-one witness. Derived from the
negative-defect benchmark `fermat_defect_three_neg`. -/
theorem fermat_defect_three : FermatDefectExists 3 :=
  ⟨6, 8, 9, fermat_defect_three_neg⟩

/-- Positive-defect existence at $n = 3$, packaged as `FermatDefectPositive`. -/
theorem fermat_defect_three_positive : FermatDefectPositive 3 := by
  refine ⟨9, 10, 12, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-- Negative-defect existence at $n = 3$, packaged as `FermatDefectNegative`. -/
theorem fermat_defect_three_negative : FermatDefectNegative 3 := by
  refine ⟨6, 8, 9, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

/-! ## Modular obstructions (Level 3 refutation candidates)

A prime `p` is a *Level-3 modular obstruction* at `(n, ε)` if the defect
congruence

  negative sign:  `a^n + b^n + 1 ≡ c^n (mod p)`
  positive sign:  `a^n + b^n ≡ c^n + 1 (mod p)`

has **no** primitive residue solution, i.e. no `(a, b, c) : (ZMod p)³` with
`(a, b, c) ≠ (0, 0, 0)` satisfying it. Such an obstruction would rule out all
integer defect-one solutions of that sign and exponent (any integer solution
reduces mod `p`, and a primitive integer triple stays primitive mod every `p`).

The search at `n ∈ {4, 5, 6}`, `ε ∈ {−1, +1}`, `p ∈ {3, 5, 7, 11, 13}` finds
**no obstruction**. The reason is structural and rules out *every* prime, not
just this range:

* Negative sign: `(a, b, c) = (0, 0, 1)` gives `0 + 0 + 1 = 1 = 1^n` in any
  `ZMod p` (for `n ≥ 1`, since `0^n = 0`). This is a primitive residue triple
  (`c = 1 ≠ 0`), so it is always a solution.
* Positive sign: `(a, b, c) = (1, 0, 0)` gives `1^n + 0^n = 1 = 0^n + 1` in any
  `ZMod p` (for `n ≥ 1`). This is a primitive residue triple (`a = 1 ≠ 0`).

Hence no single-prime congruence obstruction can exist for the defect-one
problem in either sign. The negative search result is recorded as a claim file
in `research/problems/fermat-defect-one/claims/`. The theorems below certify
the structural unit witnesses, both as the explicit `decide`-checked instances
at each `(n, ε, p)` in scope and as the general all-`n`, all-`p` statements. -/

/-- Negative-sign defect congruence over `ZMod p` has a *primitive* residue
solution `(a, b, c)` (not all zero): `a^n + b^n + 1 = c^n`. -/
def ModSolvableNeg (n : Nat) (p : Nat) : Prop :=
  ∃ a b c : ZMod p, ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧ a ^ n + b ^ n + 1 = c ^ n

/-- Positive-sign defect congruence over `ZMod p` has a *primitive* residue
solution `(a, b, c)` (not all zero): `a^n + b^n = c^n + 1`. -/
def ModSolvablePos (n : Nat) (p : Nat) : Prop :=
  ∃ a b c : ZMod p, ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧ a ^ n + b ^ n = c ^ n + 1

/-- **General structural non-obstruction, negative sign.** For every `n ≥ 1`
and every prime `p`, the negative defect congruence has the primitive residue
solution `(0, 0, 1)`. Consequently *no* prime is a Level-3 modular obstruction
for the negative sign at any exponent — in particular none at `n ∈ {4,5,6}`,
`p ∈ {3,5,7,11,13}`. -/
theorem fermat_defect_no_obstruction_neg (n p : Nat) (hn : 1 ≤ n)
    [NeZero p] [Fact (1 < p)] : ModSolvableNeg n p := by
  refine ⟨0, 0, 1, ?_, ?_⟩
  · rintro ⟨-, -, h⟩
    exact (one_ne_zero h)
  · have h0 : (0 : ZMod p) ^ n = 0 := zero_pow (by omega)
    simp [h0]

/-- **General structural non-obstruction, positive sign.** For every `n ≥ 1`
and every prime `p`, the positive defect congruence has the primitive residue
solution `(1, 0, 0)`. Consequently *no* prime is a Level-3 modular obstruction
for the positive sign at any exponent. -/
theorem fermat_defect_no_obstruction_pos (n p : Nat) (hn : 1 ≤ n)
    [NeZero p] [Fact (1 < p)] : ModSolvablePos n p := by
  refine ⟨1, 0, 0, ?_, ?_⟩
  · rintro ⟨h, -, -⟩
    exact (one_ne_zero h)
  · have h0 : (0 : ZMod p) ^ n = 0 := zero_pow (by omega)
    simp [h0]

/-! ### Explicit `decide`-checked instances at the searched `(n, ε, p)`

Each instance exhibits a concrete primitive residue witness and is verified by
`decide` over the finite type `ZMod p`. The naming follows the issue request,
`fermat_defect_obstruction_n_<k>_<sign>_mod_<p>`; because the search found *no*
obstruction, each theorem states `Mod{Neg,Pos}Solvable` — the congruence is
solvable, hence there is no obstruction at that `(n, ε, p)`. -/

theorem fermat_defect_obstruction_n_4_neg_mod_3 : ModSolvableNeg 4 3 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_neg_mod_5 : ModSolvableNeg 4 5 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_neg_mod_7 : ModSolvableNeg 4 7 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_neg_mod_11 : ModSolvableNeg 4 11 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_neg_mod_13 : ModSolvableNeg 4 13 :=
  ⟨0, 0, 1, by decide, by decide⟩

theorem fermat_defect_obstruction_n_4_pos_mod_3 : ModSolvablePos 4 3 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_pos_mod_5 : ModSolvablePos 4 5 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_pos_mod_7 : ModSolvablePos 4 7 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_pos_mod_11 : ModSolvablePos 4 11 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_4_pos_mod_13 : ModSolvablePos 4 13 :=
  ⟨1, 0, 0, by decide, by decide⟩

theorem fermat_defect_obstruction_n_5_neg_mod_3 : ModSolvableNeg 5 3 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_neg_mod_5 : ModSolvableNeg 5 5 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_neg_mod_7 : ModSolvableNeg 5 7 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_neg_mod_11 : ModSolvableNeg 5 11 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_neg_mod_13 : ModSolvableNeg 5 13 :=
  ⟨0, 0, 1, by decide, by decide⟩

theorem fermat_defect_obstruction_n_5_pos_mod_3 : ModSolvablePos 5 3 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_pos_mod_5 : ModSolvablePos 5 5 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_pos_mod_7 : ModSolvablePos 5 7 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_pos_mod_11 : ModSolvablePos 5 11 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_5_pos_mod_13 : ModSolvablePos 5 13 :=
  ⟨1, 0, 0, by decide, by decide⟩

theorem fermat_defect_obstruction_n_6_neg_mod_3 : ModSolvableNeg 6 3 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_neg_mod_5 : ModSolvableNeg 6 5 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_neg_mod_7 : ModSolvableNeg 6 7 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_neg_mod_11 : ModSolvableNeg 6 11 :=
  ⟨0, 0, 1, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_neg_mod_13 : ModSolvableNeg 6 13 :=
  ⟨0, 0, 1, by decide, by decide⟩

theorem fermat_defect_obstruction_n_6_pos_mod_3 : ModSolvablePos 6 3 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_pos_mod_5 : ModSolvablePos 6 5 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_pos_mod_7 : ModSolvablePos 6 7 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_pos_mod_11 : ModSolvablePos 6 11 :=
  ⟨1, 0, 0, by decide, by decide⟩
theorem fermat_defect_obstruction_n_6_pos_mod_13 : ModSolvablePos 6 13 :=
  ⟨1, 0, 0, by decide, by decide⟩

/-! ## Open conjecture: defect-one existence for every $n \ge 3$ -/

/-- **Fermat defect-one conjecture (Level 2).** For every exponent $n \ge 3$,
there is a primitive nontrivial triple $(a, b, c)$ with $2 \le a \le b < c$,
$\gcd(a, b, c) = 1$, and $|a^n + b^n - c^n| = 1$.

Status: open. The $n = 3$ case is verified above (both signs witnessed). For
$n \ge 4$ this is a genuine research conjecture, sitting between Fermat's
Last Theorem (zero defect impossible) and Pillai-type problems (gaps between
perfect powers). -/
theorem fermat_defect_one_exists :
    ∀ n : Nat, 3 ≤ n → FermatDefectExists n := by
  sorry

end FermatDefectOne
