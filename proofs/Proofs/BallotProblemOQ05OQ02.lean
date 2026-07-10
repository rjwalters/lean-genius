/-
# The Reflection (André) Form of the Ballot Number, `C(a+b,b) − C(a+b,b−1)`

The companion file `Proofs.BallotProblemOQ05` derives the **strict** Bertrand ballot
number from the Dvoretzky–Motzkin cycle lemma and records it in the reflection form

  `ballotNumber a b = C(a+b−1, a−1) − C(a+b−1, a)`,

counting the sequences of `a` up-steps `(+1)` and `b` down-steps `(−1)` whose every
partial sum is *strictly* positive.

This file treats the *other* classical reflection form,

  `reflectBallot a b = C(a+b, b) − C(a+b, b−1)`,

which is the count of sequences whose every partial sum is `≥ 0` — the
**non-negative** (weakly-ahead) ballot number, the entries of the Catalan triangle.
The two are *not* the same sequence: e.g. `reflectBallot 2 1 = 2` while the strict
`ballotNumber 2 1 = 1`.  The purpose of this file is to **reconcile** them.

## Main result

The non-negative and strict ballot numbers are related by the classical
**prepend-an-up-step bijection**: a non-negative `(a, b)`-path becomes a strictly
positive `(a+1, b)`-path by inserting a mandatory initial `+1`, and conversely.
Arithmetically this is the single shift `a ↦ a + 1`:

* `reflectBallot_eq` — `reflectBallot a b = ballotNumber (a+1) b`  (for `1 ≤ b`).

Everything else is a corollary of this one identity together with the cycle-lemma
arithmetic already proved in the parent file:

* `reflectBallot_sub_exact` — the `ℕ` subtraction `C(a+b,b) − C(a+b,b−1)` is *exact*
  (no truncation) whenever `b ≤ a`, because `C(a+b, b−1) ≤ C(a+b, b)` there.
* `reflectBallot_mul` — the cycle-lemma aggregate for the non-negative count:
  `reflectBallot a b · (a+1+b) = (a+1−b) · C(a+1+b, a+1)`.
* `reflectBallot_div` — the corresponding probability `(a+1−b)/(a+1+b)` over `ℚ`.
* `reflectBallot_catalan` — the diagonal `reflectBallot n n = catalan n` (`1 ≤ n`),
  the number of Dyck paths of semilength `n`.

The two reflection derivations therefore agree: the André count `C(a+b,b) − C(a+b,b−1)`
is exactly the cycle-lemma count of the shifted parameters.  Elementary binomial
arithmetic throughout — no axioms, no `sorry`, no `native_decide`.

## References
* André, D. (1887), *Solution directe du problème résolu par M. Bertrand*.
* Renault, M. (2008), *Lost (and found) in translation: André's actual method*.
-/
import Mathlib
import Proofs.BallotProblemOQ05

namespace BallotProblemOQ05OQ02

open BallotProblemOQ05

/-- The **non-negative ballot number** `reflectBallot a b`, in André's reflection form.

This counts the sequences of `a` up-steps `(+1)` and `b` down-steps `(−1)` whose every
partial sum is `≥ 0` (weak dominance).  Equivalently these are the entries of the
Catalan triangle; the diagonal `a = b` recovers the Catalan numbers. -/
def reflectBallot (a b : ℕ) : ℕ :=
  (a + b).choose b - (a + b).choose (b - 1)

/-- **The reconciliation identity.**  For `1 ≤ b`, the non-negative ballot number is the
strict ballot number of the parameters shifted by one up-step:

  `reflectBallot a b = ballotNumber (a+1) b`.

This is the arithmetic shadow of the **prepend-an-up-step bijection**: a non-negative
`(a, b)`-path is precisely a strictly-positive `(a+1, b)`-path with its forced initial
`+1` removed.  Both sides are reflection differences of the *same* binomials read
through the symmetry `C(a+b, k) = C(a+b, a+b−k)`. -/
theorem reflectBallot_eq (a b : ℕ) (hb : 1 ≤ b) :
    reflectBallot a b = ballotNumber (a + 1) b := by
  have e1 : a + 1 + b - 1 = a + b := by omega
  have e2 : a + 1 - 1 = a := by omega
  simp only [reflectBallot, ballotNumber, e1, e2]
  -- `C(a+b, b) = C(a+b, a)` via `k ↦ (a+b) − k` symmetry
  have h1 : (a + b).choose b = (a + b).choose a := by
    have h := Nat.choose_symm (Nat.le_add_right a b)
    rwa [Nat.add_sub_cancel_left] at h
  -- `C(a+b, b−1) = C(a+b, a+1)`, valid since `1 ≤ b`
  have h2 : (a + b).choose (b - 1) = (a + b).choose (a + 1) := by
    have h := Nat.choose_symm (show a + 1 ≤ a + b by omega)
    have e3 : a + b - (a + 1) = b - 1 := by omega
    rwa [e3] at h
  rw [h1, h2]

/-- The reflection subtraction is **exact** for `b ≤ a`: `C(a+b, b−1) ≤ C(a+b, b)`, so
`reflectBallot a b + C(a+b, b−1) = C(a+b, b)` with no `ℕ` truncation. -/
theorem reflectBallot_sub_exact (a b : ℕ) (hb : 1 ≤ b) (hab : b ≤ a) :
    reflectBallot a b + (a + b).choose (b - 1) = (a + b).choose b := by
  have hle : (a + b).choose (b - 1) ≤ (a + b).choose b := by
    -- Pascal ratio: `C(a+b, b) · b = C(a+b, b−1) · (a+1)`
    have h := Nat.choose_succ_right_eq (a + b) (b - 1)
    have eb : b - 1 + 1 = b := by omega
    have ed : (a + b) - (b - 1) = a + 1 := by omega
    rw [eb, ed] at h
    -- h : C(a+b, b) * b = C(a+b, b−1) * (a+1)
    have hstep : (a + b).choose (b - 1) * (a + 1) ≤ (a + b).choose b * (a + 1) := by
      rw [← h]; gcongr; omega
    exact Nat.le_of_mul_le_mul_right hstep (by omega)
  simp only [reflectBallot]; omega

/-- **Cycle-lemma aggregate for the non-negative count.**  Applying the parent file's
`ballotNumber_mul_add` to the shifted parameters `(a+1, b)`:

  `reflectBallot a b · (a+1+b) = (a+1−b) · C(a+1+b, a+1)`.

So the André reflection number carries the same `(a′−b)/(a′+b)` cycle-lemma meaning at
the shifted top count `a′ = a+1`; in particular `a+1+b` divides `(a+1−b)·C(a+1+b, a+1)`. -/
theorem reflectBallot_mul (a b : ℕ) (hb : 1 ≤ b) :
    reflectBallot a b * (a + 1 + b) = (a + 1 - b) * (a + 1 + b).choose (a + 1) := by
  rw [reflectBallot_eq a b hb]
  exact ballotNumber_mul_add (a + 1) b (by omega)

/-- **Non-negative ballot probability.**  For `1 ≤ b ≤ a`, over `ℚ`:

  `reflectBallot a b / C(a+1+b, a+1) = (a+1−b)/(a+1+b)`. -/
theorem reflectBallot_div (a b : ℕ) (hb : 1 ≤ b) (hab : b ≤ a) :
    (reflectBallot a b : ℚ) / (((a + 1) + b).choose (a + 1) : ℚ)
      = (((a + 1 : ℕ) : ℚ) - b) / (((a + 1 : ℕ) : ℚ) + b) := by
  rw [reflectBallot_eq a b hb]
  exact ballotNumber_div (a + 1) b (by omega) (by omega)

/-- **Catalan (Dyck-path) specialisation.**  On the diagonal `a = b = n` (`1 ≤ n`) the
non-negative ballot number is the `n`-th Catalan number: the count of non-negative
paths with `n` up- and `n` down-steps is the number of Dyck paths of semilength `n`. -/
theorem reflectBallot_catalan (n : ℕ) (hn : 1 ≤ n) : reflectBallot n n = catalan n := by
  rw [reflectBallot_eq n n hn]
  exact ballotNumber_catalan n

/-! ### Worked examples (checked by `decide`, hence `0`-axiom) -/

/-- `a = 2, b = 1`: `C(3,1) − C(3,0) = 3 − 1 = 2` (vs. strict `ballotNumber 2 1 = 1`). -/
example : reflectBallot 2 1 = 2 := by decide

/-- `a = 3, b = 2`: `C(5,2) − C(5,1) = 10 − 5 = 5`. -/
example : reflectBallot 3 2 = 5 := by decide

/-- Diagonal `n = 2`: `C(4,2) − C(4,1) = 6 − 4 = 2 = catalan 2`. -/
example : reflectBallot 2 2 = 2 := by decide

/-- Diagonal `n = 3`: `C(6,3) − C(6,2) = 20 − 15 = 5 = catalan 3`. -/
example : reflectBallot 3 3 = 5 := by decide

end BallotProblemOQ05OQ02
