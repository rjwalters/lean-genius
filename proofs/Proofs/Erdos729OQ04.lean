/-
  Erdős Problem #729 — Open Question OQ-04

  Question:
    Can the proof of `legendre_for_two` (v₂(n!) = n − s₂(n), where s₂ is the
    binary digit sum) be completed in Lean using Mathlib's `padicValNat`
    machinery — i.e. WITHOUT the axiom `legendre_identity`?

  Answer: YES.

  The parent module `Proofs.Erdos729Problem` proves `legendre_for_two` only by
  forwarding to the axiom `legendre_identity`
    (v_p(n!) = (n − s_p(n))/(p − 1)).
  Mathlib already contains Legendre's theorem in digit-sum form:

    `sub_one_mul_padicValNat_factorial`
      : (p − 1) * padicValNat p (n!) = n − (Nat.digits p n).sum

  Specialising to p = 2 gives `1 * padicValNat 2 (n!) = n − (Nat.digits 2 n).sum`,
  which is exactly `legendre_for_two` once we identify the binary digit sum
  with `(Nat.digits 2 n).sum`.

  This file gives the axiom-free derivation. It is self-contained (it does not
  import the parent module): we use a structurally-mirrored recursive binary
  digit sum `binDigitSum` matching the parent's `digitSum 2 ·` recurrence, and
  prove it equals `(Nat.digits 2 n).sum`.

  Status: 0 axioms, 0 sorries.

  Follow-up (Docker-gated): retire `legendre_identity` directly in the parent
  registered file. That edit must additionally bridge the parent's `digitSum`,
  which is defined with `if n = 0 then … else …` (so `simp only [digitSum]`
  loops); the bridge there needs a single-step unfold (`digitSum.eq_def`)
  rather than the structural `simp only` usable here.

  Tags: factorials, legendre-formula, p-adic-valuation, axiom-removal
-/

import Mathlib

namespace Erdos729OQ04

open Nat

/-- Binary digit sum, defined by the same recurrence as the parent file's
    `digitSum 2 ·` but with a structural `0 / succ` split so its equation
    lemmas can be unfolded one step at a time without looping. -/
def binDigitSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + binDigitSum ((n + 1) / 2)
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- The recursive binary digit sum agrees with Mathlib's `Nat.digits 2`. -/
theorem binDigitSum_eq_digits_sum (n : ℕ) :
    binDigitSum n = (Nat.digits 2 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simp [binDigitSum]
    · simp only [binDigitSum]
      rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) (Nat.succ_pos m),
          List.sum_cons,
          ih ((m + 1) / 2) (Nat.div_lt_self (Nat.succ_pos m) (by norm_num))]

/-- **Legendre's theorem for p = 2, axiom-free**, stated with Mathlib's native
    base-2 digit sum.  This is a direct application of
    `sub_one_mul_padicValNat_factorial`. -/
theorem legendre_for_two_native (n : ℕ) :
    padicValNat 2 n.factorial = n - (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa using h

/-- v₂(n!) = n − s₂(n) with the recursive binary digit sum, proved with no
    axioms (the parent's `legendre_for_two` uses `axiom legendre_identity`). -/
theorem legendre_for_two (n : ℕ) :
    padicValNat 2 n.factorial = n - binDigitSum n := by
  rw [legendre_for_two_native, binDigitSum_eq_digits_sum]

end Erdos729OQ04
