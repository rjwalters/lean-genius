import Proofs.DerangementsOQ02
import Proofs.DerangementsOQ04
import Mathlib.Tactic

/-!
# Partial derangements: the factorial-times-truncated-exponential closed form

## What this proves

Let `S(n, k)` be the number of permutations of an `n`-element set with **exactly
`k` fixed points** (the *rencontres numbers* / partial-derangement numbers).  This
entry gives the closed form of `S(n, k)`, over an **arbitrary characteristic-zero
field** `𝕜`:

$$ S(n,k) \;=\; \frac{n!}{k!}\,\sum_{j=0}^{n-k} \frac{(-1)^j}{j!}. $$

The right-hand bracket is the order-`(n-k)` truncation of the exponential series of
`e^{-1}`, so the identity reads `S(n,k) = (n!/k!) · (partial sum of e^{-1})`.  For
`k = 0` it specialises to the classical derangement closed form
`D_n = n! · ∑_{j≤n} (-1)^j/j!`.

## How this answers the open question

The parent entry `derangements-oq-04` proves the field-level derangement closed
form
`(numDerangements m : 𝕜) = m! · ∑_{j≤m} (-1)^j/j!`
(`DerangementsOQ04.numDerangements_closed_form`) and asks (open question) whether the
same single-induction technique yields a clean closed form for **partial
derangements** (permutations with exactly `k` fixed points) over a field.

This file answers it.  The bridge is purely algebraic: the sibling entry
`derangements-oq-02` already establishes the combinatorial identity

  `S(n,k) = C(n,k) · numDerangements (n-k)`   (`PartialDerangements.card_perms_with_kfixed`),

so combining it with the parent's field closed form and the factorial identity
`C(n,k) · k! · (n-k)! = n!` (`Nat.choose_mul_factorial_mul_factorial`) collapses the
constant `C(n,k) · (n-k)!` to `n!/k!` inside `𝕜`.  Characteristic zero is exactly
what makes `k!` invertible.

## Main results

* `card_perms_with_kfixed_closed_form` — the closed form over a char-zero field `𝕜`.
* `card_perms_with_kfixed_eq_factorial_mul_trunc` — the truncated-`e^{-1}` phrasing,
  reusing `DerangementsOQ04.truncExpNegOne`.
* `card_perms_with_kfixed_closed_form_rat` / `_real` — specialisations to `ℚ` / `ℝ`.
* `card_perms_with_kfixed_zero_closed_form` — for `k = 0` it recovers the parent
  derangement closed form, confirming consistency.

## Status
- [x] Complete proof (0 sorries, 0 axioms beyond Mathlib's foundations).
-/

namespace DerangementsOQ04OQ01

open Finset

/-- **Closed form for partial derangements over a characteristic-zero field.**

`S(n,k) = (n!/k!) · ∑_{j=0}^{n-k} (-1)^j/j!`, where `S(n,k)` is the number of
permutations of `Fin n` with exactly `k` fixed points. -/
theorem card_perms_with_kfixed_closed_form
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (univ.filter (fun x => σ x = x)).card = k)).card : 𝕜)
      = (n.factorial : 𝕜) / (k.factorial : 𝕜)
        * ∑ j ∈ range (n - k + 1), (-1 : 𝕜) ^ j / (j.factorial : 𝕜) := by
  -- combinatorial identity S(n,k) = C(n,k) · D(n-k)  (sibling entry derangements-oq-02)
  have hcard := PartialDerangements.card_perms_with_kfixed n k hk
  -- field closed form for the derangement number D(n-k)  (parent entry derangements-oq-04)
  have hD := DerangementsOQ04.numDerangements_closed_form 𝕜 (n - k)
  -- k! is invertible in a characteristic-zero field
  have hkfac : (k.factorial : 𝕜) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  -- the factorial identity C(n,k) · k! · (n-k)! = n!, cast into 𝕜
  have hchoose : (n.choose k : 𝕜) * (k.factorial : 𝕜) * ((n - k).factorial : 𝕜)
      = (n.factorial : 𝕜) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  rw [hcard]
  push_cast
  rw [hD, div_mul_eq_mul_div, eq_div_iff hkfac]
  -- goal reduces to the factorial identity times the truncated sum; ring-closes via hchoose
  linear_combination (∑ j ∈ range (n - k + 1), (-1 : 𝕜) ^ j / (j.factorial : 𝕜)) * hchoose

/-- The truncated-`e^{-1}` phrasing of the same identity, reusing
`DerangementsOQ04.truncExpNegOne`:
`S(n,k) = (n!/k!) · truncExpNegOne 𝕜 (n-k+1)`. -/
theorem card_perms_with_kfixed_eq_factorial_mul_trunc
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (univ.filter (fun x => σ x = x)).card = k)).card : 𝕜)
      = (n.factorial : 𝕜) / (k.factorial : 𝕜)
        * DerangementsOQ04.truncExpNegOne 𝕜 (n - k + 1) := by
  rw [DerangementsOQ04.truncExpNegOne, card_perms_with_kfixed_closed_form 𝕜 n k hk]

/-- Closed form over the rationals. -/
theorem card_perms_with_kfixed_closed_form_rat (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (univ.filter (fun x => σ x = x)).card = k)).card : ℚ)
      = (n.factorial : ℚ) / (k.factorial : ℚ)
        * ∑ j ∈ range (n - k + 1), (-1 : ℚ) ^ j / (j.factorial : ℚ) :=
  card_perms_with_kfixed_closed_form ℚ n k hk

/-- Closed form over the reals. -/
theorem card_perms_with_kfixed_closed_form_real (n k : ℕ) (hk : k ≤ n) :
    ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (univ.filter (fun x => σ x = x)).card = k)).card : ℝ)
      = (n.factorial : ℝ) / (k.factorial : ℝ)
        * ∑ j ∈ range (n - k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ) :=
  card_perms_with_kfixed_closed_form ℝ n k hk

/-- **Consistency with the parent.**  Setting `k = 0` recovers the derangement
closed form `D_n = n! · ∑_{j≤n} (-1)^j/j!`: with `0! = 1` the prefactor `n!/0!`
is just `n!`, and `S(n,0) = D_n`. -/
theorem card_perms_with_kfixed_zero_closed_form
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (n : ℕ) :
    ((univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (univ.filter (fun x => σ x = x)).card = 0)).card : 𝕜)
      = (n.factorial : 𝕜) * ∑ j ∈ range (n + 1), (-1 : 𝕜) ^ j / (j.factorial : 𝕜) := by
  have h := card_perms_with_kfixed_closed_form 𝕜 n 0 (Nat.zero_le n)
  simpa using h

/-- Sanity check for `S(4,1)`.  A permutation of `4` elements with exactly one
fixed point chooses that fixed point (`C(4,1) = 4` ways) and deranges the other
`3` (`D_3 = 2` ways), so `S(4,1) = 4·2 = 8`.  The closed form
`(4!/1!)·(1 - 1 + 1/2 - 1/6) = 24·(1/3) = 8` agrees. -/
example : ((univ.filter (fun σ : Equiv.Perm (Fin 4) =>
      (univ.filter (fun x => σ x = x)).card = 1)).card : ℚ)
    = (Nat.factorial 4 : ℚ) / (Nat.factorial 1 : ℚ)
      * ∑ j ∈ range 4, (-1 : ℚ) ^ j / (j.factorial : ℚ) :=
  card_perms_with_kfixed_closed_form_rat 4 1 (by norm_num)

end DerangementsOQ04OQ01
