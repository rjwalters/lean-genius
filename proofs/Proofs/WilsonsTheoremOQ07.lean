import Mathlib

/-
# Wilson's theorem, oq-07: an *explicit* square root of `-1` modulo `p ≡ 1 (mod 4)`

**Open question (`wilsons-theorem-oq-07`).** Wilson's theorem
(`ZMod.wilsons_lemma`) states `(p-1)! ≡ -1 (mod p)`. A classical refinement
pairs each residue `k` with its reflection `p - k ≡ -k`, which splits the
factorial across its midpoint `m = (p-1)/2`:

  `(p-1)! ≡ (-1)^m * (m!)^2  (mod p)`   for every odd prime `p`.

Specialising the parity of `m`:

* if `p ≡ 1 (mod 4)` then `m` is even, so `(m!)^2 ≡ -1 (mod p)`:
  `m! = ((p-1)/2)!` is an **explicit square root of `-1`**;
* if `p ≡ 3 (mod 4)` then `m` is odd, so `(m!)^2 ≡ +1 (mod p)`, hence
  `m! ≡ ±1`.

Mathlib already knows that `-1` *is* a square modulo `p` exactly when
`p % 4 ≠ 3` (`ZMod.exists_sq_eq_neg_one_iff`), but that statement is purely
existential. The contribution here is the **constructive** witness
`((p-1)/2)!` together with the sign-controlled reflection identity it comes
from. This complements the sibling entries on Wilson's family
(`wilsons-theorem-oq-01` … `-oq-06`), none of which produce the explicit root.

Everything is fully machine-checked over `Mathlib`, with no `sorry`, no
`axiom`, and no `native_decide`.
-/

open Finset

namespace WilsonsTheoremOQ07

open scoped Nat

variable (p : ℕ) [Fact p.Prime]

/-- **Reflection refinement of Wilson's theorem.** For an odd prime `p`, writing
`m = (p-1)/2`, the factorial `(p-1)!` factors through its midpoint as
`(-1)^m * (m!)^2`. Pairing `k ↔ p - k ≡ -k` over the lower half `{1, …, m}`
turns the upper half `{m+1, …, p-1}` into `(-1)^m * m!`, and Wilson's theorem
fixes the total product at `-1`. -/
theorem neg_one_pow_mul_factorial_sq (hodd : Odd p) :
    (-1 : ZMod p) ^ ((p - 1) / 2) * (((p - 1) / 2)! : ZMod p) ^ 2 = -1 := by
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  set m := (p - 1) / 2 with hm
  have hpm : p = 2 * m + 1 := by omega
  -- Lower half product equals `m!`.
  have hL : ∏ i ∈ Ico 1 (m + 1), (i : ZMod p) = (m ! : ZMod p) := by
    rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
  -- Each upper-half factor reflects: `↑(p - j) = -↑j` for `j ≤ m`.
  have hcast : ∀ j ∈ Ico 1 (m + 1), ((p - j : ℕ) : ZMod p) = -(j : ZMod p) := by
    intro j hj
    rw [mem_Ico] at hj
    have hjp : j ≤ p := by omega
    rw [Nat.cast_sub hjp, ZMod.natCast_self, zero_sub]
  -- Reindex the upper half `{m+1, …, p-1}` as `{p - j : 1 ≤ j ≤ m}`.
  have hreflect : ∏ j ∈ Ico 1 (m + 1), ((p - j : ℕ) : ZMod p)
      = ∏ i ∈ Ico (m + 1) p, (i : ZMod p) := by
    have h := Finset.prod_Ico_reflect (fun i : ℕ => ((i : ℕ) : ZMod p)) 1
      (m := m + 1) (n := p) (by omega)
    simp only at h
    have hb1 : p + 1 - (m + 1) = m + 1 := by omega
    have hb2 : p + 1 - 1 = p := by omega
    rw [hb1, hb2] at h
    exact h
  -- Upper half product equals `(-1)^m * m!`.
  have hR : ∏ i ∈ Ico (m + 1) p, (i : ZMod p) = (-1 : ZMod p) ^ m * (m ! : ZMod p) := by
    rw [← hreflect, Finset.prod_congr rfl hcast, Finset.prod_neg, Nat.card_Ico, hL,
      Nat.add_sub_cancel]
  -- Wilson's theorem: the full product over `{1, …, p-1}` is `-1`.
  have hsplit : (∏ i ∈ Ico 1 (m + 1), (i : ZMod p)) * (∏ i ∈ Ico (m + 1) p, (i : ZMod p))
      = ∏ i ∈ Ico 1 p, (i : ZMod p) :=
    Finset.prod_Ico_consecutive _ (by omega) (by omega)
  have hwilson : ∏ i ∈ Ico 1 p, (i : ZMod p) = -1 := ZMod.prod_Ico_one_prime p
  rw [hL, hR, hwilson] at hsplit
  -- Rearrange `m! * ((-1)^m * m!) = -1` into the claimed form.
  calc (-1 : ZMod p) ^ m * (m ! : ZMod p) ^ 2
      = (m ! : ZMod p) * ((-1 : ZMod p) ^ m * (m ! : ZMod p)) := by ring
    _ = -1 := hsplit

/-- **Explicit square root of `-1`.** For a prime `p ≡ 1 (mod 4)`, the factorial
`((p-1)/2)!` squares to `-1` in `ZMod p`. -/
theorem factorial_half_sq_eq_neg_one (h4 : p % 4 = 1) :
    (((p - 1) / 2)! : ZMod p) ^ 2 = -1 := by
  have hodd : Odd p := by rw [Nat.odd_iff]; omega
  have hmeven : Even ((p - 1) / 2) := by rw [Nat.even_iff]; omega
  have key := neg_one_pow_mul_factorial_sq p hodd
  rw [hmeven.neg_one_pow, one_mul] at key
  exact key

/-- **Companion case.** For a prime `p ≡ 3 (mod 4)`, the factorial `((p-1)/2)!`
squares to `+1` in `ZMod p` (so it equals `±1`, never a root of `-1`). -/
theorem factorial_half_sq_eq_one (h4 : p % 4 = 3) :
    (((p - 1) / 2)! : ZMod p) ^ 2 = 1 := by
  have hodd : Odd p := by rw [Nat.odd_iff]; omega
  have hmodd : Odd ((p - 1) / 2) := by rw [Nat.odd_iff]; omega
  have key := neg_one_pow_mul_factorial_sq p hodd
  rw [hmodd.neg_one_pow] at key
  linear_combination -key

/-- The explicit root recovers the forward direction of Mathlib's existential
`ZMod.exists_sq_eq_neg_one_iff` constructively: when `p ≡ 1 (mod 4)`, `-1` is a
square modulo `p`, witnessed by `((p-1)/2)!`. -/
theorem exists_sq_eq_neg_one_of_one_mod_four (h4 : p % 4 = 1) :
    ∃ y : ZMod p, y ^ 2 = -1 :=
  ⟨(((p - 1) / 2)! : ZMod p), factorial_half_sq_eq_neg_one p h4⟩

/-- Consistency check against Mathlib: the explicit root exists for `p ≡ 1 (mod 4)`
precisely because `p % 4 ≠ 3`, the criterion of `ZMod.exists_sq_eq_neg_one_iff`. -/
example (h4 : p % 4 = 1) : p % 4 ≠ 3 := by omega

/-- `p = 5`: `((5-1)/2)! = 2! = 2` and `2² = 4 ≡ -1 (mod 5)`. -/
example : (((5 - 1) / 2)! : ZMod 5) ^ 2 = -1 := by decide

/-- `p = 13`: `((13-1)/2)! = 6! = 720 ≡ 5 (mod 13)` and `5² = 25 ≡ -1 (mod 13)`. -/
example : (((13 - 1) / 2)! : ZMod 13) ^ 2 = -1 := by decide

/-- `p = 7 ≡ 3 (mod 4)`: `((7-1)/2)! = 3! = 6 ≡ -1 (mod 7)` and `(-1)² = 1`. -/
example : (((7 - 1) / 2)! : ZMod 7) ^ 2 = 1 := by decide

end WilsonsTheoremOQ07
