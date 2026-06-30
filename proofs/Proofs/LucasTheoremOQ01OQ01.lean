import Mathlib
import Proofs.LucasTheoremOQ01

/-!
# Fine's Theorem: the digit-product count of binomials not divisible by a prime

For a prime `p`, write `n` in base `p` as `n = (nₐ … n₁ n₀)_p`.  **Fine's theorem**
(1947) counts the entries of row `n` of Pascal's triangle that are *not* divisible
by `p`:

> the number of `k ∈ {0, …, n}` with `p ∤ C(n, k)` equals `∏ᵢ (nᵢ + 1)`,

the product over the base-`p` digits `nᵢ` of `n`.

This generalises the prime-`2` special case proved in `LucasTheoremOQ01`
(`oddCount n = 2 ^ s₂(n)`): when `p = 2` every digit is `0` or `1`, so each factor
`nᵢ + 1` is `1` or `2` and the product is `2` raised to the number of `1`-digits,
i.e. `2 ^ s₂(n)`.

## The proof

The engine is the single base-`p` step of Lucas' theorem,
`C(p·n + r, k) ≡ C(r, k mod p) · C(n, k div p) (mod p)` for `0 ≤ r < p`.  Since
`r < p`, the digit-wise factor `C(r, s)` is coprime to `p` exactly when `s ≤ r`
(when `s > r` it vanishes; when `s ≤ r` the factorial identity forces `vₚ = 0`).
This yields the pointwise characterisation

* `not_dvd_choose_step` : `p ∤ C(p·n + r, k) ↔ k mod p ≤ r ∧ p ∤ C(n, k div p)`,

generalising `odd_choose_two_mul` / `odd_choose_two_mul_add_one`.  Partitioning row
`p·n + r` by the last base-`p` digit `s = k mod p` turns the row into the image of
`(fineRow p n) ×ˢ {0, …, r}` under `(j, s) ↦ p·j + s`, giving the multiplicative
recursion

* `fineCount_recursion` : `fineCount p (p·n + r) = (r + 1) · fineCount p n`,

mirroring `oddCount_two_mul` and `oddCount_two_mul_add_one`.  A strong induction
on `n`, run alongside the base-`p` digit recursion `Nat.digits_def'`, then gives the
closed form

* `fine_theorem` : `fineCount p n = ∏ over (digits p n) of (digit + 1)`.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat Finset

namespace FineTheorem

/-- The set of column indices `k ≤ n` for which `p ∤ C(n, k)`. -/
def fineRow (p n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun k => ¬ p ∣ n.choose k)

/-- The number of entries in row `n` of Pascal's triangle not divisible by `p`. -/
def fineCount (p n : ℕ) : ℕ := (fineRow p n).card

/-! ## A small-row binomial is coprime to `p` iff the column fits -/

/-- For a prime `p` and `r < p`, the binomial `C(r, s)` is coprime to `p` exactly when
`s ≤ r`: if `s > r` the coefficient vanishes (and `p ∣ 0`), while if `s ≤ r` the
factorial identity `C(r,s)·s!·(r−s)! = r!` together with `p ∤ r!` (as `r < p`) forces
`vₚ(C(r,s)) = 0`. -/
theorem choose_not_dvd_iff {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : r < p) (s : ℕ) :
    ¬ p ∣ r.choose s ↔ s ≤ r := by
  rcases le_or_gt s r with hs | hs
  · simp only [hs, iff_true]
    intro hdvd
    have hfac : r.choose s * s ! * (r - s)! = r ! :=
      Nat.choose_mul_factorial_mul_factorial hs
    have hpr : p ∣ r ! := by
      rw [← hfac]; exact (hdvd.mul_right _).mul_right _
    rw [hp.dvd_factorial] at hpr
    omega
  · rw [Nat.choose_eq_zero_of_lt hs]
    simp only [dvd_zero, not_true_eq_false, false_iff, not_le]
    exact hs

/-! ## The pointwise non-divisibility characterisation (single base-`p` step) -/

/-- **Pointwise step.** For a prime `p` and last digit `r < p`,
`p ∤ C(p·n + r, k)` iff the last base-`p` digit `k mod p` of `k` is `≤ r` and
`p ∤ C(n, k div p)`.  This is the general-`p` analogue of `odd_choose_two_mul`
(`r = 0`) and `odd_choose_two_mul_add_one` (`r = 1`). -/
theorem not_dvd_choose_step {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : r < p) (n k : ℕ) :
    ¬ p ∣ (p * n + r).choose k ↔ k % p ≤ r ∧ ¬ p ∣ n.choose (k / p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (p * n + r).choose k
      ≡ ((p * n + r) % p).choose (k % p) * ((p * n + r) / p).choose (k / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have e1 : (p * n + r) % p = r := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  have e2 : (p * n + r) / p = n := by
    rw [Nat.mul_add_div hp.pos]; simp [Nat.div_eq_of_lt hr]
  rw [e1, e2] at h
  have hiff : p ∣ (p * n + r).choose k ↔ p ∣ r.choose (k % p) * n.choose (k / p) := by
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun ha => h.symm.trans ha, fun hb => h.trans hb⟩
  rw [hiff, hp.dvd_mul, not_or, choose_not_dvd_iff hp hr]

/-! ## The multiplicative recursion for `fineCount` -/

/-- **Multiplicative recursion.** For a prime `p` and last digit `r < p`,
`fineCount p (p·n + r) = (r + 1) · fineCount p n`.  Row `p·n + r` is the image of
`fineRow p n ×ˢ {0, …, r}` under `(j, s) ↦ p·j + s` (split off the last base-`p`
digit), and that map is injective on the product, so the cardinalities multiply.
Generalises `oddCount_two_mul` (`r = 0`) and `oddCount_two_mul_add_one` (`r = 1`). -/
theorem fineCount_recursion {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : r < p) (n : ℕ) :
    fineCount p (p * n + r) = (r + 1) * fineCount p n := by
  have himg : fineRow p (p * n + r)
      = (fineRow p n ×ˢ range (r + 1)).image (fun x : ℕ × ℕ => p * x.1 + x.2) := by
    ext k
    simp only [fineRow, Finset.mem_filter, Finset.mem_range, Finset.mem_image,
      Finset.mem_product, Nat.lt_succ_iff, Prod.exists]
    constructor
    · rintro ⟨hk, hnd⟩
      rw [not_dvd_choose_step hp hr] at hnd
      obtain ⟨hs, hndj⟩ := hnd
      have hjn : k / p ≤ n := by
        by_contra hcon
        push_neg at hcon
        exact hndj (by rw [Nat.choose_eq_zero_of_lt hcon]; exact dvd_zero p)
      refine ⟨k / p, k % p, ⟨⟨hjn, hndj⟩, hs⟩, ?_⟩
      exact Nat.div_add_mod k p
    · rintro ⟨j, s, ⟨⟨hjn, hndj⟩, hs⟩, rfl⟩
      have hsp : s < p := lt_of_le_of_lt hs hr
      have hmod : (p * j + s) % p = s := by
        rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hsp
      have hdiv : (p * j + s) / p = j := by
        rw [Nat.mul_add_div hp.pos]; simp [Nat.div_eq_of_lt hsp]
      have hpj : p * j ≤ p * n := by gcongr
      refine ⟨by omega, ?_⟩
      rw [not_dvd_choose_step hp hr, hmod, hdiv]
      exact ⟨hs, hndj⟩
  have hinj : Set.InjOn (fun x : ℕ × ℕ => p * x.1 + x.2)
      (↑(fineRow p n ×ˢ range (r + 1)) : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at ha hb
    have hap : a.2 < p := lt_of_lt_of_le ha.2 (by omega)
    have hbp : b.2 < p := lt_of_lt_of_le hb.2 (by omega)
    have key : p * a.1 + a.2 = p * b.1 + b.2 := hab
    have h1 : a.1 = b.1 := by
      have e1 : (p * a.1 + a.2) / p = a.1 := by
        rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hap, add_zero]
      have e2 : (p * b.1 + b.2) / p = b.1 := by
        rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hbp, add_zero]
      rw [← e1, ← e2, key]
    have h2 : a.2 = b.2 := by rw [h1] at key; exact Nat.add_left_cancel key
    exact Prod.ext h1 h2
  have hcard : (fineRow p (p * n + r)).card
      = (fineRow p n ×ˢ range (r + 1)).card := by
    rw [himg]; exact Finset.card_image_of_injOn hinj
  unfold fineCount
  rw [hcard, Finset.card_product, Finset.card_range]
  ring

/-- Base case: `p ∤ C(0, 0) = 1`, so row `0` has a single surviving entry. -/
theorem fineCount_zero {p : ℕ} (hp : p.Prime) : fineCount p 0 = 1 := by
  have h : fineRow p 0 = {0} := by
    ext k
    simp only [fineRow, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, _⟩; omega
    · rintro rfl
      refine ⟨by omega, ?_⟩
      rw [Nat.choose_self]
      exact Nat.dvd_one.not.mpr hp.ne_one
  unfold fineCount
  rw [h, Finset.card_singleton]

/-! ## Fine's theorem -/

/-- **Fine's theorem.** For a prime `p`, the number of entries in row `n` of Pascal's
triangle that are *not* divisible by `p` equals the product `∏ᵢ (nᵢ + 1)` over the
base-`p` digits `nᵢ` of `n`.

Specialising to `p = 2` recovers Glaisher's `oddCount n = 2 ^ s₂(n)` from
`LucasTheoremOQ01`. -/
theorem fine_theorem {p : ℕ} (hp : p.Prime) (n : ℕ) :
    fineCount p n = ((Nat.digits p n).map (· + 1)).prod := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [fineCount_zero hp]; simp
    · have hp1 : 1 < p := hp.one_lt
      have hsplit : p * (n / p) + n % p = n := Nat.div_add_mod n p
      have hlt : n / p < n := Nat.div_lt_self hn hp1
      have hr : n % p < p := Nat.mod_lt _ hp.pos
      calc fineCount p n
          = fineCount p (p * (n / p) + n % p) := by rw [hsplit]
        _ = (n % p + 1) * fineCount p (n / p) := fineCount_recursion hp hr _
        _ = (n % p + 1) * ((Nat.digits p (n / p)).map (· + 1)).prod := by rw [ih _ hlt]
        _ = ((Nat.digits p n).map (· + 1)).prod := by
              rw [Nat.digits_def' hp1 hn, List.map_cons, List.prod_cons]

/-! ## Sanity checks -/

/-- Row `5` mod `2`: digits of `5` are `1, 0, 1` (`5 = 101₂`), product
`(1+1)(0+1)(1+1) = 4`, matching `oddCount 5 = 4`. -/
example : fineCount 2 5 = 4 := by decide

/-- Row `7` mod `3`: `7 = 21₃` has digits `1, 2`, product `(1+1)(2+1) = 6`. -/
example : fineCount 3 7 = 6 := by decide

/-- Row `10` mod `3`: `10 = 101₃` has digits `1, 0, 1`, product
`(1+1)(0+1)(1+1) = 4`. -/
example : fineCount 3 10 = 4 := by decide

/-- The closed form holds for `p = 3`, `n = 7`. -/
example : fineCount 3 7 = ((Nat.digits 3 7).map (· + 1)).prod :=
  fine_theorem (by norm_num) 7

end FineTheorem
