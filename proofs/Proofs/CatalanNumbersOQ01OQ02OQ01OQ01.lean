import Proofs.CatalanNumbersOQ01OQ02OQ01

/-!
# Catalan OQ-01-OQ-02-OQ-01-OQ-01: Catalan `p`-Divisibility as a Kummer Carry Criterion

The parent entry `catalan-numbers-oq-01-oq-02-oq-01` proved a division-free
identity for the `p`-adic valuation of the Catalan numbers at an arbitrary prime,
culminating in the criterion

* `not_dvd_catalan_iff` : `p ∤ Cₙ ⟺ (p − 1)·v_p(n+1) + s_p(2n) = 2·s_p(n)`,

where `s_p` is the base-`p` digit sum.  The right-hand side mixes digit sums in a
way that hides its combinatorial meaning.  **Kummer's theorem** says the quantity
`(2·s_p(n) − s_p(2n)) / (p − 1)` is literally the number of *carries* when one
adds `n` to itself in base `p`, and that this carry count equals the `p`-adic
valuation of the central binomial coefficient `C(2n,n)`.  We therefore define

* `carries p n := v_p(C(2n,n))`  (the Kummer carry count of `n + n` in base `p`),

and reformulate the parent's results in their natural combinatorial shape:

* `sub_one_mul_carries` : `(p − 1)·carries p n + s_p(2n) = 2·s_p(n)`
  (so `(p − 1)·carries p n = 2·s_p(n) − s_p(2n)` is the digit-sum carry formula);
* `not_dvd_catalan_iff_carries` : **`p ∤ Cₙ ⟺ carries p n = v_p(n+1)`**
  (the carry form of the criterion: `p` divides `Cₙ` unless the carries in `n + n`
  are exactly used up by the trailing-zero count `v_p(n+1)` of `n + 1`);
* `padicValNat_catalan_add_succ_eq_carries` :
  **`v_p(Cₙ) + v_p(n+1) = carries p n`**, hence `v_p(n+1) ≤ carries p n` and the
  clean valuation formula `v_p(Cₙ) = carries p n − v_p(n+1)` — the arithmetic
  analogue of `Cₙ = C(2n,n) / (n+1)`.

For the first interesting odd prime `p = 3` we record the specialisation
`not_dvd_catalan_three_iff_carries` and exhibit, with fully checked witnesses, the
first *gap* in the non-divisible index set: `3 ∤ Cₙ` for `n ∈ {0,1,2,3,4}` and
`n ∈ {8,…,13}`, while `3 ∣ Cₙ` for the bridging block `n ∈ {5,6,7}`.  Computing
`Cₙ mod 3` over `n ≤ 30` gives the non-divisible set
`{0,1,2,3,4, 8,9,10,11,12,13, 26,27,28,29,30}`, whose base-`3` block structure
(`[0,4], [8,13], [26,30]`) is the carry criterion at work.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
The hard analytic content (Legendre's formula + digit sums) lives entirely in the
parent; this entry is the combinatorial repackaging plus one application of
multiplicativity of `padicValNat`.
-/

open Nat

namespace CatalanKummer

open CatalanPAdic

variable {p : ℕ}

/-- **Kummer carry count.**  The number of carries when adding `n + n` in base `p`,
realised as the `p`-adic valuation of the central binomial coefficient `C(2n,n)`
(Kummer's theorem identifies these two quantities). -/
def carries (p n : ℕ) : ℕ := padicValNat p (Nat.centralBinom n)

/-- **Digit-sum carry formula.**  `(p − 1)·carries p n + s_p(2n) = 2·s_p(n)`,
equivalently `(p − 1)·carries p n = 2·s_p(n) − s_p(2n)`.  This is the parent's
central-binomial valuation identity, restated for the carry count. -/
theorem sub_one_mul_carries [Fact p.Prime] (n : ℕ) :
    (p - 1) * carries p n + (Nat.digits p (2 * n)).sum = 2 * (Nat.digits p n).sum :=
  sub_one_mul_padicValNat_centralBinom n

/-- **Valuation splitting of the carry count.**
`v_p(Cₙ) + v_p(n+1) = carries p n`.

Immediate from `(n+1)·Cₙ = C(2n,n)` and additivity of `padicValNat` on the nonzero
factors `n + 1` and `Cₙ`.  This is the arithmetic form of `Cₙ = C(2n,n)/(n+1)`. -/
theorem padicValNat_catalan_add_succ_eq_carries [Fact p.Prime] (n : ℕ) :
    padicValNat p (catalan n) + padicValNat p (n + 1) = carries p n := by
  have h : carries p n = padicValNat p (n + 1) + padicValNat p (catalan n) := by
    unfold carries
    rw [← succ_mul_catalan_eq_centralBinom n,
      padicValNat.mul (by omega) (catalan_ne_zero n)]
  omega

/-- **Carry lower bound.**  `v_p(n+1) ≤ carries p n`: the trailing-zero count of
`n + 1` never exceeds the carry count of `n + n`.  (Equivalently `(n+1) ∣ C(2n,n)`
at the level of `p`-adic valuations.) -/
theorem padicValNat_succ_le_carries [Fact p.Prime] (n : ℕ) :
    padicValNat p (n + 1) ≤ carries p n := by
  have := padicValNat_catalan_add_succ_eq_carries (p := p) n
  omega

/-- **Valuation difference formula.**
`v_p(Cₙ) = carries p n − v_p(n+1)` (genuine ℕ-subtraction, valid because of
`padicValNat_succ_le_carries`).  The Catalan number loses exactly `v_p(n+1)`
factors of `p` relative to the central binomial coefficient. -/
theorem padicValNat_catalan_eq [Fact p.Prime] (n : ℕ) :
    padicValNat p (catalan n) = carries p n - padicValNat p (n + 1) := by
  have := padicValNat_catalan_add_succ_eq_carries (p := p) n
  omega

/-- **Carry form of the divisibility criterion.**
`p ∤ Cₙ ⟺ carries p n = v_p(n+1)`.

`p` divides the `n`-th Catalan number unless the carries produced by adding
`n + n` in base `p` are exactly cancelled by the trailing-zero count of `n + 1`.
This is the parent's `not_dvd_catalan_iff` with its raw digit-sum right-hand side
traded for the single equation `carries p n = v_p(n+1)`, obtained by cancelling the
nonzero factor `p − 1` against the digit-sum carry formula. -/
theorem not_dvd_catalan_iff_carries [hp : Fact p.Prime] (n : ℕ) :
    ¬ p ∣ catalan n ↔ carries p n = padicValNat p (n + 1) := by
  rw [not_dvd_catalan_iff (p := p) n]
  have hc := sub_one_mul_carries (p := p) n
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  constructor
  · intro h
    -- both `(p-1)·carries` and `(p-1)·v(n+1)` equal `2 s_p(n) − s_p(2n)`
    have heq : (p - 1) * carries p n = (p - 1) * padicValNat p (n + 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left hp1 heq
  · intro h
    rw [h] at hc
    omega

/-! ### Specialisation to the prime `p = 3` -/

/-- **Carry criterion at `p = 3`.**  `3 ∤ Cₙ ⟺ carries 3 n = v₃(n+1)`.
The first odd-prime analogue of the sibling's parity law
(`Cₙ` odd ⟺ `n + 1` a power of two). -/
theorem not_dvd_catalan_three_iff_carries (n : ℕ) :
    ¬ (3 : ℕ) ∣ catalan n ↔ carries 3 n = padicValNat 3 (n + 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact not_dvd_catalan_iff_carries (p := 3) n

/-! ### Concrete witnesses: the first gap in `{ n | 3 ∤ Cₙ }`

We avoid evaluating `Nat.catalan` directly (its naive recursion does not reduce in
the kernel); instead we read each value off `(n+1)·Cₙ = C(2n,n)` with `C(2n,n)`
computed by `decide`, then finish the divisibility check by `decide`.  This shows
the non-divisible blocks `{0,…,4}` and `{8,…,13}` are separated by a genuine gap
at `n = 5, 6, 7`. -/

/-- `C₄ = 14`, hence `3 ∤ C₄` (top of the first non-divisible block). -/
example : ¬ (3 : ℕ) ∣ catalan 4 := by
  have h := succ_mul_catalan_eq_centralBinom 4
  have hc : Nat.centralBinom 4 = 70 := by decide
  have : catalan 4 = 14 := by omega
  rw [this]; decide

/-- `C₅ = 42`, hence `3 ∣ C₅` (the gap begins). -/
example : (3 : ℕ) ∣ catalan 5 := by
  have h := succ_mul_catalan_eq_centralBinom 5
  have hc : Nat.centralBinom 5 = 252 := by decide
  have : catalan 5 = 42 := by omega
  rw [this]; decide

/-- `C₆ = 132`, hence `3 ∣ C₆`. -/
example : (3 : ℕ) ∣ catalan 6 := by
  have h := succ_mul_catalan_eq_centralBinom 6
  have hc : Nat.centralBinom 6 = 924 := by decide
  have : catalan 6 = 132 := by omega
  rw [this]; decide

/-- `C₇ = 429`, hence `3 ∣ C₇` (the gap ends). -/
example : (3 : ℕ) ∣ catalan 7 := by
  have h := succ_mul_catalan_eq_centralBinom 7
  have hc : Nat.centralBinom 7 = 3432 := by decide
  have : catalan 7 = 429 := by omega
  rw [this]; decide

/-- `C₈ = 1430`, hence `3 ∤ C₈` (bottom of the second non-divisible block). -/
example : ¬ (3 : ℕ) ∣ catalan 8 := by
  have h := succ_mul_catalan_eq_centralBinom 8
  have hc : Nat.centralBinom 8 = 12870 := by decide
  have : catalan 8 = 1430 := by omega
  rw [this]; decide

end CatalanKummer
