import Mathlib

/-!
# Catalan OQ-01-OQ-02-OQ-01: The `p`-adic Valuation of the Catalan Numbers

The sibling entry `catalan-numbers-oq-01-oq-02` describes the **2-adic** valuation
of the Catalan numbers `Cₙ = catalan n`, obtaining `v₂(Cₙ) = s₂(n+1) − 1` and the
parity law `Cₙ` odd ⟺ `n + 1` is a power of two.  That argument was special to the
prime `2`, where the binary digit sum is doubling-invariant: `s₂(2n) = s₂(n)`.

This entry removes that restriction and describes the valuation of `Cₙ` at an
**arbitrary prime `p`**.  The two ingredients are both general in `p`:

* **Legendre's formula** `(p − 1)·v_p(m!) = m − s_p(m)`
  (`sub_one_mul_padicValNat_factorial`), where `s_p` is the base-`p` digit sum, and
* the factorisation `(2n)! = C(2n,n)·(n!)²`, giving the central-binomial valuation.

Combining these with `(n+1)·Cₙ = C(2n,n)` (`succ_mul_catalan_eq_centralBinom`)
yields the complete, division-free identity

* `sub_one_mul_padicValNat_centralBinom` : `(p−1)·v_p(C(2n,n)) + s_p(2n) = 2·s_p(n)`
* `sub_one_mul_padicValNat_catalan`      :
    `(p−1)·(v_p(Cₙ) + v_p(n+1)) + s_p(2n) = 2·s_p(n)`

and a clean **`p`-divisibility criterion** generalising the parity law:

* `not_dvd_catalan_iff` :
    `p ∤ Cₙ ⟺ (p−1)·v_p(n+1) + s_p(2n) = 2·s_p(n)`.

For `p = 2` this recovers the sibling's `Cₙ` odd ⟺ `v₂(n+1) + s₂(n) = 2·s₂(n)`,
i.e. (via the carry identity) `s₂(n+1) = 1`.  The quantity `2·s_p(n) − s_p(2n)` is
exactly `(p−1)` times Kummer's carry count for `n + n` in base `p`, so the headline
identity is Kummer's theorem made explicit for the Catalan numbers.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat

namespace CatalanPAdic

variable {p : ℕ}

/-- `catalan n ≠ 0` (mirrors the sibling entry; needed for valuation splitting). -/
theorem catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  intro h
  have hmul := succ_mul_catalan_eq_centralBinom n
  rw [h, Nat.mul_zero] at hmul
  exact (Nat.centralBinom_pos n).ne' hmul.symm

/-- **Central-binomial valuation at a general prime.**
`(p − 1)·v_p(C(2n,n)) + s_p(2n) = 2·s_p(n)`.

Proved straight from Legendre's formula applied to `(2n)!` and `n!`, together with
the factorisation `(2n)! = C(2n,n)·(n!)²`.  No base-`p` digit induction and no
truncated subtraction: `s_p(m) ≤ m` (`digit_sum_le`) keeps every step additive. -/
theorem sub_one_mul_padicValNat_centralBinom [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (Nat.centralBinom n) + (Nat.digits p (2 * n)).sum
      = 2 * (Nat.digits p n).sum := by
  -- Legendre's formula on `(2n)!` and `n!`.
  have L2 := sub_one_mul_padicValNat_factorial (p := p) (2 * n)
  have Ln := sub_one_mul_padicValNat_factorial (p := p) n
  have b2 : (Nat.digits p (2 * n)).sum ≤ 2 * n := Nat.digit_sum_le p (2 * n)
  have bn : (Nat.digits p n).sum ≤ n := Nat.digit_sum_le p n
  -- Factorisation `(2n)! = C(2n,n)·n!·n!`.
  have hC : Nat.centralBinom n ≠ 0 := (Nat.centralBinom_pos n).ne'
  have hn! : (n ! : ℕ) ≠ 0 := Nat.factorial_ne_zero n
  have hfac : Nat.centralBinom n * n ! * n ! = (2 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
    exact h
  -- Hence `v_p((2n)!) = v_p(C) + v_p(n!) + v_p(n!)`.
  have hv : padicValNat p ((2 * n)!)
      = padicValNat p (Nat.centralBinom n) + padicValNat p (n !) + padicValNat p (n !) := by
    rw [← hfac, padicValNat.mul (Nat.mul_ne_zero hC hn!) hn!, padicValNat.mul hC hn!]
  -- The single nonlinear step: distribute `(p−1)` over `hv`.
  have hmul : (p - 1) * padicValNat p ((2 * n)!)
      = (p - 1) * padicValNat p (Nat.centralBinom n) + 2 * ((p - 1) * padicValNat p (n !)) := by
    rw [hv]; ring
  omega

/-- **The `p`-adic valuation of the Catalan numbers.**
`(p − 1)·(v_p(Cₙ) + v_p(n+1)) + s_p(2n) = 2·s_p(n)`.

Immediate from the central-binomial identity and `(n+1)·Cₙ = C(2n,n)`. -/
theorem sub_one_mul_padicValNat_catalan [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * (padicValNat p (catalan n) + padicValNat p (n + 1))
      + (Nat.digits p (2 * n)).sum = 2 * (Nat.digits p n).sum := by
  have hcb := sub_one_mul_padicValNat_centralBinom (p := p) n
  have hmul := succ_mul_catalan_eq_centralBinom n
  have hsplit : padicValNat p (Nat.centralBinom n)
      = padicValNat p (n + 1) + padicValNat p (catalan n) := by
    rw [← hmul, padicValNat.mul (by omega) (catalan_ne_zero n)]
  have hexp : (p - 1) * padicValNat p (Nat.centralBinom n)
      = (p - 1) * (padicValNat p (catalan n) + padicValNat p (n + 1)) := by
    rw [hsplit]; ring
  omega

/-- **`p`-divisibility criterion for the Catalan numbers.**
`p ∤ Cₙ ⟺ (p − 1)·v_p(n+1) + s_p(2n) = 2·s_p(n)`.

This generalises the sibling's parity law: for `p = 2` the right side is
`v₂(n+1) + s₂(n) = 2·s₂(n)`, i.e. `v₂(n+1) = s₂(n)`, which (with the carry identity)
is equivalent to `n + 1` being a power of two. -/
theorem not_dvd_catalan_iff [hp : Fact p.Prime] (n : ℕ) :
    ¬ p ∣ catalan n ↔
      (p - 1) * padicValNat p (n + 1) + (Nat.digits p (2 * n)).sum
        = 2 * (Nat.digits p n).sum := by
  have hcat : catalan n ≠ 0 := catalan_ne_zero n
  have hdvd : p ∣ catalan n ↔ 1 ≤ padicValNat p (catalan n) := by
    rw [← padicValNat_dvd_iff_le hcat, pow_one]
  have hmain := sub_one_mul_padicValNat_catalan (p := p) n
  have hexp : (p - 1) * (padicValNat p (catalan n) + padicValNat p (n + 1))
      = (p - 1) * padicValNat p (catalan n) + (p - 1) * padicValNat p (n + 1) := by ring
  constructor
  · intro h
    have hz : padicValNat p (catalan n) = 0 := by rw [hdvd] at h; omega
    have hβ : (p - 1) * padicValNat p (catalan n) = 0 := by rw [hz, Nat.mul_zero]
    omega
  · intro h
    rw [hdvd]
    intro hle
    have hp2 : 2 ≤ p := hp.out.two_le
    have hzero : (p - 1) * padicValNat p (catalan n) = 0 := by omega
    have : padicValNat p (catalan n) = 0 := by
      rcases Nat.mul_eq_zero.mp hzero with h1 | h2
      · omega
      · exact h2
    omega

/-! ### Concrete example -/

/-- `C₂ = 2` is not divisible by `3`.  The criterion's right side reads
`(3−1)·v₃(3) + s₃(4) = 2·1 + 2 = 4 = 2·s₃(2) = 2·2`, consistent with `3 ∤ C₂`. -/
example : ¬ (3 : ℕ) ∣ catalan 2 := by rw [catalan_two]; decide

end CatalanPAdic
