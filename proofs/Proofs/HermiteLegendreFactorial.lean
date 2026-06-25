/-
# Legendre's Formula through Hermite's Identity

**Legendre's formula** (de Polignac, 1808) gives the `p`-adic valuation of `n!`:
$$v_p(n!) = \sum_{i \ge 1} \left\lfloor \frac{n}{p^{\,i}} \right\rfloor .$$

Mathlib already proves this as `padicValNat_factorial` (the sum being taken over a
finite window `Ico 1 b` once `b > \log_p n`).  What this file adds is a derivation
that routes *each* Legendre summand through **Hermite's identity**
$$\sum_{k=0}^{m-1} \left\lfloor x + \frac{k}{m} \right\rfloor = \lfloor m x \rfloor ,$$
already in the gallery as `HermiteFloorIdentity.hermite_floor_identity`.

## The bridge

Specialising Hermite's identity at `x = n / m^{j+1}` and `m` copies gives
$$\sum_{k=0}^{m-1} \left\lfloor \frac{n}{m^{\,j+1}} + \frac{k}{m} \right\rfloor
   = \left\lfloor m \cdot \frac{n}{m^{\,j+1}} \right\rfloor
   = \left\lfloor \frac{n}{m^{\,j}} \right\rfloor
   = \left\lfloor \frac{n}{m^{\,j}} \right\rfloor_{\mathbb N},$$
the last step because `⌊(n:ℝ)/m^j⌋` is just Euclidean division of naturals.

This is `legendre_summand_split`: it expresses the integer quotient `n / m^j`
that appears in Legendre's sum as a *finer* sum of `m` real floors one level down.
Feeding this into Mathlib's `padicValNat_factorial` term-by-term yields the headline

`legendre_factorial_hermite`:
$$v_p(n!) = \sum_{i=1}^{b-1} \sum_{k=0}^{p-1}
    \left\lfloor \frac{n}{p^{\,i+1}} + \frac{k}{p} \right\rfloor .$$

So Legendre's count of carries is rewritten entirely in terms of Hermite floor
sums — every quotient `⌊n/p^i⌋` is resolved into the Hermite refinement at the
next level.  This is an exposition/synthesis result: the Legendre core is cited
from Mathlib, while the Hermite layer (`legendre_summand_split` and the headline)
is the new content.  No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib
import Proofs.HermiteFloorIdentity

open Finset

namespace HermiteLegendreFactorial

/-- The real floor of `n / m^j` is the Euclidean quotient `n / m^j` of naturals. -/
theorem floor_natCast_div_pow (n m j : ℕ) :
    ⌊(n : ℝ) / (m : ℝ) ^ j⌋ = (↑(n / m ^ j) : ℤ) := by
  have hmj : (m : ℝ) ^ j = ((m ^ j : ℕ) : ℝ) := by push_cast; ring
  rw [hmj, Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]

/-- **Hermite splitting of a Legendre summand.**  For `m ≥ 1` the integer quotient
`n / m^j` that appears in Legendre's formula equals the Hermite floor sum at the
next level: `⌊n / m^j⌋ = ∑_{k<m} ⌊n / m^{j+1} + k/m⌋`. -/
theorem legendre_summand_split (m n j : ℕ) (hm : 0 < m) :
    (↑(n / m ^ j) : ℤ)
      = ∑ k ∈ range m, ⌊(n : ℝ) / (m : ℝ) ^ (j + 1) + (k : ℝ) / (m : ℝ)⌋ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  -- Hermite's identity at `x = n / m^{j+1}`, with `m` copies.
  have h := HermiteFloorIdentity.hermite_floor_identity ((n : ℝ) / (m : ℝ) ^ (j + 1)) m hm
  rw [h]
  -- Collapse `m · (n / m^{j+1})` to `n / m^j`, then identify the floor with `n / m^j`.
  have hmul : (m : ℝ) * ((n : ℝ) / (m : ℝ) ^ (j + 1)) = (n : ℝ) / (m : ℝ) ^ j := by
    have hpj : (m : ℝ) ^ j ≠ 0 := pow_ne_zero _ hm0
    have hpj1 : (m : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hm0
    field_simp
    ring
  rw [hmul, floor_natCast_div_pow]

/-- **Legendre's formula via Hermite's identity.**  For a prime `p` and any bound
`b > log_p n`, the `p`-adic valuation of `n!` is the double Hermite floor sum
`∑_{i=1}^{b-1} ∑_{k=0}^{p-1} ⌊n / p^{i+1} + k/p⌋`.  Each Legendre quotient
`⌊n/p^i⌋` has been replaced by its Hermite refinement one level down. -/
theorem legendre_factorial_hermite (p n b : ℕ) [hp : Fact p.Prime]
    (hb : Nat.log p n < b) :
    (padicValNat p (Nat.factorial n) : ℤ)
      = ∑ i ∈ Finset.Ico 1 b, ∑ k ∈ range p,
          ⌊(n : ℝ) / (p : ℝ) ^ (i + 1) + (k : ℝ) / (p : ℝ)⌋ := by
  have hleg : padicValNat p (Nat.factorial n) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
    padicValNat_factorial (p := p) (hnb := hb)
  rw [hleg, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact legendre_summand_split p n i hp.out.pos

end HermiteLegendreFactorial
