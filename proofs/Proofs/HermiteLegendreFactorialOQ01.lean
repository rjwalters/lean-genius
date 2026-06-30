/-
# Iterating the Hermite Refinement of Legendre's Formula (depth d)

The entry `hermite-legendre-factorial` proves Legendre's formula through one level of
Hermite's identity:
$$\lfloor n/m^j\rfloor = \sum_{k=0}^{m-1}\Big\lfloor \frac{n}{m^{j+1}} + \frac{k}{m}\Big\rfloor
  \qquad(\text{`legendre_summand_split`}).$$
It poses the open question: *iterate the refinement to depth `d`, so `v_p(n!)` becomes a
`(d+1)`-fold Hermite floor sum — characterise the resulting nested expression.*

This file answers that question. The characterisation is clean:

> **Iterating the refinement `d` times collapses to a single Hermite floor sum at modulus
> `m^d`.** A `d`-fold nested Hermite refinement of the Legendre summand is *equal* to one
> Hermite split at the `d`-th prime power.

Concretely we prove:

* `legendre_summand_split_depth` — the flat depth-`d` form
  $$\lfloor n/m^j\rfloor = \sum_{k=0}^{m^d-1}\Big\lfloor \frac{n}{m^{j+d}} + \frac{k}{m^d}\Big\rfloor,$$
  obtained directly from Hermite's identity with `m^d` copies at `x = n/m^{j+d}`. At `d = 1`
  this is exactly the parent `legendre_summand_split`; at `d = 0` it is the identity.

* `legendre_summand_refine_step` — the *single iteration step*: one Hermite split takes a
  depth-`d` term to `m` depth-`(d+1)` terms,
  $$\Big\lfloor \frac{n}{m^{j+d}} + \frac{k}{m^d}\Big\rfloor
    = \sum_{k'=0}^{m-1}\Big\lfloor \frac{n}{m^{j+d+1}} + \frac{k + k' m^d}{m^{d+1}}\Big\rfloor,$$
  with the new mixed-radix index `k + k' m^d`. This is the literal "iterate" — applying it
  `d` times to `legendre_summand_split` reproduces the depth-`d` form.

* `legendre_iterate_collapse` — the characterisation: the depth-`d` and depth-`(d+1)` flat
  sums agree (both equal `n/m^j`), so deepening the refinement merely re-indexes one Hermite
  sum into the next finer one; no genuinely new "nested closed form" appears beyond the single
  `m^d`-term Hermite sum.

* `legendre_factorial_hermite_depth` — the headline: for a prime `p`,
  $$v_p(n!) = \sum_{i=1}^{b-1}\sum_{k=0}^{p^d-1}\Big\lfloor \frac{n}{p^{i+d}} + \frac{k}{p^d}\Big\rfloor.$$

The Legendre core is cited from Mathlib (`padicValNat_factorial`); the depth-`d` Hermite layer
is the new content. No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib
import Proofs.HermiteFloorIdentity
import Proofs.HermiteLegendreFactorial

open Finset

namespace HermiteLegendreFactorialOQ01

/-- **Flat depth-`d` Hermite split of a Legendre summand.**  For `m ≥ 1`, the integer quotient
`n / m^j` equals a single Hermite floor sum of `m^d` terms taken `d` levels down:
`⌊n/m^j⌋ = ∑_{k<m^d} ⌊n/m^{j+d} + k/m^d⌋`.  This is Hermite's identity applied with `m^d`
copies at `x = n/m^{j+d}` — the `d`-fold iterated refinement collapsed into one sum. -/
theorem legendre_summand_split_depth (m n j d : ℕ) (hm : 0 < m) :
    (↑(n / m ^ j) : ℤ)
      = ∑ k ∈ range (m ^ d), ⌊(n : ℝ) / (m : ℝ) ^ (j + d) + (k : ℝ) / (m : ℝ) ^ d⌋ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hmd : 0 < m ^ d := pow_pos hm d
  have hjd : (m : ℝ) ^ j ≠ 0 := pow_ne_zero _ hm0
  have hdd : (m : ℝ) ^ d ≠ 0 := pow_ne_zero _ hm0
  -- Hermite's identity at `x = n / m^{j+d}` with `m^d` copies.
  have h := HermiteFloorIdentity.hermite_floor_identity ((n : ℝ) / (m : ℝ) ^ (j + d)) (m ^ d) hmd
  push_cast at h
  -- `m^d · (n / m^{j+d}) = n / m^j`, then identify the real floor with the natural quotient.
  have hmul : (m : ℝ) ^ d * ((n : ℝ) / (m : ℝ) ^ (j + d)) = (n : ℝ) / (m : ℝ) ^ j := by
    rw [pow_add]
    field_simp
  rw [h, hmul, HermiteLegendreFactorial.floor_natCast_div_pow]

/-- **Single iteration step.**  One Hermite split refines a depth-`d` floor term into `m`
depth-`(d+1)` terms, with the new index `k + k'·m^d` running through a finer residue:
`⌊n/m^{j+d} + k/m^d⌋ = ∑_{k'<m} ⌊n/m^{j+d+1} + (k + k'·m^d)/m^{d+1}⌋`.  Applying this `d`
times to `legendre_summand_split` is precisely "iterating the refinement". -/
theorem legendre_summand_refine_step (m n j d k : ℕ) (hm : 0 < m) :
    ⌊(n : ℝ) / (m : ℝ) ^ (j + d) + (k : ℝ) / (m : ℝ) ^ d⌋
      = ∑ k' ∈ range m,
          ⌊(n : ℝ) / (m : ℝ) ^ (j + d + 1)
              + ((k : ℝ) + (k' : ℝ) * (m : ℝ) ^ d) / (m : ℝ) ^ (d + 1)⌋ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  -- Hermite's identity at `x = n/m^{j+d+1} + k/m^{d+1}` with `m` copies.
  have h := HermiteFloorIdentity.hermite_floor_identity
      ((n : ℝ) / (m : ℝ) ^ (j + d + 1) + (k : ℝ) / (m : ℝ) ^ (d + 1)) m hm
  -- `m · x = n/m^{j+d} + k/m^d`, the depth-`d` term being refined.
  have hx : (m : ℝ) * ((n : ℝ) / (m : ℝ) ^ (j + d + 1) + (k : ℝ) / (m : ℝ) ^ (d + 1))
      = (n : ℝ) / (m : ℝ) ^ (j + d) + (k : ℝ) / (m : ℝ) ^ d := by
    field_simp
    ring
  rw [hx] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  congr 1
  field_simp
  ring

/-- **Collapse characterisation.**  Refining one level deeper does not produce a new nested
closed form: the depth-`d` Hermite sum and the depth-`(d+1)` Hermite sum are equal (both count
`n/m^j`).  Iterating the refinement merely re-indexes a single Hermite sum into the next finer
one — the answer to the open question is that the `(d+1)`-fold nesting *is* the single
`m^d`-term Hermite split (`legendre_summand_split_depth`). -/
theorem legendre_iterate_collapse (m n j d : ℕ) (hm : 0 < m) :
    ∑ k ∈ range (m ^ d), ⌊(n : ℝ) / (m : ℝ) ^ (j + d) + (k : ℝ) / (m : ℝ) ^ d⌋
      = ∑ k ∈ range (m ^ (d + 1)),
          ⌊(n : ℝ) / (m : ℝ) ^ (j + (d + 1)) + (k : ℝ) / (m : ℝ) ^ (d + 1)⌋ := by
  rw [← legendre_summand_split_depth m n j d hm,
      ← legendre_summand_split_depth m n j (d + 1) hm]

/-- The depth-`1` specialisation recovers the parent `legendre_summand_split`:
`⌊n/m^j⌋ = ∑_{k<m} ⌊n/m^{j+1} + k/m⌋`. -/
theorem legendre_summand_split_depth_one (m n j : ℕ) (hm : 0 < m) :
    (↑(n / m ^ j) : ℤ)
      = ∑ k ∈ range m, ⌊(n : ℝ) / (m : ℝ) ^ (j + 1) + (k : ℝ) / (m : ℝ)⌋ := by
  have h := legendre_summand_split_depth m n j 1 hm
  simpa using h

/-- **Legendre's formula at depth `d` via Hermite.**  For a prime `p` and any bound
`b > log_p n`, the `p`-adic valuation of `n!` is the depth-`d` Hermite floor sum
`∑_{i=1}^{b-1} ∑_{k<p^d} ⌊n/p^{i+d} + k/p^d⌋`.  Each Legendre quotient `⌊n/p^i⌋` is replaced by
its `m^d`-term Hermite refinement `d` levels down. -/
theorem legendre_factorial_hermite_depth (p n b d : ℕ) [hp : Fact p.Prime]
    (hb : Nat.log p n < b) :
    (padicValNat p (Nat.factorial n) : ℤ)
      = ∑ i ∈ Finset.Ico 1 b, ∑ k ∈ range (p ^ d),
          ⌊(n : ℝ) / (p : ℝ) ^ (i + d) + (k : ℝ) / (p : ℝ) ^ d⌋ := by
  have hleg : padicValNat p (Nat.factorial n) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i :=
    padicValNat_factorial (p := p) (hnb := hb)
  rw [hleg, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact legendre_summand_split_depth p n i d hp.out.pos

end HermiteLegendreFactorialOQ01
