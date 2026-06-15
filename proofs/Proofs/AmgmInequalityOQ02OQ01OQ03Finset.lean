/-
# Newton–Girard k = 3 over a concrete Finset (amgm-inequality-oq-02-oq-01-oq-03)

problem.md asks for the closed form `p₃ = e₁³ − 3·e₁·e₂ + 3·e₃` in the parent's
**concrete `Finset`** style (elementary symmetric sums via `powersetCard`), not
the `MvPolynomial` API. The universal form is already proved in
`AmgmInequalityOQ02OQ01OQ03.lean` (`psum_three_closed`); this file works toward
the concrete general-Finset statement.

## What is proved here (build-pending; Docker/Aristotle blackout)

- `D_collapse` (L3): `Doff = e₁·p₂ − p₃`, where
  `Doff = ∑ᵢ ∑_{j≠i} fᵢ²·fⱼ`. Elementary `Finset.sum_erase_eq_sub` algebra.
- `offdiag_pair_eq`: `∑ᵢ ∑_{j≠i} fᵢ·fⱼ = e₁² − p₂` (a rearrangement of the
  parent's `sq_sum_eq_diag_plus_offdiag`).
- `two_mul_newton_girard`: `2·p₃ = 2·(e₁³ − 3·e₁·e₂ + 3·e₃)`, the honest extent
  of the ordered-triple **partition route** (Route A), assembled from the two
  combinatorial cruxes (`cube_partition`, `two_e2_eq_off_diag`) plus `D_collapse`
  and `offdiag_pair_eq`. Verified `linear_combination` over an arbitrary
  `CommRing`.

## Finding — Route A cannot prove the bare identity over a general ring

The ordered-triple partition gives `e₁³ = p₃ + 3·Doff + 6·e₃`; combined with the
other relations it determines only **`2·p₃`**, not `p₃`. Dividing by 2 (as the
prior ACT skeleton did) is invalid in characteristic 2: e.g. over `ℤ/2` the four
relations hold yet do not pin `p₃` without a `½`. (The identity `p₃ = e₁³ −
3e₁e₂ + 3e₃` is nonetheless TRUE over every commutative ring — it has integer
coefficients — but proving it in full generality requires **Route B**, the
`aeval` specialization of the universal `psum_three_closed`, not the partition.)

So the genuinely general concrete-Finset theorem (`newton_girard_three_finset`,
left as a documented `sorry`) should be obtained by Route B; `two_mul_newton_girard`
records exactly how far Route A reaches.

## Remaining cruxes (the only `sorry`s here)

- `cube_partition` (L2): `(∑ᵢ fᵢ)³ = p₃ + 3·Doff + 6·e₃` — the
  ordered-triple ↔ `powersetCard 3` bridge (multiplicities 1/3/6, cert-verified).
- `two_e2_eq_off_diag` (L4): `2·e₂ = ∑ᵢ ∑_{j≠i} fᵢ·fⱼ` — the
  `powersetCard 2` ↔ ordered-pair bridge.
- `newton_girard_three_finset`: the general statement, via Route B.

All numeric facts (the 1/3/6 multiplicities, `Doff = e₁p₂ − p₃`, the totals) are
checked in `research/problems/amgm-inequality-oq-02-oq-01-oq-03/lean/verify_newton_girard_k3.py`.

## References

- Mead, D. G. (1992). *Newton's identities.* Amer. Math. Monthly 99, 749–751.
-/

import Mathlib
import Proofs.AMGMInequalityOQ02OQ01

namespace AmgmFinsetNewtonGirardK3

open Finset BigOperators

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

noncomputable def e1 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i
noncomputable def e2 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, f i
noncomputable def e3 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, f i
def p2 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 2
def p3 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 3
def Doff (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, ∑ j ∈ s.erase i, f i ^ 2 * f j

/-- (L3) `Doff = e₁·p₂ − p₃`. Pull the constant `fᵢ²` out of the inner sum, use
`∑_{j≠i} fⱼ = e₁ − fᵢ`, and distribute. -/
theorem D_collapse (s : Finset ι) (f : ι → R) :
    Doff s f = e1 s f * p2 s f - p3 s f := by
  have key : ∀ i ∈ s, ∑ j ∈ s.erase i, f i ^ 2 * f j
      = f i ^ 2 * (∑ j ∈ s, f j) - f i ^ 3 := by
    intro i hi
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hi]
    ring
  unfold Doff e1 p2 p3
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- The ordered distinct-pair sum equals `e₁² − p₂` (rearranged parent k = 2). -/
theorem offdiag_pair_eq (s : Finset ι) (f : ι → R) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j = e1 s f ^ 2 - p2 s f := by
  have h := AMGMInequalityOQ02OQ01.sq_sum_eq_diag_plus_offdiag s f
  unfold e1 p2
  linear_combination -h

/-! ## The two combinatorial cruxes (powerset ↔ ordered-tuple bridges) -/

/-- (L2) CRUX — the ordered-triple partition (multiplicities 1/3/6). -/
theorem cube_partition (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ 3 = p3 s f + 3 * Doff s f + 6 * e3 s f := by
  sorry

/-- (L4) CRUX — each 2-subset is two ordered pairs. -/
theorem two_e2_eq_off_diag (s : Finset ι) (f : ι → R) :
    2 * e2 s f = ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
  sorry

/-- **Route A endpoint.** The partition route determines only `2·p₃`:
`2·p₃ = 2·(e₁³ − 3·e₁·e₂ + 3·e₃)`. Valid over any `CommRing`; concluding the bare
identity from here would need to cancel `2`, which fails in characteristic 2. -/
theorem two_mul_newton_girard (s : Finset ι) (f : ι → R) :
    2 * p3 s f = 2 * (e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f) := by
  have hL2 := cube_partition s f
  have hL3 := D_collapse s f
  have hL4 := two_e2_eq_off_diag s f
  have hpar := AMGMInequalityOQ02OQ01.sq_sum_eq_diag_plus_offdiag s f
  simp only [e1, e2, e3, p2, p3, Doff] at hL2 hL3 hL4 ⊢
  linear_combination hL2 + 3 * hL3
    + 3 * (∑ i ∈ s, f i) * hL4 - 3 * (∑ i ∈ s, f i) * hpar

/-- **Main target (general concrete Finset).** True over every `CommRing`; obtain
via Route B (`aeval` of the universal `psum_three_closed`), since Route A reaches
only `two_mul_newton_girard`. -/
theorem newton_girard_three_finset (s : Finset ι) (f : ι → R) :
    p3 s f = e1 s f ^ 3 - 3 * (e1 s f * e2 s f) + 3 * e3 s f := by
  sorry

#check @D_collapse
#check @offdiag_pair_eq
#check @two_mul_newton_girard

end AmgmFinsetNewtonGirardK3
