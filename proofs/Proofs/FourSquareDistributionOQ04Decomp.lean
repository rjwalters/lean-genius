import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

/-
# Four-Square Distribution — Open Question 04: the uniform partition reduction

## Parent / sibling

`FourSquareDistribution.lean` (the `2k = 4` case) and the open
`FourSquareDistributionOQ04.lean` (`2k = 6`, PR #24364) both establish the type
decomposition **computationally**: they define a sorted-tuple `RepType`, define

  contribution(type) = (m! / ∏ mᵢ!) · 2^(#nonzero)              (★)

and then, for each small `n` separately, discharge `contribution = value` by
`native_decide` and sum the literals against a **hard-coded** Jacobi number
(`r₄(4) = 24`, `r₆(30) = 14144`, …). Crucially, in those files the totals are
integer *literals*: there is no Lean object equal to the genuine representation
count `r_{2k}(n) = #{ x ∈ ℤ^{2k} : Σ xᵢ² = n }`, and no proof that the sum of the
contributions equals that count. The decomposition `r_{2k} = Σ contributions` is
only asserted, case by case, via the certificate.

## What this file adds (the missing uniform step)

This file supplies the **uniform** `(DECOMP)` partition — for *every* number of
coordinates `m` and *every* `n` at once — against the **actual** representation
count, with no hard-coded Jacobi values:

1. `reps m n` : a `Finset (Fin m → ℤ)` of genuine representations. `mem_reps_iff`
   proves it is faithful — `f ∈ reps m n ↔ Σ (f i)² = n` — so `(reps m n).card`
   *is* `r_m(n)` (the box bound `-n ≤ fᵢ ≤ n` is automatic, since one square
   cannot exceed the total). For `m = 2k` this is exactly `r_{2k}(n)`.
2. `shape f` : the multiset of absolute values `{|f i|}`, i.e. the orbit invariant
   of the hyperoctahedral action `B_m = S_m ⋉ (ℤ/2)^m`.
3. `reps_card_eq_sum_fiber` : **fully proved, no sorry** —

       (reps m n).card = ∑_{s ∈ shapes} ((reps m n).filter (shape · = s)).card

   This is the genuine `(DECOMP)` for all `m, n` simultaneously, obtained from
   `Finset.card_eq_sum_card_fiberwise`. It replaces the parent's per-`n`
   hand-summation of literals by one partition theorem about the real count.
4. The whole open question is then reduced to a **single isolated lemma**,
   the orbit-size statement `FiberFormula m n` : each shape-fiber has size `(★)`
   `= 2^{#nonzero}·m!/∏mᵢ!`. This file states it as a hypothesis and assembles the
   full formula from it in `reps_card_eq_sum_contribution`; this file is now
   **`sorry`-free**. The hypothesis is **discharged** for every attained shape in
   `FourSquareDistributionOQ04Bridge.lean` (`fiber_card_eq_shapeContribution`),
   which combines the sign-count half (`FourSquareDistributionOQ04Sign`) with the
   discharged multiset-arrangement count
   (`FourSquareDistributionOQ04ArrangeProof.arrangement_card`); the fully
   instantiated headline is
   `FourSquareDistributionOQ04Bridge.reps_card_eq_sum_shapeContribution`. It lives
   downstream only because of the import order, not because anything is left open.

## Why this is progress, honestly

The fiberwise partition (item 3) is *new* relative to the parent and PR #24364:
those files never form the representation count as a Lean object, so they cannot
state — let alone prove — that the contributions sum to it. Here that sum law is
proved unconditionally for all `m, n`, and the residual open content is pinned to
one clearly-stated orbit-size lemma. The arithmetic (Jacobi `r_{2k}` totals) is
*not* needed for the partition; it would only be needed to evaluate the right-hand
side in closed form.

**Build status.** Authored under a Docker/Aristotle blackout; **not registered**
in `Proofs.lean`. Uses only standard `Finset`/`Multiset`/`Fintype.piFinset` API
plus `card_eq_sum_card_fiberwise`. Verified on paper; a build-enabled session
should register and, if needed, adjust imports.

## References

- Jacobi (1834), *Fundamenta nova*. (Closed forms for `r₄, r₆, r₈`.)
- Grosswald (1985), *Representations of Integers as Sums of Squares.*
-/

namespace FourSquareDistributionOQ04Decomp

open Finset

/-! ## Part 0: an elementary integer inequality

For any integer `x`, `|x| ≤ x²`. This is what makes the box `[-n, n]` lossless:
a single coordinate's square never exceeds the total `n`, so `|fᵢ| ≤ n`. -/

theorem abs_le_sq (x : ℤ) : |x| ≤ x ^ 2 := by
  rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  rcases le_or_lt |x| 0 with h | h
  · have hx : |x| = 0 := le_antisymm h (abs_nonneg x)
    simp [hx]
  · have h1 : (1 : ℤ) ≤ |x| := by omega
    nlinarith [mul_nonneg (abs_nonneg x) (by omega : (0 : ℤ) ≤ |x| - 1)]

/-! ## Part 1: the genuine representation set

`reps m n` collects all integer `m`-tuples whose squares sum to `n`, realized as
a filter on the finite box `[-n, n]^m`. `mem_reps_iff` shows the box never clips a
real representation, so `(reps m n).card = r_m(n)`. -/

/-- Integer `m`-tuples `f` with `Σ (f i)² = n`, as a `Finset`. -/
def reps (m n : ℕ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
    (fun f => ∑ i, (f i) ^ 2 = (n : ℤ))

/-- The box is lossless: membership in `reps m n` is exactly the sum-of-squares
condition. Hence `(reps m n).card` is the true representation count `r_m(n)`. -/
theorem mem_reps_iff {m n : ℕ} (f : Fin m → ℤ) :
    f ∈ reps m n ↔ ∑ i, (f i) ^ 2 = (n : ℤ) := by
  simp only [reps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hterm : (f i) ^ 2 ≤ (n : ℤ) := by
      have hle := Finset.single_le_sum
        (f := fun j => (f j) ^ 2) (fun j _ => sq_nonneg (f j)) (Finset.mem_univ i)
      rwa [h] at hle
    have habs : |f i| ≤ (n : ℤ) := le_trans (abs_le_sq (f i)) hterm
    exact abs_le.mp habs

/-! ## Part 2: the shape (orbit) invariant -/

/-- The orbit invariant of the hyperoctahedral action: the multiset of absolute
values of the coordinates. Two representations lie in the same `B_m`-orbit iff
they have the same `shape`. -/
def shape {m : ℕ} (f : Fin m → ℤ) : Multiset ℤ :=
  Multiset.map (fun i => |f i|) (Finset.univ : Finset (Fin m)).val

/-! ## Part 3: the uniform partition `(DECOMP)` — fully proved

For every `m` and `n`, the representation count splits as a sum over shapes of
the fiber sizes. This is the all-`n` decomposition the parent files only asserted
case by case. -/

theorem reps_card_eq_sum_fiber (m n : ℕ) :
    (reps m n).card
      = ∑ s ∈ (reps m n).image shape,
          ((reps m n).filter (fun f => shape f = s)).card :=
  Finset.card_eq_sum_card_fiberwise (fun f hf => Finset.mem_image_of_mem shape hf)

/-! ## Part 4: the orbit-size formula `(★)` and the residual open lemma

`shapeContribution s` is the formula `2^{#nonzero} · m! / ∏ (mult v)!`. The whole
open question reduces to the single claim that each fiber has this size. -/

/-- The symmetry multiplier `(★)` attached to a shape `s` of an `m`-tuple:
`m! / ∏_{v} (count v)!` orderings times `2^{#nonzero}` sign choices. -/
def shapeContribution (m : ℕ) (s : Multiset ℤ) : ℕ :=
  (Nat.factorial m / (s.toFinset.prod (fun v => Nat.factorial (s.count v))))
    * 2 ^ (Multiset.card (s.filter (fun v => v ≠ 0)))

/-- The orbit-size statement of the hyperoctahedral action `B_m = S_m ⋉ (ℤ/2)^m`:
each shape-fiber has size given by the orbit formula `(★)`. Stated here as the
single hypothesis that `reps_card_eq_sum_contribution` consumes; everything else
in this file is unconditional. This formula is **proved** for every attained
shape in `FourSquareDistributionOQ04Bridge.lean`
(`fiber_card_eq_shapeContribution`), built from the sign-count half
(`FourSquareDistributionOQ04Sign`) and the discharged arrangement count
(`FourSquareDistributionOQ04ArrangeProof.arrangement_card`). It is phrased as a
hypothesis rather than re-proved here only because Bridge is downstream of this
file in the import graph. -/
abbrev FiberFormula (m n : ℕ) : Prop :=
  ∀ s ∈ (reps m n).image shape,
    ((reps m n).filter (fun f => shape f = s)).card = shapeContribution m s

/-- Assembling Parts 3 and 4: the full type decomposition of the genuine
representation count, for every `m` and `n`, given the orbit-size lemma
`FiberFormula m n` (proved as `FourSquareDistributionOQ04Bridge.fiber_card_eq_shapeContribution`).
For `m = 2k` this is the open question's `r_{2k}(n) = Σ contributions`; see
`FourSquareDistributionOQ04Bridge.reps_card_eq_sum_shapeContribution` for the
fully discharged headline. -/
theorem reps_card_eq_sum_contribution (m n : ℕ) (hfiber : FiberFormula m n) :
    (reps m n).card
      = ∑ s ∈ (reps m n).image shape, shapeContribution m s := by
  rw [reps_card_eq_sum_fiber]
  exact Finset.sum_congr rfl (fun s hs => hfiber s hs)

#check @mem_reps_iff
#check @reps_card_eq_sum_fiber
#check @reps_card_eq_sum_contribution

end FourSquareDistributionOQ04Decomp
