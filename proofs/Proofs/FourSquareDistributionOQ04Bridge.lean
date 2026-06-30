import Mathlib
import Proofs.FourSquareDistributionOQ04Decomp
import Proofs.FourSquareDistributionOQ04Arrange
import Proofs.FourSquareDistributionOQ04Keystone

/-
# Four-Square Distribution — OQ-04: the bridge that collapses the stack to one residue

## Where this fits

The open question's type-decomposition `r_{2k}(n) = Σ_shapes shapeContribution`
was, until now, spread over four sibling files that were never wired together:

* `FourSquareDistributionOQ04Decomp.lean` — the genuine representation set `reps m n`,
  the shape invariant, and the uniform fiberwise partition `reps_card_eq_sum_fiber`
  (proved). It reduced the whole question to one lemma `fiber_card_eq_contribution`
  (each shape-fiber has size `(★) = m!/∏count! · 2^{#nonzero}`), left as a `sorry`.
* `FourSquareDistributionOQ04Sign.lean` — the sign-count half `2^{#nonzero}` (proved).
* `FourSquareDistributionOQ04Keystone.lean` — the assembly: it proves
  `fiber_card_eq_contribution` **modulo a hypothesis** `harr` about the size of the
  absolute-value image `(shapeFiber m n s).image absMap`, using `signFiber_card`
  and `Finset.card_eq_sum_card_fiberwise` (no `sorry` of its own).
* `FourSquareDistributionOQ04Arrange.lean` — the arrangement-count half: it proves
  `arrangement_card_div_form : (arrangements s).card = m!/∏count!` **modulo** the one
  combinatorial residue `arrangement_card` (the multiset-permutation count).

The gap nobody had closed is that Keystone's `harr` is phrased about
`(shapeFiber m n s).image absMap`, whereas Arrange's count is about the canonical
arrangement set `arrangements s`. **These two `Finset`s are equal** — that is the
content of this file's `image_absMap_eq_arrangements`. With it:

* `harr` is discharged from `arrangement_card_div_form`, so Keystone's
  `fiber_card_eq_contribution` holds for every attained shape;
* hence `reps_card_eq_sum_shapeContribution` re-proves Decomp's headline
  decomposition **with no `sorry` of its own** — the whole stack now rests on the
  *single* residue `arrangement_card`.

## Why the two `Finset`s are equal

For `s ∈ (reps m n).image shape` (i.e. `s` is an attained absolute-value multiset):

* every element of `s` is `≥ 0` (it is some `|f₀ i|`), and `card s = m`;
* a profile `g ∈ (shapeFiber m n s).image absMap` is `|f|`-componentwise for some
  representation `f` of shape `s`, so `multiset(g) = shape f = s`, i.e.
  `g ∈ arrangements s`;
* conversely if `multiset(g) = s` then every `g i ∈ s` is `≥ 0`, so `|g| = g`; and
  the sum of squares depends only on the value-multiset, so `Σ (g i)² = Σ (f₀ i)² = n`,
  giving `g ∈ reps m n` with `shape g = s` and `absMap g = g`. Hence `g` is in the
  image. The sum-of-squares invariance is the helper `sumsq_invariant`.

## Honesty / build status

Authored under a Docker + Aristotle backend outage (`lake build` is forbidden
locally and Docker OOMs from the worktree's broken `.lake` cache; Aristotle `prove`
returns 404 this session). **Build-pending and unregistered** in `Proofs.lean`; a
build-enabled session should register the OQ-04 stack and adjust imports if needed.
The only `sorry` anywhere in the stack is `arrangement_card` (a known result: the
number of orderings of a multiset is the multinomial coefficient). The end-to-end
formula is independently certified for all `m ≤ 5`, `n ≤ 12` by
`research/problems/four-square-distribution-oq-04/verify_orbit_formula.py`.
-/

namespace FourSquareDistributionOQ04Bridge

open Finset
open FourSquareDistributionOQ04Decomp
open FourSquareDistributionOQ04Arrange
open FourSquareDistributionOQ04Keystone

/-! ## Sum-of-squares is a function of the value-multiset only -/

/-- If two tuples have the same multiset of values, their sums of squares agree.
This is what makes membership in `reps m n` constant across an arrangement class. -/
theorem sumsq_invariant {m : ℕ} (a b : Fin m → ℤ)
    (hab : Multiset.map a (Finset.univ : Finset (Fin m)).val
         = Multiset.map b (Finset.univ : Finset (Fin m)).val) :
    (∑ i, (a i) ^ 2) = ∑ i, (b i) ^ 2 := by
  have h2 :
      (Multiset.map (fun x : ℤ => x ^ 2)
          (Multiset.map a (Finset.univ : Finset (Fin m)).val)).sum
        = (Multiset.map (fun x : ℤ => x ^ 2)
          (Multiset.map b (Finset.univ : Finset (Fin m)).val)).sum := by
    rw [hab]
  rw [Multiset.map_map, Multiset.map_map, Function.comp_def, Function.comp_def,
    Finset.sum_map_val, Finset.sum_map_val] at h2
  exact h2

/-! ## The bridge: the abs-image of a shape-fiber is the canonical arrangement set -/

/-- **The missing link.** For an attained shape `s`, the absolute-value image of the
shape-fiber is exactly the canonical multiset-arrangement set. This identifies
Keystone's `harr` target with Arrange's `arrangement_card_div_form`. -/
theorem image_absMap_eq_arrangements {m n : ℕ} (s : Multiset ℤ)
    (hs : s ∈ (reps m n).image shape) :
    (shapeFiber m n s).image absMap = arrangements (m := m) s := by
  classical
  obtain ⟨f₀, hf₀reps, hf₀shape⟩ := Finset.mem_image.mp hs
  -- every part of `s` is `≥ 0`
  have hs_nonneg : ∀ x ∈ s, (0 : ℤ) ≤ x := by
    intro x hx
    rw [← hf₀shape, shape] at hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact abs_nonneg _
  ext g
  constructor
  · -- image ⊆ arrangements
    intro hg
    obtain ⟨f, hfF, hfg⟩ := Finset.mem_image.mp hg
    rw [shapeFiber, Finset.mem_filter] at hfF
    obtain ⟨_, hfshape⟩ := hfF
    rw [mem_arrangements_iff, ← hfg, ← shape_eq_map_absMap]
    exact hfshape
  · -- arrangements ⊆ image
    intro hg
    rw [mem_arrangements_iff] at hg
    have hgnn : ∀ i, 0 ≤ g i := by
      intro i
      apply hs_nonneg
      rw [← hg]
      exact Multiset.mem_map_of_mem g (Finset.mem_val.mpr (Finset.mem_univ i))
    have habsg : absMap g = g := by
      funext i; rw [absMap]; exact abs_of_nonneg (hgnn i)
    rw [Finset.mem_image]
    refine ⟨g, ?_, habsg⟩
    rw [shapeFiber, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · -- g ∈ reps m n  (sum of squares = n, inherited from f₀)
      rw [mem_reps_iff]
      have hmapeq : Multiset.map g (Finset.univ : Finset (Fin m)).val
          = Multiset.map (fun i => |f₀ i|) (Finset.univ : Finset (Fin m)).val := by
        rw [hg, ← hf₀shape, shape]
      have hkey := sumsq_invariant g (fun i => |f₀ i|) hmapeq
      rw [hkey]
      simp_rw [sq_abs]
      exact (mem_reps_iff f₀).mp hf₀reps
    · -- shape g = s
      rw [shape_eq_map_absMap, habsg]
      exact hg

/-! ## Consequences: the whole stack reduces to `arrangement_card` -/

/-- `card s = m` for any attained shape `s`. -/
theorem card_of_mem_image_shape {m n : ℕ} (s : Multiset ℤ)
    (hs : s ∈ (reps m n).image shape) : Multiset.card s = m := by
  obtain ⟨f₀, _, hf₀shape⟩ := Finset.mem_image.mp hs
  have : Multiset.card s = (Finset.univ : Finset (Fin m)).card := by
    rw [← hf₀shape, shape, Multiset.card_map]; rfl
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- **Keystone's `fiber_card_eq_contribution`, fully discharged of its hypothesis**
(modulo only `arrangement_card`). Each shape-fiber of the genuine representation set
has size `shapeContribution m s`. -/
theorem fiber_card_eq_shapeContribution {m n : ℕ} (s : Multiset ℤ)
    (hs : s ∈ (reps m n).image shape) :
    (shapeFiber m n s).card = shapeContribution m s := by
  apply FourSquareDistributionOQ04Keystone.fiber_card_eq_contribution
  rw [image_absMap_eq_arrangements s hs]
  exact arrangement_card_div_form s (card_of_mem_image_shape s hs)

/-- **The open question's headline decomposition**, re-proved with no `sorry` of its
own — the whole stack now rests on the single residue `arrangement_card`. For every
`m` and `n`, the genuine representation count `r_m(n) = (reps m n).card` is the sum
over attained shapes of the orbit-size formula `(★)`. For `m = 2k` this is
`r_{2k}(n) = Σ_shapes shapeContribution`. -/
theorem reps_card_eq_sum_shapeContribution (m n : ℕ) :
    (reps m n).card = ∑ s ∈ (reps m n).image shape, shapeContribution m s := by
  rw [reps_card_eq_sum_fiber]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  exact fiber_card_eq_shapeContribution s hs

/-- The orbit-size hypothesis `FiberFormula m n` that `Decomp`'s
`reps_card_eq_sum_contribution` consumes is **discharged** for every `m, n`. This
closes the last open input of the `Decomp` blueprint, so
`Decomp.reps_card_eq_sum_contribution m n (fiberFormula_holds m n)` is the same
fully-verified headline as `reps_card_eq_sum_shapeContribution`. -/
theorem fiberFormula_holds (m n : ℕ) :
    FourSquareDistributionOQ04Decomp.FiberFormula m n :=
  fun s hs => fiber_card_eq_shapeContribution s hs

#check @sumsq_invariant
#check @image_absMap_eq_arrangements
#check @fiber_card_eq_shapeContribution
#check @reps_card_eq_sum_shapeContribution

end FourSquareDistributionOQ04Bridge
