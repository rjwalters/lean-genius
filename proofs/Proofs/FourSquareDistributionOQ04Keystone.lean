import Mathlib
import Proofs.FourSquareDistributionOQ04Decomp
import Proofs.FourSquareDistributionOQ04Sign

/-
# Four-Square Distribution — OQ-04: the keystone assembly

## Where this fits

The open question reduces, via `FourSquareDistributionOQ04Decomp.lean`, to one
orbit-size lemma `fiber_card_eq_contribution`: each `shape`-fiber of the genuine
representation set `reps m n` has size

  (★)   `m! / ∏_v (count_v s)! · 2^{#nonzero}`.

Two pieces of `(★)` are already in place on `main`:

* `FourSquareDistributionOQ04Sign.signFiber_card` — the **sign-count half**
  `2^{#nonzero}` (the number of sign-flips of a fixed coordinate profile), proved
  unconditionally;
* the **arrangement-count half** `m! / ∏_v (count_v)!` — the multiset-permutation
  count, isolated as the single residue `arrangement_card` (canonical
  `Nat.multinomial` form set up in PR #24518).

The Sign file's trailing blueprint lists the remaining bookkeeping as steps 1 & 3:
(1) each fiber of the coordinatewise absolute-value map equals a `signFiber`, and
(3) assemble the keystone from the fiberwise sum. **Those two steps were described
but never encoded in Lean.** This file encodes them.

## What this file proves (all unconditional except the named residue)

* `absFiber_eq_signFiber` — step (1): for an absolute-value profile `g` realized on
  the shape-fiber, the set of representations with `|f ·| = g` is *exactly*
  `signFiber g`. (Every sign-flip of a representation is again a representation of
  the same shape; conversely a fiber element is recovered up to coordinate signs.)
* `nonzero_card_eq` — the `#nonzero` bridge: the number of nonzero coordinates of
  such a `g` equals `#nonzero s` (constant across the fiber), via
  `Multiset.countP_map`.
* `shapeFiber_card_eq_arrangements_mul` — step (3), **unconditional**: the
  shape-fiber size is `(#abs-profiles) · 2^{#nonzero s}`, i.e. the arrangement
  count times the sign count, by `Finset.card_eq_sum_card_fiberwise` over the
  absolute-value map.
* `fiber_card_eq_contribution` — the Decomp keystone, derived from the previous
  line **modulo the single arrangement-count residue** supplied as a hypothesis
  `harr` (exactly the statement of #24518's `arrangement_card_div_form`, identified
  with the abs-profile image here). With `harr` discharged, this *is* the open
  question for every `m, n`.

This file therefore collapses the entire open question to the one combinatorial
lemma `arrangement_card`, with **no `sorry` of its own** — the residue is an
explicit hypothesis, not an axiom or `sorry`.

## Honesty / build status

Authored under a Docker + Aristotle backend outage (`docker info` timed out;
Aristotle `prove` previously returned 404), so this is **build-pending** and
**unregistered** in `Proofs.lean`; a build-enabled session should register it and
adjust any imports. It uses only `Finset`/`Multiset`/`Fintype.piFinset` API with
the repo-precedented lemmas `Finset.card_eq_sum_card_fiberwise`,
`Multiset.countP_map`, `Multiset.countP_eq_card_filter`. The end-to-end claim
(fiber size `= (★)`) is independently certified for all `m ≤ 5`, `n ≤ 12` by
`research/problems/four-square-distribution-oq-04/verify_orbit_formula.py`.
-/

namespace FourSquareDistributionOQ04Keystone

open Finset
open FourSquareDistributionOQ04Decomp
open FourSquareDistributionOQ04Sign

/-- The coordinatewise absolute-value profile of a tuple. Note `shape f` is exactly
`Multiset.map (absMap f) univ.val`. -/
def absMap {m : ℕ} (f : Fin m → ℤ) : Fin m → ℤ := fun i => |f i|

/-- The shape-fiber: representations of `n` whose absolute-value multiset is `s`. -/
def shapeFiber (m n : ℕ) (s : Multiset ℤ) : Finset (Fin m → ℤ) :=
  (reps m n).filter (fun f => shape f = s)

theorem shape_eq_map_absMap {m : ℕ} (f : Fin m → ℤ) :
    shape f = Multiset.map (absMap f) (Finset.univ : Finset (Fin m)).val := rfl

/-! ## Step 1: each abs-profile fiber is a `signFiber` -/

/-- **Step (1) of the Sign-file blueprint.** For an absolute-value profile `g`
attained on the shape-fiber, the representations with `absMap f = g` are exactly
the sign-flips `signFiber g`. -/
theorem absFiber_eq_signFiber {m n : ℕ} (s : Multiset ℤ) (g : Fin m → ℤ)
    (hg : g ∈ (shapeFiber m n s).image absMap) :
    (shapeFiber m n s).filter (fun f => absMap f = g) = signFiber g := by
  classical
  obtain ⟨f₀, hf₀F, hf₀g⟩ := Finset.mem_image.mp hg
  obtain ⟨hf₀reps, hf₀shape⟩ := Finset.mem_filter.mp hf₀F
  -- The witness gives: `g ≥ 0`, `multiset(g) = s`, and `Σ (g i)² = n`.
  have hgnonneg : ∀ i, 0 ≤ g i := by
    intro i; rw [← hf₀g]; exact abs_nonneg _
  have hms : Multiset.map g (Finset.univ : Finset (Fin m)).val = s := by
    rw [← hf₀g]; exact hf₀shape
  have hsum : ∑ i, (g i) ^ 2 = (n : ℤ) := by
    have hsq : ∀ i, (g i) ^ 2 = (f₀ i) ^ 2 := by
      intro i; rw [← hf₀g]; exact sq_abs (f₀ i)
    simp_rw [hsq]; exact (mem_reps_iff f₀).mp hf₀reps
  ext f
  simp only [shapeFiber, Finset.mem_filter, signFiber, Fintype.mem_piFinset,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · -- A fiber element is a sign-flip of `g`.
    rintro ⟨⟨_, _⟩, hfabs⟩ i
    have habs : |f i| = g i := congrFun hfabs i
    rcases abs_cases (f i) with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; rw [← h1, habs]
    · right; rw [h1] at habs; linarith [habs]
  · -- A sign-flip of `g` is a representation of shape `s` with profile `g`.
    intro hf
    have habs : ∀ i, |f i| = g i := by
      intro i
      rcases hf i with h | h
      · rw [h, abs_of_nonneg (hgnonneg i)]
      · rw [h, abs_neg, abs_of_nonneg (hgnonneg i)]
    have hfabs : absMap f = g := funext habs
    have hsqeq : ∀ i, (f i) ^ 2 = (g i) ^ 2 := by
      intro i; rw [← sq_abs (f i), habs i]
    have hfreps : f ∈ reps m n := by
      rw [mem_reps_iff]; simp_rw [hsqeq]; exact hsum
    have hfshape : shape f = s := by
      rw [shape_eq_map_absMap, hfabs]; exact hms
    exact ⟨⟨hfreps, hfshape⟩, hfabs⟩

/-! ## The `#nonzero` bridge -/

/-- The number of nonzero coordinates of an attained abs-profile `g` equals the
number of nonzero parts of `s` (constant across the shape-fiber). -/
theorem nonzero_card_eq {m n : ℕ} (s : Multiset ℤ) (g : Fin m → ℤ)
    (hg : g ∈ (shapeFiber m n s).image absMap) :
    ((Finset.univ : Finset (Fin m)).filter (fun i => g i ≠ 0)).card
      = Multiset.card (s.filter (fun v => v ≠ 0)) := by
  classical
  obtain ⟨f₀, hf₀F, hf₀g⟩ := Finset.mem_image.mp hg
  obtain ⟨_, hf₀shape⟩ := Finset.mem_filter.mp hf₀F
  have hms : Multiset.map g (Finset.univ : Finset (Fin m)).val = s := by
    rw [← hf₀g]; exact hf₀shape
  rw [← hms, ← Multiset.countP_eq_card_filter, Multiset.countP_map]
  rfl

/-! ## Step 3: the shape-fiber size, unconditionally -/

/-- **Step (3), unconditional.** The shape-fiber decomposes over the
absolute-value map into one `signFiber` per attained abs-profile, each of size
`2^{#nonzero s}`; hence the fiber has size `(#abs-profiles) · 2^{#nonzero s}`. -/
theorem shapeFiber_card_eq_arrangements_mul (m n : ℕ) (s : Multiset ℤ) :
    (shapeFiber m n s).card
      = ((shapeFiber m n s).image absMap).card
          * 2 ^ Multiset.card (s.filter (fun v => v ≠ 0)) := by
  classical
  set M : ℕ := Multiset.card (s.filter (fun v => v ≠ 0)) with hM
  have key : ∀ g ∈ (shapeFiber m n s).image absMap,
      ((shapeFiber m n s).filter (fun f => absMap f = g)).card = 2 ^ M := by
    intro g hg
    rw [absFiber_eq_signFiber s g hg, signFiber_card]
    rw [hM]; congr 1; exact nonzero_card_eq s g hg
  rw [Finset.card_eq_sum_card_fiberwise
      (fun f hf => Finset.mem_image_of_mem absMap hf)]
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-! ## The keystone, modulo the arrangement-count residue -/

/-- **The Decomp keystone**, derived modulo the single arrangement-count residue
`harr`. `harr` is exactly #24518's `arrangement_card_div_form`, with the canonical
arrangement set identified here as the absolute-value image of the shape-fiber.

With `harr` discharged (the `Equiv.Perm (Fin m)` orbit–stabilizer count), this is
`fiber_card_eq_contribution` from `FourSquareDistributionOQ04Decomp.lean`, hence
the open question `r_{2k}(n) = Σ_shapes shapeContribution` for every `m, n`. -/
theorem fiber_card_eq_contribution {m n : ℕ} (s : Multiset ℤ)
    (harr : ((shapeFiber m n s).image absMap).card
              = m.factorial / (s.toFinset.prod (fun v => (s.count v).factorial))) :
    (shapeFiber m n s).card = shapeContribution m s := by
  rw [shapeFiber_card_eq_arrangements_mul, harr]
  rfl

#check @absFiber_eq_signFiber
#check @nonzero_card_eq
#check @shapeFiber_card_eq_arrangements_mul
#check @fiber_card_eq_contribution

end FourSquareDistributionOQ04Keystone
