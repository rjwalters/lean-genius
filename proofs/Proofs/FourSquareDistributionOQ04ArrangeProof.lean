import Mathlib

/-
# Four-Square Distribution — OQ-04: discharging the `arrangement_card` residue

Companion to `FourSquareDistributionOQ04Arrange.lean` (merged via #24518), which
reduced the entire open question to a single combinatorial residue, the
multiset-arrangement count

  `arrangement_card`:  `#{ g : Fin m → ℤ | multiset(g) = s } = Nat.multinomial s.toFinset s.count`.

## Key discovery (researcher-5, 2026-06-16)

The parent file's docstring states there is "**no ready cardinality lemma**" for
the stabilizer order `∏_v (count_v)!` and that this product "is the genuine
residue" to be computed by hand. **That is no longer true.** Mathlib's
`DomMulAct.stabilizer_card'` (`Mathlib/GroupTheory/Perm/DomMulAct.lean`) computes
exactly this product for the precomposition action of `Equiv.Perm` on functions:

  `DomMulAct.stabilizer_card' (f : α → ι) [Fintype α] [DecidableEq α] [DecidableEq ι] :`
  `  Fintype.card {g : Perm α // f ∘ g = f}`
  `    = ∏ i ∈ Finset.univ.image f, (Fintype.card {a // f a = i})!`

(It needs only `DecidableEq ι`, NOT `Fintype ι`, so it applies with `ι = ℤ`.)

This collapses the orbit–stabilizer argument to wiring:
1. Set up the `DomMulAct (Perm (Fin m))` action on `Fin m → ℤ`.
2. `MulAction.card_orbit_mul_card_stabilizer_eq_card_group g`:
   `card (orbit) · card (stabilizer) = card (Perm (Fin m)) = m!` (`Fintype.card_perm`).
3. `stabilizer_card'` rewrites `card (stabilizer)` as `∏_{i ∈ image g} (card (fiber i))!`.
   For `g ∈ arrangements s` we have `image g = s.toFinset` and `card (fiber i) = s.count i`,
   so the product is `∏_{v ∈ s.toFinset} (s.count v)!`.
4. The orbit of `g` is (in bijection with) `arrangements s`: precomposition by a
   permutation preserves the multiset image, and conversely any function with the
   same multiset image is a precomposition of `g`.
5. Hence `card (arrangements s) · ∏count! = m!`, i.e.
   `card (arrangements s) = m! / ∏count! = Nat.multinomial s.toFinset s.count`
   (via the parent's `factorial_div_eq_multinomial` + `Nat.multinomial_spec`).

## Status

Build-gated orphan (NOT registered in `Proofs.lean`; CI-safe). Authored under a
dual backend outage (Aristotle `prove_file` → 404; this worktree's `proofs/.lake`
is a corrupt self-symlink so docker-build is blocked here). The structural lemmas
proven below typecheck against standard Mathlib API; the genuinely combinatorial
glue (orbit ↔ arrangements, fiber-size = count) is isolated as annotated `sorry`s
for an Aristotle `prove_file` / docker-build discharge once a backend recovers.

`arrangements` is restated here verbatim from the parent so the file is
self-contained (and `prove_file`-portable). On discharge, fold into the parent's
`arrangement_card` or import this companion.
-/

namespace FourSquareDistributionOQ04ArrangeProof

open Finset

/-- The canonical `Finset` of multiset-arrangements (verbatim from the parent file). -/
def arrangements {m : ℕ} (s : Multiset ℤ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => s.toFinset)).filter
    (fun g => Multiset.map g (Finset.univ : Finset (Fin m)).val = s)

theorem mem_arrangements_iff {m : ℕ} (s : Multiset ℤ) (g : Fin m → ℤ) :
    g ∈ arrangements s ↔ Multiset.map g (Finset.univ : Finset (Fin m)).val = s := by
  classical
  simp only [arrangements, Finset.mem_filter, Fintype.mem_piFinset, Multiset.mem_toFinset]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨fun i => ?_, h⟩
    rw [← h]
    exact Multiset.mem_map_of_mem g (Finset.mem_val.mpr (Finset.mem_univ i))

/-- The image of an arrangement is exactly `s.toFinset`: the set of values of `g`
    equals the support of the multiset `s` it realizes. -/
theorem image_eq_toFinset_of_mem {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    (Finset.univ : Finset (Fin m)).image g = s.toFinset := by
  sorry

/-- The `i`-fiber of an arrangement has size `s.count i`: the number of indices
    mapping to a value equals that value's multiplicity in the realized multiset. -/
theorem card_fiber_eq_count {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) (i : ℤ) :
    Fintype.card {a : Fin m // g a = i} = s.count i := by
  sorry

/-- **Stabilizer order = ∏ count!** for an arrangement `g`, packaged from
    `DomMulAct.stabilizer_card'` together with `image_eq_toFinset_of_mem` and
    `card_fiber_eq_count`. -/
theorem stabilizer_card_eq_prod_count {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    Fintype.card {σ : Equiv.Perm (Fin m) // g ∘ σ = g}
      = ∏ v ∈ s.toFinset, (s.count v)! := by
  sorry

/-- **Orbit ↔ arrangements.** The orbit of an arrangement `g` under the
    precomposition action of `Equiv.Perm (Fin m)` is, in cardinality, exactly
    `arrangements s`: precomposition preserves the multiset image, and every
    function realizing `s` is a precomposition of `g`. -/
theorem card_orbit_eq_card_arrangements {m : ℕ} (s : Multiset ℤ) {g : Fin m → ℤ}
    (hg : g ∈ arrangements s) :
    Fintype.card {h : Fin m → ℤ // ∃ σ : Equiv.Perm (Fin m), h = g ∘ σ}
      = (arrangements (m := m) s).card := by
  sorry

/-- **Residue discharged: `card (arrangements s) · ∏count! = m!`.**
    Orbit–stabilizer (`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`)
    plus `Fintype.card_perm` (`card (Perm (Fin m)) = m!`) and the two bridges
    above. This is the exact-division correctness fact that makes the parent's
    `Nat.div` non-truncating. -/
theorem arrangements_card_mul_prod_count {m : ℕ} (s : Multiset ℤ)
    (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card * ∏ v ∈ s.toFinset, (s.count v)! = m ! := by
  sorry

/-- **The residue, in `Nat.multinomial` form.** Identical statement to the parent
    file's `arrangement_card`; obtained by dividing
    `arrangements_card_mul_prod_count` by `∏count!` and applying
    `Nat.multinomial_spec` (`multinomial · ∏count! = (∑count)!` with `∑count = m`). -/
theorem arrangement_card {m : ℕ} (s : Multiset ℤ) (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card
      = Nat.multinomial s.toFinset (fun v => s.count v) := by
  sorry

end FourSquareDistributionOQ04ArrangeProof
