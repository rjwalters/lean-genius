import Mathlib
import Proofs.FourSquareDistributionOQ04ArrangeProof

/-
# Four-Square Distribution — OQ-04: the arrangement-count residue in `Nat.multinomial` form

## Context

`FourSquareDistributionOQ04Decomp.lean` reduces the whole open question to one
orbit-size lemma `fiber_card_eq_contribution`: each `shape`-fiber of the genuine
representation set has size

  (★)   `m! / ∏_v (count_v)! · 2^{#nonzero}`.

`FourSquareDistributionOQ04Sign.lean` proves the **sign-count half** `2^{#nonzero}`
in full. The blueprint there splits `(★)` over the coordinatewise absolute-value
map and isolates the remaining residue as a single combinatorial count — the
**multiset-arrangement count**

  `arrangement_card`:  `#{ g : Fin m → ℤ | multiset(g) = s } = m! / ∏_v (count_v s)!`.

A build-free Mathlib search (researcher-2, 2026-06-15) found that `Nat.multinomial`
already *is* `m! / ∏count!` and carries the factored identity `Nat.multinomial_spec`,
but that there is **no ready cardinality lemma** for multiset arrangements, and
recommended re-expressing the residue via `Nat.multinomial` so that
`multinomial_spec` applies directly.

This file executes that recommendation. It:

* **proves** the reformulation bridge `factorial_div_eq_multinomial`:
  `m! / ∏_v (count_v s)! = Nat.multinomial s.toFinset s.count`
  (so the `Nat.div` in `shapeContribution` *is* the multinomial coefficient);
* **proves** `prod_count_factorial_dvd`: `∏_v (count_v s)! ∣ m!`, i.e. that
  `Nat.div` is exact (no truncation) — a genuine correctness fact about the
  formula `(★)` used by the parent / sibling files;
* gives the canonical `Finset` `arrangements s` of multiset arrangements with a
  clean membership characterization `mem_arrangements_iff`;
* states `arrangement_card` (the sole remaining residue) in canonical
  `Nat.multinomial` form, and derives `arrangement_card_div_form` (the `m!/∏count!`
  shape used by `shapeContribution`) from it via the proved bridge.

Everything except `arrangement_card` is unconditional. The residue is now in the
exact form `multinomial_spec` consumes, which is the recommended setup for the
orbit–stabilizer proof (`Equiv.Perm (Fin m)` precomposition; stabilizer of an
arrangement `g` is `≅ ∏_v Equiv.Perm (g⁻¹ {v})` of order `∏_v (count_v)!`, so
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` gives
`|arrangements| · ∏count! = m!`, hence `= multinomial` by `multinomial_spec`).

Build status: PENDING (authored under a Docker + Aristotle backend outage, both
re-tested live this session: `docker info` daemon down, Aristotle `prove` → 404).
UNREGISTERED in `Proofs.lean`. Uses only standard `Nat.multinomial` /
`Fintype.piFinset` / `Multiset` API.

The exact statement of `arrangement_card` is independently certified by
`research/problems/four-square-distribution-oq-04/verify_orbit_formula.py`
(`check_arrangement`): the brute multiset-arrangement count equals
`m! / ∏count!` for all multisets drawn from `{0,1,2}` of size `m ≤ 6`.
-/

namespace FourSquareDistributionOQ04Arrange

open Finset

/-! ## Part 1: the reformulation bridge `m! / ∏count! = Nat.multinomial`

`Nat.multinomial s f = (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!` by definition. Applied to
`s.toFinset` and `f = s.count`, the sum of the multiplicities is `Multiset.card s`,
so the multinomial coefficient is exactly the symmetry numerator `m! / ∏count!`. -/

/-- The symmetry numerator of the orbit formula is the multinomial coefficient:
`m! / ∏_v (count_v s)! = Nat.multinomial s.toFinset s.count`. -/
theorem factorial_div_eq_multinomial {m : ℕ} (s : Multiset ℤ)
    (hm : Multiset.card s = m) :
    m.factorial / (∏ v ∈ s.toFinset, (s.count v).factorial)
      = Nat.multinomial s.toFinset (fun v => s.count v) := by
  have hdef : Nat.multinomial s.toFinset (fun v => s.count v)
      = (∑ v ∈ s.toFinset, s.count v).factorial
          / ∏ v ∈ s.toFinset, (s.count v).factorial := rfl
  rw [hdef, Multiset.toFinset_sum_count_eq, hm]

/-- The product of per-value factorials divides `m!`, so the `Nat.div` in the
orbit formula `(★)` is exact (no truncation). This is the factored identity
`Nat.multinomial_spec` read as a divisibility. -/
theorem prod_count_factorial_dvd {m : ℕ} (s : Multiset ℤ)
    (hm : Multiset.card s = m) :
    (∏ v ∈ s.toFinset, (s.count v).factorial) ∣ m.factorial := by
  have hspec : (∏ v ∈ s.toFinset, (s.count v).factorial)
        * Nat.multinomial s.toFinset (fun v => s.count v)
      = (∑ v ∈ s.toFinset, s.count v).factorial :=
    Nat.multinomial_spec _ _
  rw [Multiset.toFinset_sum_count_eq, hm] at hspec
  exact ⟨_, hspec.symm⟩

/-! ## Part 2: the multiset-arrangement set and the residual count -/

/-- The arrangements of a multiset `s` as functions `Fin m → ℤ`: all `g` whose
multiset of values is exactly `s`. Realized as a `Finset` on the finite box
`(s.toFinset)^m`, which is lossless since every value of an arrangement of `s`
lies in `s`. -/
def arrangements {m : ℕ} (s : Multiset ℤ) : Finset (Fin m → ℤ) :=
  (Fintype.piFinset (fun _ : Fin m => s.toFinset)).filter
    (fun g => Multiset.map g (Finset.univ : Finset (Fin m)).val = s)

/-- Membership in `arrangements s` is exactly the multiset-image condition; the
box `(s.toFinset)^m` never clips an arrangement. -/
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

/-- **The single remaining residue (OPEN / proof target).** The number of
arrangements of a size-`m` multiset `s` is the multinomial coefficient
`Nat.multinomial s.toFinset s.count = m! / ∏_v (count_v)!`.

This is the sign-free combinatorial heart of the orbit-size formula. It is
**discharged** (no `sorry`) in `FourSquareDistributionOQ04ArrangeProof.lean` by an
elementary fiberwise count on the precomposition map `σ ↦ g₀ ∘ σ :
Equiv.Perm (Fin m) → arrangements s`: each fiber is a stabilizer coset of size
`∏_v (count_v s)!`, so `m! = |arrangements s| · ∏count!`, and `Nat.multinomial_spec`
cancels the product. This avoids `MulAction.orbit` and its `Fintype`-instance
synthesis (the documented blocker for the orbit–stabilizer route). The proof
file uses the identical `arrangements` definition, so the discharge transfers by
definitional unfolding. -/
theorem arrangement_card {m : ℕ} (s : Multiset ℤ) (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card
      = Nat.multinomial s.toFinset (fun v => s.count v) :=
  FourSquareDistributionOQ04ArrangeProof.arrangement_card s hm

/-- The arrangement count in the `m! / ∏count!` shape used by `shapeContribution`,
obtained from `arrangement_card` through the proved reformulation bridge. -/
theorem arrangement_card_div_form {m : ℕ} (s : Multiset ℤ)
    (hm : Multiset.card s = m) :
    (arrangements (m := m) s).card
      = m.factorial / (∏ v ∈ s.toFinset, (s.count v).factorial) := by
  rw [arrangement_card s hm, ← factorial_div_eq_multinomial s hm]

#check @factorial_div_eq_multinomial
#check @prod_count_factorial_dvd
#check @mem_arrangements_iff
#check @arrangement_card_div_form

end FourSquareDistributionOQ04Arrange
