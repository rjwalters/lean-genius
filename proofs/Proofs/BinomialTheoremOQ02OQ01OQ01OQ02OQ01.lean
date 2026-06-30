import Mathlib

/-!
# Binomial OQ-02-01-01-02-01: the degree-one multinomial support is the index set

The parent entry (`binomial-theorem-oq-02-oq-01-oq-01-oq-02`, *Multinomial Entropy*)
sums probabilities over `s.piAntidiag n`, the finite set of functions `k : ι → ℕ`
supported on `s` with `∑_{i ∈ s} k i = n` -- the "compositions of `n` over `s`", i.e.
the support of the multinomial distribution of `n` trials over the categories `s`.

For `n = 1` this support degenerates completely: a single trial must land in exactly one
of the `|s|` categories, so each member of `s.piAntidiag 1` is an indicator `Pi.single i 1`
for a unique `i ∈ s`. Hence `s.piAntidiag 1` is in canonical bijection with `s` itself.
This file makes that precise.

## Main results

* `single_mem_piAntidiag_one` : `Pi.single i 1 ∈ s.piAntidiag 1` for every `i ∈ s`.
* `piAntidiag_one_eq_image`   : `s.piAntidiag 1 = s.image (fun i => Pi.single i 1)`
  -- the structural characterisation: degree-one tuples are exactly the indicators.
* `card_piAntidiag_one`       : `(s.piAntidiag 1).card = s.card`.
* `piAntidiagOneEquiv`        : the explicit bijection `↥s ≃ ↥(s.piAntidiag 1)`,
  `i ↦ Pi.single i 1`.

All results are `0`-axiom and depend only on Mathlib's `Finset.piAntidiag` API.
-/

open Finset

open scoped Classical

namespace BinomialTheoremOQ02OQ01OQ01OQ02OQ01

variable {ι : Type*} [DecidableEq ι] (s : Finset ι)

/-- The indicator `Pi.single i 1` is a degree-one tuple supported on `s` whenever `i ∈ s`. -/
theorem single_mem_piAntidiag_one {i : ι} (hi : i ∈ s) :
    Pi.single i (1 : ℕ) ∈ s.piAntidiag 1 := by
  rw [mem_piAntidiag]
  refine ⟨?_, ?_⟩
  · -- `∑_{j ∈ s} Pi.single i 1 j = 1`
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; exact Pi.single_eq_of_ne hj 1
    · intro hni; exact absurd hi hni
  · -- support of `Pi.single i 1` is `⊆ s`
    intro j hj
    by_cases hji : j = i
    · rw [hji]; exact hi
    · exact absurd (Pi.single_eq_of_ne hji 1) hj

/-- **Structural characterisation.** The degree-one tuples over `s` are exactly the
indicators `Pi.single i 1`, `i ∈ s`. -/
theorem piAntidiag_one_eq_image :
    s.piAntidiag 1 = s.image (fun i => Pi.single i (1 : ℕ)) := by
  ext f
  rw [mem_piAntidiag, mem_image]
  constructor
  · rintro ⟨hsum, hsupp⟩
    -- some index carries a nonzero value (else the sum would be `0 ≠ 1`)
    obtain ⟨i, hi_mem, hi_ne⟩ : ∃ i ∈ s, f i ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_eq_zero h] at hsum
      exact one_ne_zero hsum.symm
    -- that value is exactly `1`
    have hfi : f i = 1 := by
      have hle : f i ≤ s.sum f := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi_mem
      rw [hsum] at hle
      have hge : 1 ≤ f i := Nat.one_le_iff_ne_zero.mpr hi_ne
      omega
    -- and every other index of `s` carries `0`
    have hrest : ∀ j ∈ s, j ≠ i → f j = 0 := by
      intro j hj hji
      have hsub : ({i, j} : Finset ι) ⊆ s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hi_mem
        · rw [Finset.mem_singleton] at hx'; rw [hx']; exact hj
      have hpair : f i + f j ≤ s.sum f :=
        calc f i + f j = ∑ k ∈ ({i, j} : Finset ι), f k := (Finset.sum_pair (Ne.symm hji)).symm
          _ ≤ s.sum f := Finset.sum_le_sum_of_subset hsub
      rw [hsum] at hpair
      omega
    refine ⟨i, hi_mem, ?_⟩
    funext j
    rw [Pi.single_apply]
    by_cases hj : j = i
    · rw [if_pos hj, hj]; exact hfi.symm
    · rw [if_neg hj]
      by_cases hjs : j ∈ s
      · exact (hrest j hjs hj).symm
      · symm; by_contra hjz; exact hjs (hsupp j hjz)
  · rintro ⟨i, hi, rfl⟩
    exact mem_piAntidiag.mp (single_mem_piAntidiag_one s hi)

/-- The map `i ↦ Pi.single i 1` is injective: indicators at distinct indices differ. -/
theorem single_one_injective :
    Function.Injective (fun i : ι => Pi.single i (1 : ℕ)) := by
  intro a b hab
  by_contra hne
  have h1 := congr_fun hab a
  dsimp only at h1
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  exact one_ne_zero h1

/-- **Cardinality.** There are exactly `|s|` degree-one tuples over `s`. -/
theorem card_piAntidiag_one : (s.piAntidiag 1).card = s.card := by
  rw [piAntidiag_one_eq_image, Finset.card_image_of_injective _ single_one_injective]

/-- **The explicit bijection** `↥s ≃ ↥(s.piAntidiag 1)`, sending `i` to its indicator
`Pi.single i 1`. This realises the degree-one multinomial support as the index set. -/
noncomputable def piAntidiagOneEquiv : ↥s ≃ ↥(s.piAntidiag 1) := by
  refine Equiv.ofBijective
    (fun i => ⟨Pi.single (i : ι) (1 : ℕ), single_mem_piAntidiag_one s i.2⟩) ⟨?_, ?_⟩
  · -- injective
    rintro a b hab
    exact Subtype.ext (single_one_injective (Subtype.ext_iff.mp hab))
  · -- surjective
    rintro ⟨f, hf⟩
    rw [piAntidiag_one_eq_image, mem_image] at hf
    obtain ⟨i, hi, hif⟩ := hf
    exact ⟨⟨i, hi⟩, Subtype.ext hif⟩

end BinomialTheoremOQ02OQ01OQ01OQ02OQ01
