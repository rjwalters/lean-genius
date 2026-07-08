import Mathlib

/-!
# Erdős #1, child OQ-02-OQ-01: the elementary counting lower bound

Erdős's distinct-subset-sums problem (#1) asks how large the elements of a set
`A ⊆ ℕ` with pairwise-distinct subset sums must be. The parent
`erdos-1-oq-02` proves the sharp **second-moment** anticoncentration bound
`2^{|A|} ≤ 3·√(Σ aᵢ²) + 2`.

This entry records the *elementary* counterpart — the counting argument that
predates and motivates the analytic one, and needs no square roots:

> **Counting bound.** If `A` has distinct subset sums then `2^{|A|} ≤ Σ A + 1`.

The `2^{|A|}` subset sums are distinct and all lie in `{0, 1, …, Σ A}`, a set of
`Σ A + 1` values, so they cannot outnumber it. Combined with `Σ A ≤ |A| · max A`
this gives the classical **Erdős–Moser elementary bound**

> `2^{|A|} ≤ |A| · max A + 1`, i.e. `max A ≥ (2^{|A|} − 1)/|A|`,

the trivial lower bound that Erdős's conjecture (`max A ≥ c · 2^{|A|}`) seeks to
improve.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## References
* P. Erdős, Problems and results in additive number theory (distinct subset sums, #1).
* L. Moser, on the elementary counting bound `max A ≥ (2ⁿ − 1)/n`.
-/

namespace Erdos1OQ02OQ01

open Finset

/-- `A` has **distinct subset sums**: distinct subsets of `A` have distinct sums. -/
def HasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S.sum id = T.sum id → S = T

/-!
## Section 1: basic structure
-/

/-- The subset-sum map is injective on the powerset of a distinct-subset-sums set. -/
theorem subsetSum_injOn {A : Finset ℕ} (h : HasDistinctSubsetSums A) :
    Set.InjOn (fun S => S.sum id) (A.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hST
  exact h S T (mem_powerset.mp hS) (mem_powerset.mp hT) hST

/-- Distinct subset sums forces `0 ∉ A` (else `{0}` and `∅` share the sum `0`). -/
theorem zero_not_mem {A : Finset ℕ} (h : HasDistinctSubsetSums A) : 0 ∉ A := by
  intro h0
  have hsum : ({0} : Finset ℕ).sum id = (∅ : Finset ℕ).sum id := by simp
  have heq := h {0} ∅ (singleton_subset_iff.mpr h0) (empty_subset _) hsum
  exact absurd heq (singleton_ne_empty 0)

/-- Distinct subset sums is hereditary: any subset of a distinct-subset-sums set
    again has distinct subset sums. -/
theorem HasDistinctSubsetSums.subset {A B : Finset ℕ} (hBA : B ⊆ A)
    (h : HasDistinctSubsetSums A) : HasDistinctSubsetSums B :=
  fun S T hS hT hST => h S T (hS.trans hBA) (hT.trans hBA) hST

/-!
## Section 2: the counting bound `2^{|A|} ≤ Σ A + 1`
-/

/-- **Elementary counting bound.** The `2^{|A|}` distinct subset sums all lie in
    `{0, …, Σ A}`, so `2^{|A|} ≤ Σ A + 1`. -/
theorem two_pow_card_le_sum_succ {A : Finset ℕ} (h : HasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.sum id + 1 := by
  have himg : A.powerset.image (fun S => S.sum id) ⊆ range (A.sum id + 1) := by
    intro s hs
    simp only [mem_image, mem_powerset] at hs
    obtain ⟨T, hT, rfl⟩ := hs
    rw [mem_range]
    have : T.sum id ≤ A.sum id := sum_le_sum_of_subset hT
    omega
  have hcard : (A.powerset.image (fun S => S.sum id)).card = 2 ^ A.card := by
    rw [card_image_of_injOn (subsetSum_injOn h), card_powerset]
  calc 2 ^ A.card = (A.powerset.image (fun S => S.sum id)).card := hcard.symm
    _ ≤ (range (A.sum id + 1)).card := card_le_card himg
    _ = A.sum id + 1 := card_range _

/-- Consequence: `|A| ≤ Σ A` for a distinct-subset-sums set (using `|A| < 2^{|A|}`). -/
theorem card_le_sum {A : Finset ℕ} (h : HasDistinctSubsetSums A) :
    A.card ≤ A.sum id := by
  have h1 := two_pow_card_le_sum_succ h
  have h2 : A.card < 2 ^ A.card := Nat.lt_two_pow_self
  omega

/-!
## Section 3: the Erdős–Moser max bound
-/

/-- **Erdős–Moser elementary bound.** Since `Σ A ≤ |A| · max A`, the counting
    bound gives `2^{|A|} ≤ |A| · max A + 1`; equivalently `max A ≥ (2^{|A|} − 1)/|A|`,
    the trivial lower bound Erdős's conjecture aims to sharpen to `c · 2^{|A|}`. -/
theorem two_pow_card_le_card_mul_max {A : Finset ℕ} (h : HasDistinctSubsetSums A)
    (hne : A.Nonempty) :
    2 ^ A.card ≤ A.card * A.max' hne + 1 := by
  have h1 := two_pow_card_le_sum_succ h
  have h2 : A.sum id ≤ A.card * A.max' hne := by
    have hbound := sum_le_card_nsmul A id (A.max' hne) (fun x hx => le_max' A x hx)
    simpa [smul_eq_mul] using hbound
  omega

/-- The powers-of-two set shows the counting bound is essentially tight: for
    `A = {1, 2, …, 2^{n-1}}` one has `Σ A = 2^n − 1`, matching
    `2^{|A|} = 2^n = Σ A + 1`. (Stated here as the arithmetic identity
    `Σ_{i<n} 2^i + 1 = 2^n` that witnesses equality in the counting bound.) -/
theorem geomSum_two_succ (n : ℕ) : (∑ i ∈ range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    omega

/-!
## Section 4: the powers-of-two extremal set

Section 2 gives the counting *lower* bound `2^{|A|} ≤ Σ A + 1`; Section 3 turns it
into `max A ≥ (2^{|A|} − 1)/|A|`. This section supplies the matching
*construction*: the geometric set `{2⁰, 2¹, …, 2^{n-1}}` is a genuine
distinct-subset-sums set of cardinality `n`, it attains **equality** in the
counting bound (`Σ A = 2ⁿ − 1`), and its largest element is only `2^{n-1} = 2ⁿ/2`.

Writing `M(n)` for the Erdős extremal maximum

> `M(n) := min { max A : |A| = n, A has distinct subset sums }`,

Section 3 and this construction pin it between the two elementary walls

> `(2ⁿ − 1)/n ≤ M(n) ≤ 2^{n-1}`.

In particular the conjectural constant `c` in Erdős's `max A ≥ c·2^{|A|}` cannot
exceed `1/2`: the whole difficulty of Erdős #1 lies in closing the `√n`-and-more
gap between the counting lower bound and this doubling construction (the analytic
second-moment bound of the parent entry `erdos-1-oq-02` narrows, but does not
close, that gap). Distinctness reuses Mathlib's `Finset.geomSum_injective`
(injectivity of `I ↦ ∑_{i∈I} 2^i`, the uniqueness of binary expansions).
-/

/-- The doubling map `i ↦ 2ⁱ` is injective. -/
theorem twoPow_injective : Function.Injective (fun i : ℕ => 2 ^ i) :=
  Nat.pow_right_injective (le_refl 2)

/-- The geometric set `{2⁰, 2¹, …, 2^{n-1}}`. -/
def geomSet (n : ℕ) : Finset ℕ := (range n).image (fun i => 2 ^ i)

/-- Membership in the geometric set: `x` is a power `2ⁱ` with `i < n`. -/
theorem mem_geomSet {n x : ℕ} : x ∈ geomSet n ↔ ∃ i < n, 2 ^ i = x := by
  simp only [geomSet, mem_image, mem_range]

/-- The geometric set has exactly `n` elements. -/
theorem card_geomSet (n : ℕ) : (geomSet n).card = n := by
  rw [geomSet, card_image_of_injective _ twoPow_injective, card_range]

/-- A subset sum over an image of powers of two collapses to a geometric sum of
    the chosen indices. -/
theorem sum_image_twoPow (I : Finset ℕ) :
    (I.image (fun i => 2 ^ i)).sum id = ∑ i ∈ I, 2 ^ i := by
  simp only [sum_image twoPow_injective.injOn, id_eq]

/-- **The geometric set has distinct subset sums.** Any subset of `{2⁰,…,2^{n-1}}`
    is the image of an index set `I ⊆ range n`, and `I ↦ ∑_{i∈I} 2ⁱ` is injective
    (`Finset.geomSum_injective`), so equal subset sums force equal subsets. -/
theorem geomSet_hasDistinctSubsetSums (n : ℕ) :
    HasDistinctSubsetSums (geomSet n) := by
  intro S T hS hT hST
  rw [geomSet] at hS hT
  obtain ⟨I, _, rfl⟩ := subset_image_iff.1 hS
  obtain ⟨J, _, rfl⟩ := subset_image_iff.1 hT
  simp only [sum_image_twoPow] at hST
  rw [geomSum_injective (le_refl 2) hST]

/-- The geometric set attains **equality** in the counting bound: `Σ A = 2ⁿ − 1`. -/
theorem sum_geomSet (n : ℕ) : (geomSet n).sum id = 2 ^ n - 1 := by
  rw [geomSet, sum_image_twoPow]
  have := geomSum_two_succ n
  omega

/-- The largest element of the geometric set is `2^{n-1}` (for `n ≥ 1`). -/
theorem max'_geomSet {n : ℕ} (hn : 1 ≤ n) (hne : (geomSet n).Nonempty) :
    (geomSet n).max' hne = 2 ^ (n - 1) := by
  apply le_antisymm
  · apply max'_le
    intro y hy
    rw [mem_geomSet] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · apply le_max'
    rw [mem_geomSet]
    exact ⟨n - 1, by omega, rfl⟩

/-- **Two-sided wall on the Erdős extremal max.** For every `n ≥ 1` there is a
    distinct-subset-sums set `A` of cardinality `n` whose largest element is
    exactly `2^{n-1}`. Combined with `two_pow_card_le_card_mul_max` (giving
    `max A ≥ (2ⁿ − 1)/|A|`) this pins the extremal maximum `M(n)` into
    `(2ⁿ − 1)/n ≤ M(n) ≤ 2^{n-1}`, so the conjectural constant `c` in
    `max A ≥ c·2^{|A|}` satisfies `c ≤ 1/2`. -/
theorem exists_extremal_geomSet (n : ℕ) (hn : 1 ≤ n) :
    ∃ A : Finset ℕ, A.card = n ∧ HasDistinctSubsetSums A ∧
      ∃ hne : A.Nonempty, A.max' hne = 2 ^ (n - 1) := by
  have hne : (geomSet n).Nonempty := by
    rw [← card_pos, card_geomSet]; omega
  exact ⟨geomSet n, card_geomSet n, geomSet_hasDistinctSubsetSums n,
    hne, max'_geomSet hn hne⟩

end Erdos1OQ02OQ01
