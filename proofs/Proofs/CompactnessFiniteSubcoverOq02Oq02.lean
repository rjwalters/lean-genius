import Mathlib

/-
# Continuous Partition of Unity Subordinate to a Finite Open Cover

## What This Proves

Given a **finite** open cover `U : ι → Set X` of a metric space `X`
(`Fintype ι`, every `U i` open, `⋃ i, U i = univ`), we construct an explicit
continuous **partition of unity** subordinate to the cover:

* `psi U i : X → ℝ` is continuous for every `i`;
* `0 ≤ psi U i x` everywhere (nonnegativity);
* `psi U i x ≠ 0 → x ∈ U i` (subordination — the support of `psi U i` sits
  inside `U i`);
* `∑ i, psi U i x = 1` for every `x` (the partition sums to one).

The bundled statement is `exists_partition_of_unity`.

## The Construction

The bump for the cover member `U i` is the distance from `x` to the complement
of `U i`:

```
bump U i x = infDist x (U i)ᶜ        (guarded so `U i = univ ↦ 1`)
```

Because `U i` is open, `(U i)ᶜ` is closed, so `infDist x (U i)ᶜ > 0` exactly
when `x ∈ U i` (`Metric.infDist_pos_iff_notMem_closure`).  The single guard
handles the degenerate member `U i = univ`, whose complement is empty and whose
`infDist` would otherwise collapse to `0`; there we use the constant `1`.

Each `x` lies in some `U i`, so `bump U i x > 0`, hence the finite sum
`∑ j, bump U j x` is strictly positive everywhere.  Normalizing,
`psi U i x = bump U i x / ∑ j, bump U j x`, gives the partition of unity.

## Why Compactness Is Not Needed

The open question that motivated this entry asks for a partition of unity on a
*compact* metric space, built from a subordinate ε-net of bump functions.  The
construction here shows that **once the cover is finite, compactness plays no
role**: the distance-to-complement bumps are purely metric and need neither a
Lebesgue number nor an ε-net.  Compactness is only what reduces an *arbitrary*
open cover to a finite one; that reduction is supplied by
`exists_partition_of_unity_compact`, which extracts a finite subcover
(`IsCompact.elim_finite_subcover`) and then applies the finite construction.

This separates the two ingredients cleanly: compactness ⇒ finiteness of the
cover, and finiteness ⇒ partition of unity (no further topology required).
-/

open Set Metric
open scoped BigOperators Classical

namespace CompactnessFiniteSubcoverOq02Oq02

variable {X : Type*} [MetricSpace X]
variable {ι : Type*} [Fintype ι]

/-- Unnormalized bump for the cover member `U i`: the distance from `x` to the
complement of `U i`, guarded so the pathological member `U i = univ` (empty
complement) contributes the constant `1` rather than collapsing to `0`. -/
noncomputable def bump (U : ι → Set X) (i : ι) (x : X) : ℝ :=
  if (U i)ᶜ = ∅ then 1 else infDist x (U i)ᶜ

@[simp] lemma bump_nonneg (U : ι → Set X) (i : ι) (x : X) : 0 ≤ bump U i x := by
  unfold bump
  split
  · exact zero_le_one
  · exact infDist_nonneg

lemma bump_continuous (U : ι → Set X) (i : ι) : Continuous (bump U i) := by
  unfold bump
  by_cases h : (U i)ᶜ = ∅
  · simp only [if_pos h]; exact continuous_const
  · simp only [if_neg h]; exact continuous_infDist_pt (U i)ᶜ

/-- On the cover member `U i`, the bump is strictly positive. -/
lemma bump_pos_of_mem (U : ι → Set X) {i : ι} (hUi : IsOpen (U i)) {x : X}
    (hx : x ∈ U i) : 0 < bump U i x := by
  unfold bump
  by_cases h : (U i)ᶜ = ∅
  · simp only [if_pos h]; exact zero_lt_one
  · simp only [if_neg h]
    have hne : ((U i)ᶜ).Nonempty := nonempty_iff_ne_empty.mpr h
    have hclosed : IsClosed (U i)ᶜ := hUi.isClosed_compl
    have hxc : x ∉ closure (U i)ᶜ := by
      rw [hclosed.closure_eq]; simpa using hx
    exact (infDist_pos_iff_notMem_closure hne).mp hxc

/-- Subordination of the bump: it can only be nonzero inside `U i`. -/
lemma bump_subordinate (U : ι → Set X) {i : ι} {x : X} (hb : bump U i x ≠ 0) :
    x ∈ U i := by
  by_cases h : (U i)ᶜ = ∅
  · have : x ∉ (U i)ᶜ := by rw [h]; exact notMem_empty x
    simpa using this
  · by_contra hxni
    have hxc : x ∈ (U i)ᶜ := hxni
    apply hb
    unfold bump
    rw [if_neg h]
    exact infDist_zero_of_mem hxc

/-- The total weight `∑ j, bump U j x` is strictly positive at every point of a
finite open cover. -/
lemma sum_bump_pos (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) (x : X) : 0 < ∑ i, bump U i x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
    have hx : x ∈ ⋃ i, U i := by rw [hcov]; trivial
    simpa using hx
  refine Finset.sum_pos' (fun j _ => bump_nonneg U j x) ?_
  exact ⟨i, Finset.mem_univ i, bump_pos_of_mem U (hU i) hi⟩

/-- The normalized partition-of-unity function for the member `U i`. -/
noncomputable def psi (U : ι → Set X) (i : ι) (x : X) : ℝ :=
  bump U i x / ∑ j, bump U j x

lemma psi_continuous (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) (i : ι) : Continuous (psi U i) := by
  refine Continuous.div (bump_continuous U i)
    (continuous_finset_sum _ (fun j _ => bump_continuous U j)) ?_
  exact fun x => (sum_bump_pos U hU hcov x).ne'

lemma psi_nonneg (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) (i : ι) (x : X) : 0 ≤ psi U i x :=
  div_nonneg (bump_nonneg U i x) (sum_bump_pos U hU hcov x).le

lemma psi_subordinate (U : ι → Set X) {i : ι} {x : X} (h : psi U i x ≠ 0) :
    x ∈ U i := by
  refine bump_subordinate U (fun hb => h ?_)
  unfold psi
  rw [hb, zero_div]

lemma psi_sum_eq_one (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) (x : X) : ∑ i, psi U i x = 1 := by
  unfold psi
  rw [← Finset.sum_div]
  exact div_self (sum_bump_pos U hU hcov x).ne'

/-- **Continuous partition of unity subordinate to a finite open cover.**
Every finite open cover of a metric space carries an explicit continuous
partition of unity: nonnegative continuous functions, each supported inside its
cover member, summing pointwise to `1`. -/
theorem exists_partition_of_unity (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) :
    ∃ ψ : ι → X → ℝ,
      (∀ i, Continuous (ψ i)) ∧
      (∀ i x, 0 ≤ ψ i x) ∧
      (∀ i x, ψ i x ≠ 0 → x ∈ U i) ∧
      (∀ x, ∑ i, ψ i x = 1) :=
  ⟨psi U,
    fun i => psi_continuous U hU hcov i,
    fun i x => psi_nonneg U hU hcov i x,
    fun _ _ h => psi_subordinate U h,
    fun x => psi_sum_eq_one U hU hcov x⟩

/-- **Partition of unity on a compact metric space.** An *arbitrary* open cover
of a compact metric space admits a finite subset `s` of indices and a continuous
partition of unity subordinate to `{U i}_{i ∈ s}` summing to one — compactness
serves only to reduce the cover to a finite one, after which the metric
construction above applies. -/
theorem exists_partition_of_unity_compact [CompactSpace X]
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) :
    ∃ (s : Finset ι) (ψ : ι → X → ℝ),
      (∀ i, Continuous (ψ i)) ∧
      (∀ i x, 0 ≤ ψ i x) ∧
      (∀ i x, ψ i x ≠ 0 → x ∈ U i) ∧
      (∀ x, ∑ i ∈ s, ψ i x = 1) := by
  -- Extract a finite subcover.
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover U hU (by rw [hcov])
  -- Reindex by the finite subcover and build the partition of unity there.
  classical
  have hscov : (⋃ i : {i // i ∈ s}, U i.1) = univ := by
    rw [eq_univ_iff_forall]
    intro x
    have hx : x ∈ ⋃ i ∈ s, U i := hs (mem_univ x)
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ψ', hcont', hnonneg', hsub', hsum'⟩ :=
    exists_partition_of_unity (X := X) (ι := {i // i ∈ s})
      (fun i => U i.1) (fun i => hU i.1) hscov
  -- Push the subtype-indexed family back to a family on all of `ι`.
  refine ⟨s, fun i => if h : i ∈ s then ψ' ⟨i, h⟩ else fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i ∈ s
    · simp only [h, dif_pos]; exact hcont' ⟨i, h⟩
    · simp only [h]; exact continuous_const
  · intro i x
    by_cases h : i ∈ s
    · simp only [h, dif_pos]; exact hnonneg' ⟨i, h⟩ x
    · simp only [h]; exact le_refl 0
  · intro i x hx
    by_cases h : i ∈ s
    · simp only [h, dif_pos] at hx; exact hsub' ⟨i, h⟩ x hx
    · simp only [h] at hx; exact absurd rfl hx
  · intro x
    rw [← hsum' x]
    -- Beta-reduce the applied family `(fun i => …) i x` inside the sum.
    simp only []
    rw [← Finset.sum_coe_sort s
          (fun a => (if h : a ∈ s then ψ' ⟨a, h⟩ else fun _ : X => (0:ℝ)) x)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dif_pos i.2, Subtype.coe_eta]
