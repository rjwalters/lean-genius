import Mathlib
import Proofs.HallMarriageTheoremOQ01OQ01OQ01

/-
# Regular families satisfy Hall's condition: a `k`-regular bipartite family admits a full SDR

A finite indexed family `t : ι → Finset α` is **`k`-regular** when

* every index `i` has exactly `k` neighbours, `#(t i) = k` (left-regularity), and
* every element `a` occurring in the family is hit by exactly `k` indices,
  `#{i | a ∈ t i} = k` (right-regularity).

Read as a bipartite graph (indices on the left, elements on the right), this is the
usual notion of a `k`-regular bipartite graph.  The classical consequence is that
such a family automatically satisfies **Hall's marriage condition**
`#s ≤ #(s.biUnion t)` for every sub-family `s`, and hence — by Hall's theorem —
possesses a **full system of distinct representatives** (a perfect matching).

The proof is a one-line **double-counting** argument.  Fix `s ⊆ ι` and count the
incidence pairs `{(i, a) : i ∈ s, a ∈ t i}` two ways:

* from the left, each `i ∈ s` contributes exactly `k` pairs, giving `k · #s`;
* from the right, each `a ∈ s.biUnion t` contributes at most `k` pairs (its global
  degree is `k`, and we only count indices inside `s`), giving at most
  `k · #(s.biUnion t)`.

Therefore `k · #s ≤ k · #(s.biUnion t)`, and cancelling `k > 0` yields Hall's
inequality.  The incidence count is packaged by Mathlib's
`Finset.card_mul_le_card_mul`.

We then feed Hall's condition into two endpoints:

* `Finset.all_card_le_biUnion_card_iff_exists_injective` (Mathlib's Hall's theorem),
  producing a globally injective choice function `f : ι → α` with `f i ∈ t i`; and
* the parent entry's deficiency calculus
  (`HallMarriageTheoremOQ01OQ01OQ01`), which records that vanishing deficiency
  makes the maximum partial transversal size equal to `#ι`.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Finset Function

namespace HallRegular

variable {ι α : Type*} [Fintype ι] [DecidableEq α] {t : ι → Finset α}

/-- A finite family `t : ι → Finset α` is **`k`-regular** when every index has exactly
`k` neighbours (`#(t i) = k`) and every element occurring in the family is hit by
exactly `k` indices (`#{i | a ∈ t i} = k`).  This is the family-theoretic statement of a
`k`-regular bipartite graph. -/
def IsKRegular (t : ι → Finset α) (k : ℕ) : Prop :=
  (∀ i, (t i).card = k) ∧
    (∀ a ∈ (univ : Finset ι).biUnion t, ((univ : Finset ι).filter (fun i => a ∈ t i)).card = k)

/-- **Hall's condition from regularity.**  A `k`-regular family (`k ≥ 1`) satisfies the
marriage inequality `#s ≤ #(s.biUnion t)` for every sub-family `s`.  The proof
double-counts the incidence pairs `{(i, a) : i ∈ s, a ∈ t i}` via
`Finset.card_mul_le_card_mul`, then cancels the common factor `k`. -/
theorem hall_condition_of_regular {k : ℕ} (hk : 0 < k) (hreg : IsKRegular t k)
    (s : Finset ι) : s.card ≤ (s.biUnion t).card := by
  obtain ⟨hL, hR⟩ := hreg
  -- Bipartite incidence relation: index `i` meets element `a` iff `a ∈ t i`.
  let r : ι → α → Prop := fun i a => a ∈ t i
  -- Double counting yields `#s · k ≤ #(s.biUnion t) · k`.
  have hmul : s.card * k ≤ (s.biUnion t).card * k := by
    apply Finset.card_mul_le_card_mul r
    · -- LEFT: every `i ∈ s` meets exactly `k` elements of `s.biUnion t`.
      intro i hi
      have hba : (s.biUnion t).bipartiteAbove r i = t i := by
        ext a
        simp only [Finset.mem_bipartiteAbove]
        constructor
        · rintro ⟨_, ha⟩; exact ha
        · intro ha; exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, ha⟩, ha⟩
      have hcard : ((s.biUnion t).bipartiteAbove r i).card = k := by rw [hba, hL i]
      exact hcard.ge
    · -- RIGHT: every `a ∈ s.biUnion t` is met by at most `k` indices of `s`.
      intro a ha
      have hmem : a ∈ (univ : Finset ι).biUnion t := by
        rw [Finset.mem_biUnion] at ha ⊢
        obtain ⟨i, _, hai⟩ := ha
        exact ⟨i, Finset.mem_univ i, hai⟩
      have hsub : (s.bipartiteBelow r a).card ≤
          ((univ : Finset ι).filter (fun i => a ∈ t i)).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_bipartiteBelow] at hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.2⟩
      calc (s.bipartiteBelow r a).card
          ≤ ((univ : Finset ι).filter (fun i => a ∈ t i)).card := hsub
        _ = k := hR a hmem
  exact Nat.le_of_mul_le_mul_right hmul hk

/-- **Existence of a full system of distinct representatives.**  A `k`-regular family
(`k ≥ 1`) admits a globally injective choice function `f : ι → α` with `f i ∈ t i` for
every `i` — a perfect matching of the bipartite graph.  Immediate from
`hall_condition_of_regular` and Mathlib's Hall marriage theorem. -/
theorem exists_sdr_of_regular {k : ℕ} (hk : 0 < k) (hreg : IsKRegular t k) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp
    (fun s => hall_condition_of_regular hk hreg s)

section Deficiency

variable [DecidableEq ι] [Nonempty α]

omit [DecidableEq ι] [Nonempty α] in
/-- A `k`-regular family has **zero deficiency** in the sense of the parent entry: Hall's
inequality holds for every sub-family, so the deficiency `maxₛ (#s − #(s.biUnion t))`
collapses to `0`. -/
theorem deficiency_eq_zero_of_regular {k : ℕ} (hk : 0 < k) (hreg : IsKRegular t k) :
    HallDefect.deficiency t = 0 :=
  (HallDefect.deficiency_eq_zero_iff t).mpr
    (fun s => hall_condition_of_regular hk hreg s)

/-- **Maximum partial transversal is the whole index set.**  Combining vanishing
deficiency with the parent entry's closed-form optimum, the attainable
partial-transversal sizes of a `k`-regular family have greatest element `#ι`: the family
has a full transversal and no larger system is possible. -/
theorem isGreatest_transversal_of_regular {k : ℕ} (hk : 0 < k) (hreg : IsKRegular t k) :
    IsGreatest (HallDefect.transversalSizes t) (Fintype.card ι) :=
  HallDefect.maxTransversal_eq_card_of_deficiency_zero (deficiency_eq_zero_of_regular hk hreg)

end Deficiency

end HallRegular
