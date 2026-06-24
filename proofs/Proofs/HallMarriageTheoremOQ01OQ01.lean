import Mathlib
import Proofs.HallMarriageTheoremOQ01

/-
# Hall's marriage theorem, defect form: matching all but the deficiency

The companion entry `HallMarriageTheoremOQ01` proves Hall's marriage theorem
together with the *deficiency obstruction*: a sub-family `s` that is deficient
(`#s > #(s.biUnion t)`) blocks a full system of distinct representatives.  This
file supplies the **quantitative converse** — the classical *defect* (or *Ore*)
form of Hall's theorem:

> Let `t : ι → Finset α` be a finite family.  Then a matching saturating **all
> but `d`** of the indices exists **iff** the family is *`d`-deficient at worst*,
> i.e. every sub-family `s` satisfies `#s ≤ #(s.biUnion t) + d`.

Concretely, "a matching saturating all but `d` indices" means: a set `J ⊆ ι`
with `#J ≥ #ι − d` together with an injective (on `J`) choice function
`f : ι → α` with `f i ∈ t i` for every `i ∈ J`.

## Why this is the right statement

Setting `d = 0` recovers the ordinary marriage theorem (a full SDR).  The
parameter `d` measures, sharply, how far the family is from satisfying Hall's
condition: the largest *deficiency* `δ = maxₛ (#s − #(s.biUnion t))` is exactly
the number of indices that *must* be left unmatched, and the theorem says a
matching of size `#ι − δ` is always attainable.

## The proof

The substantive direction is the classical **dummy-target augmentation**.  Form
the augmented family `aug t d : ι → Finset (α ⊕ Fin d)` by adjoining, to every
target set, a shared block of `d` brand-new "dummy" targets (a copy of `Fin d`).
For any nonempty `s`,

  `#(s.biUnion (aug t d)) = #(s.biUnion t) + d`,

because the `α`-part and the dummy block are disjoint.  Hence the deficiency
hypothesis `#s ≤ #(s.biUnion t) + d` turns into Hall's condition for `aug t d`,
and **Mathlib's marriage theorem** (`all_card_le_biUnion_card_iff_exists_injective`)
yields an injective `f' : ι → α ⊕ Fin d` with `f' i ∈ aug t d i`.  The indices
landing in the genuine `α` part form the matched set `J`; the rest inject into
the `d` dummies, so at most `d` indices are unmatched, giving `#J ≥ #ι − d`.

The reverse direction is a direct count: a matching on `J` injects `s ∩ J` into
`s.biUnion t`, and `s \ J` has at most `d` elements.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no
`native_decide`.
-/

open Finset Function

namespace HallDefect

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α] [Nonempty α]

/-- The **augmented family**: to every target set `t i` we adjoin a shared block
of `d` fresh "dummy" targets, realised as a copy of `Fin d` sitting in the right
summand of `α ⊕ Fin d`. -/
def aug (t : ι → Finset α) (d : ℕ) (i : ι) : Finset (α ⊕ Fin d) :=
  (t i).map Embedding.inl ∪ (univ : Finset (Fin d)).map Embedding.inr

omit [Fintype ι] [DecidableEq ι] [Nonempty α] in
/-- **Augmentation satisfies Hall.** If the family is at worst `d`-deficient,
then the augmented family satisfies Hall's condition outright: every sub-family
`s` has `#s ≤ #(s.biUnion (aug t d))`. -/
theorem aug_hall {t : ι → Finset α} {d : ℕ}
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card + d) :
    ∀ s : Finset ι, s.card ≤ (s.biUnion (aug t d)).card := by
  intro s
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · -- the augmented union splits as an `α`-part plus the full dummy block
    have hsplit : s.biUnion (aug t d)
        = (s.biUnion t).map Embedding.inl
            ∪ (univ : Finset (Fin d)).map Embedding.inr := by
      ext x
      simp only [aug, mem_biUnion, mem_union, mem_map]
      constructor
      · rintro ⟨i, hi, h'⟩
        rcases h' with ⟨a, ha, rfl⟩ | ⟨k, hk, rfl⟩
        · exact Or.inl ⟨a, ⟨i, hi, ha⟩, rfl⟩
        · exact Or.inr ⟨k, hk, rfl⟩
      · rintro (⟨a, ⟨i, hi, ha⟩, rfl⟩ | ⟨k, hk, rfl⟩)
        · exact ⟨i, hi, Or.inl ⟨a, ha, rfl⟩⟩
        · obtain ⟨i, hi⟩ := hs
          exact ⟨i, hi, Or.inr ⟨k, hk, rfl⟩⟩
    have hdisj : Disjoint ((s.biUnion t).map Embedding.inl)
        ((univ : Finset (Fin d)).map Embedding.inr) := by
      rw [Finset.disjoint_left]
      rintro x hx hx'
      simp only [mem_map] at hx hx'
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨k, -, hk⟩ := hx'
      exact Sum.inr_ne_inl hk
    have hcard : (s.biUnion (aug t d)).card = (s.biUnion t).card + d := by
      rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_map,
        Finset.card_map, Finset.card_univ, Fintype.card_fin]
    rw [hcard]; exact h s

/-- **Defect Hall, hard direction.** If the family is at worst `d`-deficient,
there is a matching saturating all but at most `d` indices: a set `J` of size
`≥ #ι − d` and a function `f` injective on `J` with `f i ∈ t i` for `i ∈ J`. -/
theorem exists_matching_of_deficiency_le {t : ι → Finset α} {d : ℕ}
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card + d) :
    ∃ (J : Finset ι) (f : ι → α),
      Fintype.card ι - d ≤ J.card ∧ Set.InjOn f ↑J ∧ ∀ i ∈ J, f i ∈ t i := by
  classical
  obtain ⟨f', hf'inj, hf'mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (aug t d)).mp (aug_hall h)
  set J : Finset ι := univ.filter (fun i => (f' i).isLeft) with hJ
  -- every matched index carries a genuine `α`-witness in `t i`
  have hLeft : ∀ i ∈ J, ∃ a, a ∈ t i ∧ f' i = Sum.inl a := by
    intro i hi
    have hiL : (f' i).isLeft = true := by
      rw [hJ, mem_filter] at hi; simpa using hi.2
    have hm := hf'mem i
    simp only [aug, mem_union, mem_map] at hm
    rcases hm with ⟨a, ha, hae⟩ | ⟨k, -, hke⟩
    · exact ⟨a, ha, hae.symm⟩
    · rw [← hke] at hiL; simp at hiL
  -- the witness function
  let f : ι → α := fun i => if hi : i ∈ J then (hLeft i hi).choose else Classical.arbitrary α
  have hf_spec : ∀ i (hi : i ∈ J), f' i = Sum.inl (f i) := by
    intro i hi
    have := (hLeft i hi).choose_spec.2
    simpa only [f, dif_pos hi] using this
  refine ⟨J, f, ?_, ?_, ?_⟩
  · -- card bound: the unmatched indices inject into the `d` dummies
    have hmap : ∀ i ∈ Jᶜ, ∃ k, f' i = Sum.inr k := by
      intro i hi
      rw [hJ, mem_compl, mem_filter] at hi
      have hnotL : (f' i).isLeft ≠ true := by
        intro hcon; exact hi ⟨mem_univ i, hcon⟩
      cases hfi : f' i with
      | inl a => rw [hfi] at hnotL; simp at hnotL
      | inr k => exact ⟨k, rfl⟩
    have hcompl : Jᶜ.card ≤ d := by
      have hle : Jᶜ.card ≤ ((univ : Finset (Fin d)).map (Embedding.inr (α := α))).card := by
        refine Finset.card_le_card_of_injOn f' ?_ (hf'inj.injOn)
        intro i hi
        obtain ⟨k, hk⟩ := hmap i hi
        rw [hk]
        simp only [Finset.mem_coe, Finset.mem_map]
        exact ⟨k, mem_univ k, rfl⟩
      rwa [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hle
    have htot := Finset.card_add_card_compl J
    omega
  · -- injective on `J`
    intro i hi j hj hij
    rw [mem_coe] at hi hj
    apply hf'inj
    rw [hf_spec i hi, hf_spec j hj, hij]
  · -- membership
    intro i hi
    have h1 := (hLeft i hi).choose_spec.1
    simpa only [f, dif_pos hi] using h1

omit [Nonempty α] in
/-- **Defect Hall, easy direction.** A matching saturating all but `d` indices
forces the family to be at worst `d`-deficient. -/
theorem deficiency_le_of_matching {t : ι → Finset α} {d : ℕ}
    {J : Finset ι} {f : ι → α}
    (hcard : Fintype.card ι - d ≤ J.card)
    (hinj : Set.InjOn f ↑J) (hmem : ∀ i ∈ J, f i ∈ t i) :
    ∀ s : Finset ι, s.card ≤ (s.biUnion t).card + d := by
  intro s
  have hsub : (s ∩ J).card ≤ (s.biUnion t).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, mem_inter] at hi
      simp only [Finset.mem_coe]
      exact mem_biUnion.mpr ⟨i, hi.1, hmem i hi.2⟩
    · exact hinj.mono (Finset.coe_subset.mpr Finset.inter_subset_right)
  have hJc : Jᶜ.card ≤ d := by
    have := Finset.card_add_card_compl J
    omega
  have hsplit : s.card ≤ (s ∩ J).card + Jᶜ.card := by
    have hsubset : s ⊆ (s ∩ J) ∪ Jᶜ := by
      intro x hx
      by_cases hxJ : x ∈ J
      · exact mem_union_left _ (mem_inter.mpr ⟨hx, hxJ⟩)
      · exact mem_union_right _ (mem_compl.mpr hxJ)
    calc s.card ≤ ((s ∩ J) ∪ Jᶜ).card := Finset.card_le_card hsubset
      _ ≤ (s ∩ J).card + Jᶜ.card := Finset.card_union_le _ _
  omega

/-- **Defect form of Hall's marriage theorem.** A matching saturating all but
`d` indices exists iff the family is at worst `d`-deficient. -/
theorem deficiency_matching_iff {t : ι → Finset α} {d : ℕ} :
    (∀ s : Finset ι, s.card ≤ (s.biUnion t).card + d) ↔
      ∃ (J : Finset ι) (f : ι → α),
        Fintype.card ι - d ≤ J.card ∧ Set.InjOn f ↑J ∧ ∀ i ∈ J, f i ∈ t i :=
  ⟨exists_matching_of_deficiency_le,
    fun ⟨_, _, hc, hi, hm⟩ => deficiency_le_of_matching hc hi hm⟩

/-- **`d = 0` recovers the marriage theorem.** Hall's condition gives a full
system of distinct representatives (injective on all of `ι`). -/
theorem exists_full_sdr_of_hall {t : ι → Finset α}
    (h : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) :
    ∃ f : ι → α, Set.InjOn f Set.univ ∧ ∀ i, f i ∈ t i := by
  obtain ⟨J, f, hc, hi, hm⟩ :=
    exists_matching_of_deficiency_le (d := 0) (by simpa using h)
  have hJ : J = univ := by
    have hle := Finset.card_le_univ J
    have : J.card = Fintype.card ι := by simp only [Nat.sub_zero] at hc; omega
    exact Finset.eq_univ_of_card J this
  refine ⟨f, ?_, ?_⟩
  · rw [hJ] at hi; simpa using hi
  · intro i; exact hm i (by rw [hJ]; exact mem_univ i)

end HallDefect
