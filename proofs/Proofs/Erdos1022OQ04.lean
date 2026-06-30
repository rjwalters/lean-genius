import Mathlib

/-!
# Erdős #1022 OQ-02 — The 2-Colorability Threshold for Complete Uniform Hypergraphs

Erdős Problem #1022 concerns **Property B**: a family `F` of sets has Property B
when there is a 2-coloring of the ground set with no member of `F` monochromatic.
The parent file proves the **first-moment upper bound** (Erdős 1964): a `t`-uniform
family with fewer than `2^{t-1}` edges always has Property B.  This file supplies the
complementary **lower-bound / sharpness companion**: an *explicit* family that fails
Property B, with an *exact* threshold.

## Main result

Let `K_n^{(t)}` be the **complete `t`-uniform hypergraph** on an `n`-element ground
set — every `t`-subset is an edge.  Then

> `K_n^{(t)}` has Property B  ⟺  `n ≤ 2t − 2`   (for `t ≥ 1`).

Equivalently, `K_n^{(t)}` is 2-colorable exactly when `n < 2t − 1`, and the first
value of `n` at which 2-colorability fails is `n = 2t − 1`.

* `hasPropertyB_completeUnif_iff` — the threshold, both directions.
* `not_hasPropertyB_completeUnif` — failure for `2t − 1 ≤ n` (pigeonhole: some color
  class has `≥ t` vertices, hence contains a monochromatic edge).
* `hasPropertyB_completeUnif` — success for `n ≤ 2t − 2` (split the ground set into
  two classes of size `≤ t − 1`, so no class contains a whole edge).

## Consequence for the extremal function `m(t)`

`m(t)` denotes the least number of edges in a `t`-uniform hypergraph without
Property B.  Taking `n = 2t − 1` gives a non-2-colorable family with exactly
`C(2t−1, t)` edges, hence

> `m(t) ≤ C(2t − 1, t)`,

which together with the parent's first-moment bound `2^{t-1} ≤ m(t)` sandwiches the
(still open) exact value of `m(t)`.

* `exists_non_propertyB_card_choose` — the witness family and its edge count.

All results are proved by elementary finite counting; no axioms, no `native_decide`.
-/

namespace Erdos1022OQ02

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A coloring `c : α → Bool` is **monochromatic** on `A` when every vertex of `A`
gets the same color. -/
def IsMonoOn (c : α → Bool) (A : Finset α) : Prop := ∃ b, ∀ x ∈ A, c x = b

/-- **Property B** for a family `F` on a finite ground set: there is a 2-coloring
under which no member of `F` is monochromatic. -/
def HasPropertyB (F : Finset (Finset α)) : Prop :=
  ∃ c : α → Bool, ∀ A ∈ F, ¬ IsMonoOn c A

/-- The **complete `t`-uniform hypergraph**: the family of all `t`-element subsets of
the ground set. -/
def completeUnif (α : Type*) [Fintype α] [DecidableEq α] (t : ℕ) : Finset (Finset α) :=
  Finset.univ.powersetCard t

@[simp] theorem mem_completeUnif {t : ℕ} {A : Finset α} :
    A ∈ completeUnif α t ↔ A.card = t := by
  simp [completeUnif, Finset.mem_powersetCard]

/-- The complete `t`-uniform hypergraph has exactly `C(n, t)` edges. -/
theorem card_completeUnif (t : ℕ) :
    (completeUnif α t).card = Nat.choose (Fintype.card α) t := by
  rw [completeUnif, Finset.card_powersetCard, Finset.card_univ]

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Failure of Property B above the threshold
-- ════════════════════════════════════════════════════════════════════════

/-- **Pigeonhole.** For any 2-coloring of an `n`-element set with `2t − 1 ≤ n`, one of
the two color classes has at least `t` vertices. -/
theorem exists_large_color_class (c : α → Bool) {t : ℕ}
    (hn : 2 * t - 1 ≤ Fintype.card α) :
    ∃ b : Bool, t ≤ (Finset.univ.filter (fun x => c x = b)).card := by
  -- the two color classes partition the ground set
  have hsplit :
      (Finset.univ.filter (fun x => c x = true)).card +
        (Finset.univ.filter (fun x => c x = false)).card = Fintype.card α := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset α)) (p := fun x => c x = true)
    simpa only [Bool.not_eq_true, Finset.card_univ] using h
  by_contra hcon
  push_neg at hcon
  have h1 := hcon true
  have h2 := hcon false
  omega

/-- **Above the threshold, Property B fails.** If `2t − 1 ≤ n` (and `t ≥ 1`), then the
complete `t`-uniform hypergraph on `n` vertices is *not* 2-colorable: every coloring
forces a monochromatic `t`-edge inside the larger color class. -/
theorem not_hasPropertyB_completeUnif {t : ℕ} (ht : 1 ≤ t)
    (hn : 2 * t - 1 ≤ Fintype.card α) :
    ¬ HasPropertyB (completeUnif α t) := by
  rintro ⟨c, hc⟩
  obtain ⟨b, hb⟩ := exists_large_color_class c hn
  -- carve out a `t`-subset of the large color class
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ.filter (fun x => c x = b)) (n := t) hb
  -- it is an edge of the complete hypergraph
  have hSedge : S ∈ completeUnif α t := mem_completeUnif.mpr hScard
  -- and it is monochromatic with color `b`
  have hSmono : IsMonoOn c S := by
    refine ⟨b, fun x hx => ?_⟩
    have := hSsub hx
    simpa using (Finset.mem_filter.mp this).2
  exact hc S hSedge hSmono

-- ════════════════════════════════════════════════════════════════════════
-- § 2. Property B at or below the threshold
-- ════════════════════════════════════════════════════════════════════════

/-- **At or below the threshold, Property B holds.** If `n ≤ 2t − 2` then the complete
`t`-uniform hypergraph on `n` vertices is 2-colorable: split the ground set into two
classes of size `≤ t − 1`, so neither class contains a whole `t`-edge. -/
theorem hasPropertyB_completeUnif {t : ℕ} (ht : 1 ≤ t)
    (hn : Fintype.card α ≤ 2 * t - 2) :
    HasPropertyB (completeUnif α t) := by
  -- pick a "first half" `T` of size `n / 2`; its complement has size `n − n/2`
  obtain ⟨T, _, hTcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset α)) (n := Fintype.card α / 2)
      (by rw [Finset.card_univ]; omega)
  -- color by membership in `T`
  refine ⟨fun x => decide (x ∈ T), fun A hA hmono => ?_⟩
  have hAcard : A.card = t := mem_completeUnif.mp hA
  obtain ⟨b, hb⟩ := hmono
  cases b with
  | true =>
    -- all of `A` lands in `T`, but `|T| = n/2 ≤ t − 1 < t`
    have hAT : A ⊆ T := by
      intro x hx; simpa using (hb x hx)
    have := Finset.card_le_card hAT
    omega
  | false =>
    -- all of `A` lands outside `T`, but `|Tᶜ| = n − n/2 ≤ t − 1 < t`
    have hAT : A ⊆ Tᶜ := by
      intro x hx
      have : decide (x ∈ T) = false := hb x hx
      simp only [decide_eq_false_iff_not] at this
      exact Finset.mem_compl.mpr this
    have hcardc : (Tᶜ : Finset α).card = Fintype.card α - Fintype.card α / 2 := by
      rw [Finset.card_compl, hTcard]
    have := Finset.card_le_card hAT
    omega

-- ════════════════════════════════════════════════════════════════════════
-- § 3. The exact threshold
-- ════════════════════════════════════════════════════════════════════════

/-- **The 2-colorability threshold.** For `t ≥ 1`, the complete `t`-uniform hypergraph
on an `n`-element ground set has Property B if and only if `n ≤ 2t − 2`.

Thus the critical size at which 2-colorability first fails is exactly `n = 2t − 1`. -/
theorem hasPropertyB_completeUnif_iff {t : ℕ} (ht : 1 ≤ t) :
    HasPropertyB (completeUnif α t) ↔ Fintype.card α ≤ 2 * t - 2 := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact not_hasPropertyB_completeUnif ht (by omega) h
  · exact hasPropertyB_completeUnif ht

-- ════════════════════════════════════════════════════════════════════════
-- § 4. Consequence for the extremal function m(t)
-- ════════════════════════════════════════════════════════════════════════

/-- **Upper bound on the extremal function `m(t)`.** For every `t ≥ 1` there is a
`t`-uniform family — namely the complete `t`-uniform hypergraph on `2t − 1` vertices —
that has *no* Property B and consists of exactly `C(2t − 1, t)` edges.

Combined with the parent's first-moment bound `2^{t-1} ≤ m(t)`, this gives the
sandwich `2^{t-1} ≤ m(t) ≤ C(2t − 1, t)`. -/
theorem exists_non_propertyB_card_choose (t : ℕ) (ht : 1 ≤ t) :
    ∃ F : Finset (Finset (Fin (2 * t - 1))),
      (∀ A ∈ F, A.card = t) ∧ ¬ HasPropertyB F ∧ F.card = Nat.choose (2 * t - 1) t := by
  have hcard : Fintype.card (Fin (2 * t - 1)) = 2 * t - 1 := Fintype.card_fin _
  refine ⟨completeUnif (Fin (2 * t - 1)) t, fun A hA => mem_completeUnif.mp hA, ?_, ?_⟩
  · exact not_hasPropertyB_completeUnif ht (by rw [hcard])
  · rw [card_completeUnif, hcard]

-- ════════════════════════════════════════════════════════════════════════
-- § 5. Small concrete instances
-- ════════════════════════════════════════════════════════════════════════

/-- The triangle `K_3` (complete `2`-uniform hypergraph on `3` vertices) is not
2-colorable — the smallest non-bipartite graph, here recovered as `t = 2`,
`n = 2t − 1 = 3`. -/
example : ¬ HasPropertyB (completeUnif (Fin 3) 2) :=
  not_hasPropertyB_completeUnif (by norm_num) (by simp)

/-- The complete `3`-uniform hypergraph on `5` vertices is not 2-colorable, witnessing
`m(3) ≤ C(5,3) = 10`. -/
example : ¬ HasPropertyB (completeUnif (Fin 5) 3) :=
  not_hasPropertyB_completeUnif (by norm_num) (by simp)

/-- Below threshold: the complete `3`-uniform hypergraph on `4` vertices *is*
2-colorable (`n = 4 ≤ 2·3 − 2 = 4`). -/
example : HasPropertyB (completeUnif (Fin 4) 3) :=
  hasPropertyB_completeUnif (by norm_num) (by simp)

end Erdos1022OQ02
