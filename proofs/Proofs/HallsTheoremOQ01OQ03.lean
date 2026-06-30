/-
# Regular bipartite graphs have a perfect matching (Hall, OQ-01 → OQ-03)

Open Question: halls-theorem-oq-01-oq-03
Parent gallery entry: halls-theorem-oq-01 (the full biconditional bipartite Hall theorem).

## Context

The parent `HallsTheoremOQ01` and its companions establish Hall's marriage theorem as a
biconditional for (locally finite) bipartite graphs. This file records two consequences at
the **`Finset` transversal** level, where Mathlib packages the marriage theorem as

  `Finset.all_card_le_biUnion_card_iff_exists_injective`
    `: (∀ s, #s ≤ #(s.biUnion t)) ↔ ∃ f, Function.Injective f ∧ ∀ i, f i ∈ t i`,

i.e. an injective **system of distinct representatives** (SDR) exists iff Hall's condition
holds. The first consequence (`exists_sdr_of_hall`) is exactly the forward direction, recorded
explicitly as the SDR existence statement.

The second, and the genuinely new content, is the classical **regularity application**, which
is absent from both Mathlib and the existing gallery (the gallery has the *conditional* matching
theorems, but not the regular case): *every `k`-regular bipartite graph with `k ≥ 1` carries a
perfect matching.* The whole point is that regularity is verified by a **double-counting**
estimate rather than checked by hand:

* `sum_card_eq` — the fundamental double-counting identity: the incidences leaving a left set
  `s` can be summed either over `s` (by degree) or over the right vertices (by `s`-back-degree);
* `card_eq_of_regular` — `k`-biregularity (`k ≥ 1`) forces `|ι| = |α|` (balance);
* `hall_condition_of_regular` — `k`-biregularity forces Hall's condition `#s ≤ #(s.biUnion t)`
  (the core estimate `k·#s ≤ k·#(s.biUnion t)`);
* `exists_perfect_matching_of_regular` — combining the two with the marriage theorem yields a
  **bijective** transversal `f : ι → α` with `f i ∈ t i`: a perfect matching.

This is the matching-theory backbone behind, e.g., bipartite edge-colouring and the
Birkhoff–von Neumann theorem, where regularity is the standard hypothesis that makes Hall's
condition automatic.

## Sorries: 0   Axioms: 0
-/
import Mathlib

open Finset

namespace HallsTheoremOQ01OQ03

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]

/-- The neighbourhood function `t` of a bipartite incidence structure is **`k`-biregular** if
every left vertex `i` has exactly `k` neighbours, and every right vertex `a` is a neighbour of
exactly `k` left vertices. -/
structure IsBiregular (t : ι → Finset α) (k : ℕ) : Prop where
  /-- Every left vertex has degree `k`. -/
  left : ∀ i, (t i).card = k
  /-- Every right vertex has back-degree `k`. -/
  right : ∀ a, (univ.filter (fun i => a ∈ t i)).card = k

omit [Fintype ι] [Fintype α] [DecidableEq ι] in
/-- **Double-counting identity.** For a set `s` of left vertices and any superset `B` of the
neighbourhood `s.biUnion t`, the total number of incidences emanating from `s` equals the sum,
over the right vertices in `B`, of the number of `s`-neighbours of each. Both sides count the
set of incident pairs `{(i, a) : i ∈ s, a ∈ t i}`. -/
lemma sum_card_eq (t : ι → Finset α) (s : Finset ι) {B : Finset α}
    (hB : s.biUnion t ⊆ B) :
    ∑ i ∈ s, (t i).card = ∑ a ∈ B, (s.filter (fun i => a ∈ t i)).card := by
  -- Expand each degree as a sum of indicators over `B`.
  have key : ∀ i ∈ s, (t i).card = ∑ a ∈ B, (if a ∈ t i then 1 else 0) := by
    intro i hi
    have hsub : t i ⊆ B := fun a ha => hB (Finset.mem_biUnion.mpr ⟨i, hi, ha⟩)
    have hfilt : (B.filter (fun a => a ∈ t i)) = t i := by
      apply Finset.ext; intro a
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    calc (t i).card = (B.filter (fun a => a ∈ t i)).card := by rw [hfilt]
      _ = ∑ a ∈ B, (if a ∈ t i then 1 else 0) := by rw [Finset.card_filter]
  calc ∑ i ∈ s, (t i).card
      = ∑ i ∈ s, ∑ a ∈ B, (if a ∈ t i then 1 else 0) := Finset.sum_congr rfl key
    _ = ∑ a ∈ B, ∑ i ∈ s, (if a ∈ t i then 1 else 0) := Finset.sum_comm
    _ = ∑ a ∈ B, (s.filter (fun i => a ∈ t i)).card := by
          apply Finset.sum_congr rfl; intro a _; rw [Finset.card_filter]

/-- **Balance.** A `k`-biregular incidence structure with `k ≥ 1` has equally many left and
right vertices: `|ι| = |α|`. Both counts equal the total number of incidences divided by `k`. -/
lemma card_eq_of_regular {t : ι → Finset α} {k : ℕ} (h : IsBiregular t k) (hk : 1 ≤ k) :
    Fintype.card ι = Fintype.card α := by
  have hsum : ∑ i : ι, (t i).card
      = ∑ a : α, (univ.filter (fun i => a ∈ t i)).card :=
    sum_card_eq t univ (Finset.subset_univ _)
  have hL : ∑ i : ι, (t i).card = Fintype.card ι * k := by
    rw [Finset.sum_congr rfl (fun i _ => h.left i), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hR : ∑ a : α, (univ.filter (fun i => a ∈ t i)).card = Fintype.card α * k := by
    rw [Finset.sum_congr rfl (fun a _ => h.right a), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have : Fintype.card ι * k = Fintype.card α * k := by rw [← hL, ← hR, hsum]
  exact Nat.eq_of_mul_eq_mul_right hk this

/-- **Hall's condition holds for regular structures.** If `t` is `k`-biregular with `k ≥ 1`,
then every set `s` of left vertices satisfies `#s ≤ #(s.biUnion t)`. The estimate comes from
double counting: the `k·#s` incidences out of `s` all land in `s.biUnion t`, where each vertex
absorbs at most `k` of them, so `k·#s ≤ k·#(s.biUnion t)`. -/
lemma hall_condition_of_regular {t : ι → Finset α} {k : ℕ} (h : IsBiregular t k) (hk : 1 ≤ k)
    (s : Finset ι) : s.card ≤ (s.biUnion t).card := by
  have hcount : ∑ i ∈ s, (t i).card
      = ∑ a ∈ s.biUnion t, (s.filter (fun i => a ∈ t i)).card :=
    sum_card_eq t s (subset_refl _)
  have hLHS : ∑ i ∈ s, (t i).card = k * s.card := by
    rw [Finset.sum_congr rfl (fun i _ => h.left i), Finset.sum_const, smul_eq_mul, mul_comm]
  -- Each right vertex has at most `k` back-neighbours in `s` (it has exactly `k` overall).
  have hfib : ∀ a ∈ s.biUnion t, (s.filter (fun i => a ∈ t i)).card ≤ k := by
    intro a _
    calc (s.filter (fun i => a ∈ t i)).card
        ≤ (univ.filter (fun i => a ∈ t i)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))
      _ = k := h.right a
  have hRHS : ∑ a ∈ s.biUnion t, (s.filter (fun i => a ∈ t i)).card
      ≤ k * (s.biUnion t).card := by
    calc ∑ a ∈ s.biUnion t, (s.filter (fun i => a ∈ t i)).card
        ≤ ∑ _a ∈ s.biUnion t, k := Finset.sum_le_sum hfib
      _ = k * (s.biUnion t).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hkey : k * s.card ≤ k * (s.biUnion t).card := by rw [← hLHS, hcount]; exact hRHS
  exact Nat.le_of_mul_le_mul_left hkey hk

omit [Fintype ι] [Fintype α] [DecidableEq ι] in
/-- **System of distinct representatives (SDR) from Hall's condition.** The forward direction of
Mathlib's marriage theorem, recorded explicitly: if every subfamily `s` satisfies
`#s ≤ #(s.biUnion t)`, then the family `t` admits an injective transversal `f` with `f i ∈ t i`
for every `i`. -/
theorem exists_sdr_of_hall (t : ι → Finset α)
    (H : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ t i :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 H

/-- **Every `k`-regular bipartite graph with `k ≥ 1` has a perfect matching.**
Phrased via the neighbourhood function `t`: there is a **bijection** `f : ι → α` with
`f i ∈ t i` for every left vertex `i`.

The proof assembles three facts: regularity forces Hall's condition
(`hall_condition_of_regular`), Hall's condition yields an injective transversal
(`exists_sdr_of_hall`), and regularity forces `|ι| = |α|` (`card_eq_of_regular`), so the
injective transversal between equinumerous finite types is automatically bijective. -/
theorem exists_perfect_matching_of_regular {t : ι → Finset α} {k : ℕ}
    (h : IsBiregular t k) (hk : 1 ≤ k) :
    ∃ f : ι → α, Function.Bijective f ∧ ∀ i, f i ∈ t i := by
  obtain ⟨f, hinj, hf⟩ :=
    exists_sdr_of_hall t (hall_condition_of_regular h hk)
  refine ⟨f, ?_, hf⟩
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, card_eq_of_regular h hk⟩

end HallsTheoremOQ01OQ03
