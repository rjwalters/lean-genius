/-
Discrete Isoperimetric Inequality (1D): Equality Rigidity

Open Question from: Isoperimetric Theorem (Wiedijk #43), OQ-02 → OQ-03

The parent entry (IsoperimetricTheoremOQ02) proves the discrete 1D isoperimetric
*inequality*: every finite `S ⊆ ℤ` with `|S| ≥ 2` has vertex edge boundary
`|∂S| ≥ 2`, and integer intervals achieve `|∂S| = 2`. It explicitly leaves the
equality characterization unformalized:

  "The full equality characterization—|∂S| = 2 implies S is an interval—holds
   but is not formalized here; only the lower bound and the interval case are
   proved."

This file closes that gap. We prove the full RIGIDITY statement: for any finite
nonempty `S ⊆ ℤ`,

      |∂S| = 2   ⟺   S is an integer interval `[min S, max S]`.

Proof idea.
  (⟸) For an interval `[a,b]` the boundary is exactly `{a-1, b+1}`, card 2.
  (⟹) Contrapositive. Suppose `S` is not the interval `[m, M]` where `m = min S`,
      `M = max S`. Since `S ⊆ [m, M]` always, there is a "gap": the smallest
      element `g` of `[m, M] \ S`. Then `m < g < M` (because `m, M ∈ S`), and
      `g - 1 ∈ S` (as `g` is the *smallest* missing point and `g - 1 ∈ [m, M]`).
      Hence `g ∈ ∂S`, and `g` is distinct from the two extreme boundary points
      `m - 1` and `M + 1`. So `{m-1, M+1, g} ⊆ ∂S` gives `|∂S| ≥ 3 > 2`.

Remark on "boundary = 2·runs".
  The *edge* count (number of lattice edges crossing between `S` and its
  complement) equals `2·(number of maximal runs)`. That is NOT the same as the
  cardinality of the *vertex* boundary `∂S` used here: e.g. `S = {0, 2}` has
  `∂S = {-1, 1, 3}` (card 3), while the edge count is 4 = 2·2. We formalize the
  correct vertex-boundary rigidity; for the vertex boundary the clean statement
  is the `|∂S| = 2 ⟺ interval` equivalence proved below.

References:
  - Bollobás (1986), Combinatorics, Cambridge University Press.
  - Harper (1966), Optimal numberings and isoperimetric problems on graphs.

Tags: combinatorics, discrete-geometry, isoperimetric-inequality, rigidity
-/
import Mathlib

namespace DiscreteIsoperimetric1DRigidity

/-- The vertex edge boundary of `S ⊆ ℤ`: integers adjacent to some element of
    `S` but not themselves in `S`. (Same definition as the parent OQ-02 entry;
    repeated here to keep this file self-contained.) -/
def edgeBoundary (S : Finset ℤ) : Finset ℤ :=
  ((S.image (· - 1)) ∪ (S.image (· + 1))) \ S

/-- Membership characterization for the edge boundary. -/
lemma mem_edgeBoundary {S : Finset ℤ} {x : ℤ} :
    x ∈ edgeBoundary S ↔ (x + 1 ∈ S ∨ x - 1 ∈ S) ∧ x ∉ S := by
  simp only [edgeBoundary, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro (⟨a, ha, hax⟩ | ⟨a, ha, hax⟩)
    · left
      have : a = x + 1 := by linarith
      simpa [this] using ha
    · right
      have : a = x - 1 := by linarith
      simpa [this] using ha
  · rintro (h | h)
    · exact Or.inl ⟨x + 1, h, by ring⟩
    · exact Or.inr ⟨x - 1, h, by ring⟩

/-- A finite nonempty `S ⊆ ℤ` is contained in the interval spanned by its
    minimum and maximum. -/
lemma subset_Icc_min'_max' {S : Finset ℤ} (h : S.Nonempty) :
    S ⊆ Finset.Icc (S.min' h) (S.max' h) := by
  intro x hx
  exact Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩

/-- The edge boundary of an integer interval `[a, b]` is exactly `{a-1, b+1}`. -/
theorem edgeBoundary_Icc {a b : ℤ} (h : a ≤ b) :
    edgeBoundary (Finset.Icc a b) = {a - 1, b + 1} := by
  ext x
  rw [mem_edgeBoundary]
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, hnot⟩
    rcases h1 with ⟨ha1, hb1⟩ | ⟨ha2, hb2⟩
    · have : x < a := by
        by_contra hc; push_neg at hc
        exact hnot ⟨hc, by linarith⟩
      left; linarith
    · have : x > b := by
        by_contra hc; push_neg at hc
        exact hnot ⟨by linarith, hc⟩
      right; linarith
  · rintro (rfl | rfl)
    · refine ⟨Or.inl ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · push_neg; intro h1; linarith
    · refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · push_neg; intro h1; linarith

/-- For an interval `[a, b]` with `a ≤ b`, the edge boundary has exactly 2
    elements. -/
theorem edgeBoundary_Icc_card {a b : ℤ} (h : a ≤ b) :
    (edgeBoundary (Finset.Icc a b)).card = 2 := by
  rw [edgeBoundary_Icc h]
  rw [Finset.card_insert_of_notMem (by simp; linarith), Finset.card_singleton]

/-- The lower extreme `min S - 1` always lies in the boundary. -/
lemma min_sub_one_mem_edgeBoundary {S : Finset ℤ} (h : S.Nonempty) :
    S.min' h - 1 ∈ edgeBoundary S := by
  rw [mem_edgeBoundary]
  refine ⟨Or.inl ?_, ?_⟩
  · simpa using S.min'_mem h
  · intro hcontra
    have := S.min'_le _ hcontra
    omega

/-- The upper extreme `max S + 1` always lies in the boundary. -/
lemma max_add_one_mem_edgeBoundary {S : Finset ℤ} (h : S.Nonempty) :
    S.max' h + 1 ∈ edgeBoundary S := by
  rw [mem_edgeBoundary]
  refine ⟨Or.inr ?_, ?_⟩
  · simpa using S.max'_mem h
  · intro hcontra
    have := S.le_max' _ hcontra
    omega

/-- **Gap lemma.** If a finite nonempty `S ⊆ ℤ` is *not* the full interval
    `[min S, max S]`, then there is an interior boundary point `g` with
    `min S < g < max S`. -/
lemma exists_interior_boundary_of_ne_Icc {S : Finset ℤ} (h : S.Nonempty)
    (hne : S ≠ Finset.Icc (S.min' h) (S.max' h)) :
    ∃ g, S.min' h < g ∧ g < S.max' h ∧ g ∈ edgeBoundary S := by
  set m := S.min' h with hm
  set M := S.max' h with hM
  -- The complement of S inside [m, M] is nonempty, since S ⊆ [m, M] but S ≠ [m, M].
  have hsub : S ⊆ Finset.Icc m M := subset_Icc_min'_max' h
  have hmissing : (Finset.Icc m M \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hcon
    exact hne (Finset.Subset.antisymm hsub hcon)
  -- Take the smallest missing point g.
  set g := (Finset.Icc m M \ S).min' hmissing with hg
  have hg_mem : g ∈ Finset.Icc m M \ S := (Finset.Icc m M \ S).min'_mem hmissing
  rw [Finset.mem_sdiff, Finset.mem_Icc] at hg_mem
  obtain ⟨⟨hmg, hgM⟩, hgS⟩ := hg_mem
  -- g ≠ m and g ≠ M since m, M ∈ S but g ∉ S.
  have hm_mem : m ∈ S := S.min'_mem h
  have hM_mem : M ∈ S := S.max'_mem h
  have hg_ne_m : g ≠ m := fun hc => hgS (hc ▸ hm_mem)
  have hg_ne_M : g ≠ M := fun hc => hgS (hc ▸ hM_mem)
  have hmg' : m < g := lt_of_le_of_ne hmg (Ne.symm hg_ne_m)
  have hgM' : g < M := lt_of_le_of_ne hgM hg_ne_M
  -- g - 1 lies in [m, M] and is below the smallest missing point, hence in S.
  have hg1_mem : g - 1 ∈ S := by
    by_contra hc
    have hg1_in : g - 1 ∈ Finset.Icc m M \ S := by
      rw [Finset.mem_sdiff, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hc⟩
    have := (Finset.Icc m M \ S).min'_le _ hg1_in
    rw [← hg] at this
    omega
  refine ⟨g, hmg', hgM', ?_⟩
  rw [mem_edgeBoundary]
  exact ⟨Or.inr hg1_mem, hgS⟩

/-- **Equality rigidity** for the discrete 1D isoperimetric inequality.
    For a finite nonempty `S ⊆ ℤ`, the vertex edge boundary has cardinality
    exactly 2 **iff** `S` is the integer interval `[min S, max S]`. -/
theorem edgeBoundary_card_eq_two_iff {S : Finset ℤ} (h : S.Nonempty) :
    (edgeBoundary S).card = 2 ↔ S = Finset.Icc (S.min' h) (S.max' h) := by
  set m := S.min' h with hm
  set M := S.max' h with hM
  have hmM : m ≤ M := S.min'_le _ (S.max'_mem h)
  constructor
  · -- card = 2 ⟹ interval. Contrapositive: not interval ⟹ a third boundary point.
    intro hcard
    by_contra hne
    obtain ⟨g, hmg, hgM, hg_mem⟩ := exists_interior_boundary_of_ne_Icc h hne
    -- {m-1, M+1, g} are three distinct boundary points.
    have h_lo : m - 1 ∈ edgeBoundary S := min_sub_one_mem_edgeBoundary h
    have h_hi : M + 1 ∈ edgeBoundary S := max_add_one_mem_edgeBoundary h
    have h_sub : ({m - 1, M + 1, g} : Finset ℤ) ⊆ edgeBoundary S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h_lo
      · exact h_hi
      · exact hg_mem
    have h_card3 : ({m - 1, M + 1, g} : Finset ℤ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp only [Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have := Finset.card_le_card h_sub
    rw [h_card3, hcard] at this
    omega
  · -- interval ⟹ card = 2
    intro hS
    rw [hS, edgeBoundary_Icc_card hmM]

/-- Packaged rigidity statement, mirroring the parent's `discrete_isoperimetric_1d`:
    the boundary attains its minimum value 2 exactly on integer intervals. -/
theorem discrete_isoperimetric_1d_rigidity :
    ∀ (S : Finset ℤ) (h : S.Nonempty),
      (edgeBoundary S).card = 2 ↔ S = Finset.Icc (S.min' h) (S.max' h) :=
  fun _ h => edgeBoundary_card_eq_two_iff h

end DiscreteIsoperimetric1DRigidity
