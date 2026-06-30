import Mathlib

/-
# The Tube Lemma from the Finite-Subcover Characterization

## What This Proves

The **tube lemma**: if `K ⊆ Y` is compact and `N ⊆ X × Y` is an open set
containing the whole slice `{x₀} ×ˢ K`, then there is an open neighbourhood `W`
of `x₀` whose entire *tube* `W ×ˢ K` is still contained in `N`.

This file answers the first open question recorded on the parent entry
`compactness-finite-subcover-oq-01`:

> *Re-derive the tube lemma directly from the finite-subcover characterization.*

`Mathlib` already proves a `generalized_tube_lemma`, but it is obtained from the
filter/uniformity machinery.  The point of this file is to produce the tube
lemma **by running the finite-subcover characterization by hand**, exactly in
the spirit of the parent file:

* For each point `y ∈ K` the pair `(x₀, y)` lies in the open set `N`, so a basic
  product neighbourhood `u y ×ˢ v y ⊆ N` exists (`isOpen_prod_iff`).
* The slices `{v y}` form an open cover of the compact set `K`.  We extract a
  **finite** subcover indexed by a `Finset` — this is the only place compactness
  is used, and it is invoked through the finite-subcover characterization
  `IsCompact.elim_finite_subcover` (the Heine–Borel form the parent file
  re-exports as `compact_iff_finite_subcover`).
* The finite intersection `W = ⋂ y ∈ r, u y` of the corresponding base slices is
  open and contains `x₀`, and `W ×ˢ K ⊆ N` because every `(x, k)` lands in some
  cell `u y ×ˢ v y ⊆ N`.

The finite intersection collapsing a pointwise family of neighbourhoods into a
single tube is the genuine content — it is the same "extract a finite subcover,
then union/intersect the finite index set" move that powers the parent's
union theorem, run in the product setting.

## Results

* `tube_lemma_of_finite_subcover` — the set-level tube lemma for a compact
  `K ⊆ Y` and an open `N ⊇ {x₀} ×ˢ K`.
* `tube_lemma_compactSpace` — the classical headline for a `CompactSpace Y`: an
  open set containing the slice `{x₀} ×ˢ univ` contains a whole tube `W ×ˢ univ`.
* `tube_lemma_forall` — the pointwise restatement: `(x, y) ∈ N` for every `x ∈ W`
  and every `y ∈ K`.
* `tube_lemma_mem_nhds` — the neighbourhood-filter consequence: the tube
  `W ×ˢ K` is a neighbourhood of each point of `{x₀} ×ˢ K`.
* `isOpen_tube_Icc` — a concrete instance over `ℝ`: any open set containing the
  vertical segment `{0} ×ˢ [0,1]` contains a genuine tube around it.
-/

open Set

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The tube lemma, re-derived from the finite-subcover characterization.**

Let `K ⊆ Y` be compact and `N ⊆ X × Y` open with the slice `{x₀} ×ˢ K ⊆ N`.
Then there is an open neighbourhood `W` of `x₀` with `W ×ˢ K ⊆ N`.

The proof extracts a basic product neighbourhood at each point of the slice,
covers `K` by their `Y`-projections, takes a **finite** subcover via
`IsCompact.elim_finite_subcover`, and intersects the finitely many
`X`-projections to obtain the tube. -/
theorem tube_lemma_of_finite_subcover {K : Set Y} (hK : IsCompact K)
    {N : Set (X × Y)} (hN : IsOpen N) {x₀ : X} (hslice : ({x₀} ×ˢ K : Set (X × Y)) ⊆ N) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ (W ×ˢ K : Set (X × Y)) ⊆ N := by
  classical
  -- At each `y ∈ K`, the point `(x₀, y)` is in the open set `N`, so we get a basic
  -- product neighbourhood `u y ×ˢ v y ⊆ N`.
  have hpt : ∀ y : K, ∃ u : Set X, ∃ w : Set Y,
      IsOpen u ∧ IsOpen w ∧ x₀ ∈ u ∧ (y : Y) ∈ w ∧ (u ×ˢ w : Set (X × Y)) ⊆ N := by
    intro y
    have hmem : (x₀, (y : Y)) ∈ N :=
      hslice ⟨rfl, y.2⟩
    obtain ⟨u, w, hu, hw, hxu, hyw, hsub⟩ := isOpen_prod_iff.1 hN x₀ (y : Y) hmem
    exact ⟨u, w, hu, hw, hxu, hyw, hsub⟩
  choose u w huo hwo hxu hyw hsub using hpt
  -- The `Y`-projections `w y` form an open cover of the compact set `K`.
  have hcov : K ⊆ ⋃ y : K, w y := by
    intro k hk
    exact mem_iUnion.2 ⟨⟨k, hk⟩, hyw ⟨k, hk⟩⟩
  obtain ⟨r, hr⟩ := hK.elim_finite_subcover w hwo hcov
  -- The tube is the finite intersection of the corresponding `X`-projections.
  refine ⟨⋂ y ∈ r, u y, ?_, ?_, ?_⟩
  · exact r.finite_toSet.isOpen_biInter fun y _ => huo y
  · exact mem_iInter₂.2 fun y _ => hxu y
  · rintro ⟨x, k⟩ ⟨hxW, hkK⟩
    -- `k` lies in some cell `w y` of the finite subcover; on that cell the tube
    -- sits inside `u y ×ˢ w y ⊆ N`.
    obtain ⟨y, hyr, hky⟩ := mem_iUnion₂.1 (hr hkK)
    have hxu' : x ∈ u y := mem_iInter₂.1 hxW y hyr
    exact hsub y ⟨hxu', hky⟩

/-- **The classical tube lemma for a compact space.**  If `Y` is compact and
`N ⊆ X × Y` is open with `(x₀, y) ∈ N` for every `y`, then there is an open
neighbourhood `W` of `x₀` whose whole tube `W ×ˢ univ` lies in `N`. -/
theorem tube_lemma_compactSpace [CompactSpace Y] {N : Set (X × Y)} (hN : IsOpen N)
    {x₀ : X} (hslice : ∀ y : Y, (x₀, y) ∈ N) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ (W ×ˢ (univ : Set Y) : Set (X × Y)) ⊆ N := by
  refine tube_lemma_of_finite_subcover (isCompact_univ) hN ?_
  rintro ⟨x, y⟩ ⟨hx, -⟩
  simp only [mem_singleton_iff] at hx
  subst hx
  exact hslice y

/-- **Pointwise restatement.**  Under the hypotheses of the tube lemma there is
an open neighbourhood `W` of `x₀` with `(x, y) ∈ N` for all `x ∈ W` and all
`y ∈ K`. -/
theorem tube_lemma_forall {K : Set Y} (hK : IsCompact K)
    {N : Set (X × Y)} (hN : IsOpen N) {x₀ : X} (hslice : ({x₀} ×ˢ K : Set (X × Y)) ⊆ N) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∀ x ∈ W, ∀ y ∈ K, (x, y) ∈ N := by
  obtain ⟨W, hWo, hxW, hWN⟩ := tube_lemma_of_finite_subcover hK hN hslice
  exact ⟨W, hWo, hxW, fun x hx y hy => hWN ⟨hx, hy⟩⟩

/-- **Neighbourhood-filter consequence.**  The tube `W ×ˢ K` produced by the
tube lemma is a neighbourhood of every point `(x₀, k)` of the slice, and in
particular `N` itself is. -/
theorem tube_lemma_mem_nhds {K : Set Y} (hK : IsCompact K)
    {N : Set (X × Y)} (hN : IsOpen N) {x₀ : X} (hslice : ({x₀} ×ˢ K : Set (X × Y)) ⊆ N) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧
      (W ×ˢ K : Set (X × Y)) ⊆ N ∧ ∀ k ∈ K, N ∈ nhds ((x₀, k) : X × Y) := by
  obtain ⟨W, hWo, hxW, hWN⟩ := tube_lemma_of_finite_subcover hK hN hslice
  refine ⟨W, hWo, hxW, hWN, fun k hk => ?_⟩
  exact hN.mem_nhds (hslice ⟨rfl, hk⟩)

/-- **Concrete instance over `ℝ`.**  Any open set `N` containing the vertical
segment `{0} ×ˢ [0,1]` contains a genuine tube `W ×ˢ [0,1]` around it, with `W`
an open neighbourhood of `0`.  Here `[0,1] = Icc 0 1` is compact by
`isCompact_Icc`. -/
theorem isOpen_tube_Icc {N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (hslice : ({(0 : ℝ)} ×ˢ Set.Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ⊆ N) :
    ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧
      (W ×ˢ Set.Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ⊆ N :=
  tube_lemma_of_finite_subcover isCompact_Icc hN hslice
