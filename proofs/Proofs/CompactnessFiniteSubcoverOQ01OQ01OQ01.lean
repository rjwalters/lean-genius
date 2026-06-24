import Mathlib
import Proofs.CompactnessFiniteSubcoverOQ01OQ01

/-
# The Closed-Projection Characterization of Compactness (Forward Direction)

## What This Proves

If `Y` is a **compact** space then for every space `X` the first projection
`Prod.fst : X × Y → X` is a **closed map**: it sends closed subsets of the
product to closed subsets of `X`.

This is the forward half of the classical *closed-projection characterization of
compactness* ("Kuratowski's theorem"):

> `Y` is compact  ⟺  for every space `X` the projection `X × Y → X` is closed.

It answers the first open question recorded on the parent entry
`compactness-finite-subcover-oq-01-oq-01`:

> *Use the tube lemma to prove that the projection `X × Y → X` is a closed map
> when `Y` is compact, again running the finite-subcover argument rather than
> citing Mathlib's `isClosedMap_fst`-style result.*

## How It Works

The whole proof is one application of the **tube lemma** that the parent file
built by hand from the finite-subcover characterization
(`tube_lemma_compactSpace`).  To show `Prod.fst '' C` is closed for a closed
`C ⊆ X × Y` we show its complement is open: pick `x₀` *outside* the image, so the
entire vertical slice `{x₀} × Y` misses `C`, i.e. it lies in the open set `Cᶜ`.
The tube lemma upgrades this slice-level fact to a whole **tube** `W ×ˢ univ ⊆ Cᶜ`
around `x₀`; the open neighbourhood `W` then misses the image, witnessing
openness of the complement.

So compactness of the fibre is exactly what lets a *pointwise* miss
(`{x₀} × Y ∩ C = ∅`) be promoted to a *uniform* miss on a neighbourhood — the
content of "projecting out a compact factor is a closed operation".

## Results

* `isClosed_fst_image_of_compactSpace` — the headline: a closed set has closed
  image under `Prod.fst` when the second factor is compact.
* `isClosedMap_fst_via_tube` — packaged as `IsClosedMap`.  (Mathlib already has
  this as `isClosedMap_fst_of_compactSpace`, obtained via filters; the point here
  is that it falls straight out of the hand-built tube lemma.)
* `isClosedMap_snd_via_tube` — the symmetric statement (compact *first* factor),
  obtained by composing with the swap homeomorphism.
* `isClosed_exists_of_compactSpace` — a quantifier-elimination flavoured
  corollary: the existential projection `{x | ∃ y, (x, y) ∈ C}` of a closed set
  is closed when `y` ranges over a compact space.
* `isOpen_emptyFibre_of_compactSpace` — the dual open set `{x | ∀ y, (x, y) ∉ C}`
  (the points with empty fibre) is open.
* `isClosedMap_fst_real_unitInterval` — a concrete instance: the projection
  `ℝ × [0,1] → ℝ` is closed.

The converse direction (closed projection for *all* `X` forces `Y` compact) is
genuinely harder — it needs a witnessing space such as the one-point
compactification or an ultrafilter argument — and is left to a future leaf.
-/

open Set

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Closed image under the projection that forgets a compact factor.**

For a compact space `Y` and a closed set `C ⊆ X × Y`, the image
`Prod.fst '' C ⊆ X` is closed.

We prove the complement is open.  If `x₀ ∉ Prod.fst '' C` then `(x₀, y) ∉ C` for
every `y`, so the whole slice `{x₀} × Y` lies in the open set `Cᶜ`.  The tube
lemma (`tube_lemma_compactSpace`, derived by hand from the finite-subcover
characterization in the parent file) returns an open `W ∋ x₀` with the entire
tube `W ×ˢ univ ⊆ Cᶜ`; that `W` is then disjoint from `Prod.fst '' C`. -/
theorem isClosed_fst_image_of_compactSpace [CompactSpace Y] {C : Set (X × Y)}
    (hC : IsClosed C) : IsClosed (Prod.fst '' C) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  -- `x` is outside the image, so the whole slice `{x} × Y` avoids `C`.
  have hslice : ∀ y : Y, (x, y) ∈ Cᶜ := by
    intro y hmem
    exact hx ⟨(x, y), hmem, rfl⟩
  -- Promote the slice-level miss to a tube `W ×ˢ univ ⊆ Cᶜ`.
  obtain ⟨W, hWo, hxW, hWN⟩ := tube_lemma_compactSpace hC.isOpen_compl hslice
  refine ⟨W, ?_, hWo, hxW⟩
  -- The tube's base `W` misses the image.
  intro x' hx'
  rintro ⟨⟨a, b⟩, hab, rfl⟩
  exact hWN ⟨hx', mem_univ b⟩ hab

/-- **Projecting out a compact factor is a closed map.**  Packaged form of
`isClosed_fst_image_of_compactSpace`. -/
theorem isClosedMap_fst_via_tube [CompactSpace Y] :
    IsClosedMap (Prod.fst : X × Y → X) :=
  fun _ hC => isClosed_fst_image_of_compactSpace hC

/-- **Symmetric statement.**  When the *first* factor `X` is compact the second
projection `Prod.snd : X × Y → Y` is closed.  Obtained from the `fst` version on
`Y × X` by composing with the swap homeomorphism. -/
theorem isClosedMap_snd_via_tube [CompactSpace X] :
    IsClosedMap (Prod.snd : X × Y → Y) := by
  have heq : (Prod.snd : X × Y → Y) = Prod.fst ∘ (Homeomorph.prodComm X Y) := by
    funext p; rfl
  rw [heq]
  exact (isClosedMap_fst_via_tube).comp (Homeomorph.prodComm X Y).isClosedMap

/-- **Existential projection of a closed set is closed.**  A quantifier
elimination flavoured corollary: when the bound variable `y` ranges over a
compact space, the "shadow" `{x | ∃ y, (x, y) ∈ C}` of a closed set `C` is
closed.  (This set is exactly `Prod.fst '' C`.) -/
theorem isClosed_exists_of_compactSpace [CompactSpace Y] {C : Set (X × Y)}
    (hC : IsClosed C) : IsClosed {x : X | ∃ y : Y, (x, y) ∈ C} := by
  have hset : {x : X | ∃ y : Y, (x, y) ∈ C} = Prod.fst '' C := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(x, y), hy, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      exact ⟨b, hab⟩
  rw [hset]
  exact isClosed_fst_image_of_compactSpace hC

/-- **Empty-fibre set is open.**  Dual of the previous corollary: the set of
base points whose fibre is empty, `{x | ∀ y, (x, y) ∉ C}`, is open when the
fibre space is compact. -/
theorem isOpen_emptyFibre_of_compactSpace [CompactSpace Y] {C : Set (X × Y)}
    (hC : IsClosed C) : IsOpen {x : X | ∀ y : Y, (x, y) ∉ C} := by
  have hset : {x : X | ∀ y : Y, (x, y) ∉ C} = (Prod.fst '' C)ᶜ := by
    ext x
    constructor
    · intro h hmem
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
      exact h b hab
    · intro h y hy
      exact h ⟨(x, y), hy, rfl⟩
  rw [hset]
  exact (isClosed_fst_image_of_compactSpace hC).isOpen_compl

/-- **Concrete instance over `ℝ`.**  The projection `ℝ × [0,1] → ℝ` is a closed
map, since the unit interval `[0,1]` is compact. -/
theorem isClosedMap_fst_real_unitInterval :
    IsClosedMap (Prod.fst : ℝ × unitInterval → ℝ) :=
  isClosedMap_fst_via_tube
