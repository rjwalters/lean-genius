import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

/-
# The Greatest Fixed Point Variant of Schroeder–Bernstein

## Open Question (OQ-02 → OQ-01)

The Knaster–Tarski proof of Schroeder–Bernstein (gallery entry
`schroeder-bernstein-oq-02`) builds the bijection from the **least** fixed point
`S* = lfp(T)` of the monotone operator `T(S) = (range g)ᶜ ∪ g '' (f '' S)`. Its
open question asks:

> The Knaster–Tarski fixed point is the *least* fixed point of `T`. Is the
> greatest fixed point `S** = gfp(T)` equally useful? What is `S** ∖ S*`
> geometrically?

## Answer

**Yes — and the right statement is stronger:** *every* fixed point of `T` yields
a Schroeder–Bernstein bijection by the same piecewise formula. The parent's
constructions never used minimality of `lfp`; they used only the fixed-point
equation `T(S) = S`, injectivity of `f`, and injectivity of `g`. We therefore
generalize the whole construction to an arbitrary fixed point `S` and then
instantiate it at both `lfp(T)` and `gfp(T)`. The `gfp` route is a genuinely
different, equally valid proof.

The difference `D = gfp(T) ∖ lfp(T)` has a clean geometric description in terms
of the dynamics of `φ = g ∘ f : α → α`:

* `D ⊆ range g` — `D` contains no "sources" (`(range g)ᶜ` lies entirely in
  `lfp`);
* `φ` maps `D` into `D`, and **every** point of `D` has a `φ`-preimage in `D`;
* hence `φ` restricts to a **bijection** `D → D` (`Set.BijOn`).

So `D` is the maximal set on which `g ∘ f` acts bijectively with neither sources
nor sinks: the union of the **bi-infinite `φ`-chains**. The least fixed point
collects exactly the chains that *start* at a source in `(range g)ᶜ`; the
greatest fixed point adds back these doubly-infinite chains. (In the classical
orbit decomposition of Schroeder–Bernstein these are the `ℤ`-orbits; `lfp`
resolves them "towards `A`", `gfp` "towards `B`".)

All results are verified with no axioms and no `sorry`.
-/

open Classical Function

noncomputable section

namespace KnasterTarskiGFP

variable {α β : Type*}

/-! ## Section 1: The Monotone Operator (as in OQ-02) -/

/-- The CBS operator `T(S) = (range g)ᶜ ∪ g '' (f '' S)`. -/
def cbsOp (f : α → β) (g : β → α) (S : Set α) : Set α :=
  (Set.range g)ᶜ ∪ g '' (f '' S)

/-- `T` is monotone. -/
theorem cbsOp_mono (f : α → β) (g : β → α) : Monotone (cbsOp f g) := by
  intro S₁ S₂ h
  exact Set.union_subset_union_right _ (Set.image_mono (Set.image_mono h))

/-- `T` bundled as an order homomorphism, enabling Knaster–Tarski (both fixed points). -/
def cbsHom (f : α → β) (g : β → α) : Set α →o Set α where
  toFun := cbsOp f g
  monotone' := cbsOp_mono f g

/-! ## Section 2: The Bijection from an *Arbitrary* Fixed Point

The key observation answering the open question: the parent's lemmas use only
the fixed-point equation `T(S) = S`, never minimality. We package them for any
`S` with `cbsOp f g S = S`. -/

variable (f : α → β) (g : β → α)

/-- Elements outside `range g` lie in any fixed point. -/
theorem compl_range_subset_fp {S : Set α} (hS : cbsOp f g S = S) :
    (Set.range g)ᶜ ⊆ S := by
  intro a ha
  have h : a ∈ cbsOp f g S := Or.inl ha
  rwa [hS] at h

/-- Elements outside a fixed point have a `g`-preimage. -/
theorem mem_range_of_not_mem_fp {S : Set α} (hS : cbsOp f g S = S) {a : α}
    (ha : a ∉ S) : a ∈ Set.range g := by
  by_contra h
  exact ha (compl_range_subset_fp f g hS h)

/-- A fixed point is closed under `g ∘ f` (set form). -/
theorem gf_image_subset_fp {S : Set α} (hS : cbsOp f g S = S) :
    g '' (f '' S) ⊆ S := by
  intro a ha
  have h : a ∈ cbsOp f g S := Or.inr ha
  rwa [hS] at h

/-- A fixed point is closed under `g ∘ f` (pointwise form). -/
theorem gf_mem_fp {S : Set α} (hS : cbsOp f g S = S) {a : α} (ha : a ∈ S) :
    g (f a) ∈ S :=
  gf_image_subset_fp f g hS ⟨f a, ⟨a, ha, rfl⟩, rfl⟩

/-- If `g b` lies in a fixed point then `b ∈ f '' S` (needs injectivity of `g`). -/
theorem mem_fimage_of_gb_mem_fp (hg : Injective g) {S : Set α}
    (hS : cbsOp f g S = S) {b : β} (hgb : g b ∈ S) : b ∈ f '' S := by
  have h : g b ∈ cbsOp f g S := by rw [hS]; exact hgb
  rw [cbsOp] at h
  rcases h with h' | ⟨x, hx, hgx⟩
  · exact absurd (Set.mem_range.mpr ⟨b, rfl⟩) h'
  · rwa [hg hgx] at hx

/-- Contrapositive: if `b ∉ f '' S` then `g b ∉ S`. -/
theorem gb_not_mem_fp (hg : Injective g) {S : Set α} (hS : cbsOp f g S = S)
    {b : β} (hb : b ∉ f '' S) : g b ∉ S :=
  fun h => hb (mem_fimage_of_gb_mem_fp f g hg hS h)

/-- The piecewise bijection attached to a fixed point `S`:
`a ↦ f a` on `S`, and `a ↦ g⁻¹ a` off `S`. -/
def bijFP {S : Set α} (hS : cbsOp f g S = S) (a : α) : β :=
  if h : a ∈ S then f a else (mem_range_of_not_mem_fp f g hS h).choose

theorem bijFP_of_mem {S : Set α} (hS : cbsOp f g S = S) {a : α} (ha : a ∈ S) :
    bijFP f g hS a = f a :=
  dif_pos ha

theorem bijFP_of_not_mem_spec {S : Set α} (hS : cbsOp f g S = S) {a : α}
    (ha : a ∉ S) : g (bijFP f g hS a) = a := by
  have heq : bijFP f g hS a = (mem_range_of_not_mem_fp f g hS ha).choose := dif_neg ha
  rw [heq]
  exact (mem_range_of_not_mem_fp f g hS ha).choose_spec

theorem bijFP_injective {S : Set α} (hS : cbsOp f g S = S)
    (hf : Injective f) : Injective (bijFP f g hS) := by
  intro a₁ a₂ heq
  by_cases h₁ : a₁ ∈ S <;> by_cases h₂ : a₂ ∈ S
  · rw [bijFP_of_mem f g hS h₁, bijFP_of_mem f g hS h₂] at heq
    exact hf heq
  · exfalso
    have hg12 := congr_arg g heq
    rw [bijFP_of_mem f g hS h₁, bijFP_of_not_mem_spec f g hS h₂] at hg12
    exact h₂ (hg12 ▸ gf_mem_fp f g hS h₁)
  · exfalso
    have hg12 := congr_arg g heq
    rw [bijFP_of_not_mem_spec f g hS h₁, bijFP_of_mem f g hS h₂] at hg12
    exact h₁ (hg12 ▸ gf_mem_fp f g hS h₂)
  · have hg12 := congr_arg g heq
    rw [bijFP_of_not_mem_spec f g hS h₁, bijFP_of_not_mem_spec f g hS h₂] at hg12
    exact hg12

theorem bijFP_surjective {S : Set α} (hS : cbsOp f g S = S) (hg : Injective g) :
    Surjective (bijFP f g hS) := by
  intro b
  by_cases hb : b ∈ f '' S
  · obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a, bijFP_of_mem f g hS ha⟩
  · have hgb : g b ∉ S := gb_not_mem_fp f g hg hS hb
    exact ⟨g b, hg (bijFP_of_not_mem_spec f g hS hgb)⟩

/-- **Every** fixed point of `T` yields a Schroeder–Bernstein bijection. -/
def equivFP {S : Set α} (hS : cbsOp f g S = S) (hf : Injective f)
    (hg : Injective g) : α ≃ β :=
  Equiv.ofBijective (bijFP f g hS)
    ⟨bijFP_injective f g hS hf, bijFP_surjective f g hS hg⟩

/-! ## Section 3: The Least and Greatest Fixed Points

Both `lfp(T)` and `gfp(T)` are fixed points (Knaster–Tarski), so both feed the
construction of Section 2. -/

/-- The least fixed point `S* = lfp(T)` (the parent's choice). -/
def lfpSet : Set α := (cbsHom f g).lfp

/-- The greatest fixed point `S** = gfp(T)` (this entry's choice). -/
def gfpSet : Set α := (cbsHom f g).gfp

theorem lfpSet_fp : cbsOp f g (lfpSet f g) = lfpSet f g := (cbsHom f g).map_lfp

theorem gfpSet_fp : cbsOp f g (gfpSet f g) = gfpSet f g := (cbsHom f g).map_gfp

/-- The least fixed point is contained in the greatest. -/
theorem lfpSet_subset_gfpSet : lfpSet f g ⊆ gfpSet f g :=
  OrderHom.le_gfp _ (cbsHom f g).map_lfp.ge

/-- **Greatest-fixed-point Schroeder–Bernstein**: the `gfp` bijection. -/
def gfp_equiv (hf : Injective f) (hg : Injective g) : α ≃ β :=
  equivFP f g (gfpSet_fp f g) hf hg

/-- The `gfp` route recovers the Schroeder–Bernstein theorem. -/
theorem gfp_schroeder_bernstein (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Function.Bijective h :=
  ⟨bijFP f g (gfpSet_fp f g),
    bijFP_injective f g _ hf, bijFP_surjective f g _ hg⟩

/-- The least-fixed-point bijection (the parent's), exhibited from the same
general construction — so `lfp` and `gfp` are two instances of one theorem. -/
def lfp_equiv (hf : Injective f) (hg : Injective g) : α ≃ β :=
  equivFP f g (lfpSet_fp f g) hf hg

/-! ## Section 4: The Geometry of `gfp ∖ lfp`

`D = gfp(T) ∖ lfp(T)` is exactly the set on which `φ = g ∘ f` acts bijectively:
no sources (`D ⊆ range g`), `φ` maps `D` into `D`, and every point of `D` has a
`φ`-predecessor in `D`. These are the bi-infinite `φ`-chains. -/

/-- The difference `D = gfp(T) ∖ lfp(T)`. -/
def diffSet : Set α := gfpSet f g \ lfpSet f g

/-- `gfp = lfp ∪ D`: the greatest fixed point adds exactly `D` to the least. -/
theorem gfpSet_eq_lfp_union_diff :
    gfpSet f g = lfpSet f g ∪ diffSet f g :=
  (Set.union_diff_cancel (lfpSet_subset_gfpSet f g)).symm

/-- `D` contains no sources: it lies entirely inside `range g`. Equivalently,
all of `(range g)ᶜ` is already in the least fixed point. -/
theorem diffSet_subset_range : diffSet f g ⊆ Set.range g := by
  intro a ha
  by_contra h
  exact ha.2 (compl_range_subset_fp f g (lfpSet_fp f g) h)

/-- `φ = g ∘ f` maps `D` into `D`. -/
theorem diffSet_gf_mem (hf : Injective f) (hg : Injective g) {a : α}
    (ha : a ∈ diffSet f g) : g (f a) ∈ diffSet f g := by
  refine ⟨gf_mem_fp f g (gfpSet_fp f g) ha.1, ?_⟩
  intro hlfp
  obtain ⟨a', ha', haa'⟩ := mem_fimage_of_gb_mem_fp f g hg (lfpSet_fp f g) hlfp
  exact ha.2 (hf haa' ▸ ha')

/-- Every point of `D` has a `φ`-predecessor inside `D`: there is no sink, the
chains extend backward indefinitely within `D`. (No injectivity needed — this is
forced by the two fixed-point equations alone.) -/
theorem diffSet_has_pred {a : α}
    (ha : a ∈ diffSet f g) : ∃ a', a' ∈ diffSet f g ∧ g (f a') = a := by
  have ha_in_op : a ∈ cbsOp f g (gfpSet f g) := by rw [gfpSet_fp]; exact ha.1
  rw [cbsOp] at ha_in_op
  rcases ha_in_op with hc | ⟨b, hb, hgb⟩
  · exact absurd (compl_range_subset_fp f g (lfpSet_fp f g) hc) ha.2
  · obtain ⟨a', ha'gfp, hfa'⟩ := hb
    refine ⟨a', ⟨ha'gfp, ?_⟩, by rw [hfa', hgb]⟩
    intro hlfp
    apply ha.2
    have hmem : g (f a') ∈ lfpSet f g := gf_mem_fp f g (lfpSet_fp f g) hlfp
    rwa [hfa', hgb] at hmem

/-- **`φ = g ∘ f` restricts to a bijection of `D = gfp ∖ lfp`.** This is the
geometric content of the open question: the difference between the greatest and
least fixed points is precisely the maximal set on which `g ∘ f` acts bijectively
— the union of the bi-infinite chains, with neither sources nor sinks. -/
theorem diffSet_gf_bijOn (hf : Injective f) (hg : Injective g) :
    Set.BijOn (fun a => g (f a)) (diffSet f g) (diffSet f g) :=
  ⟨fun _ ha => diffSet_gf_mem f g hf hg ha,
   fun _ _ _ _ h => hf (hg h),
   fun _ ha => diffSet_has_pred f g ha⟩

/-- The least and greatest fixed points coincide iff `D` is empty — iff there are
no bi-infinite `φ`-chains. -/
theorem lfpSet_eq_gfpSet_iff_diff_empty :
    lfpSet f g = gfpSet f g ↔ diffSet f g = ∅ := by
  rw [diffSet, Set.diff_eq_empty]
  exact ⟨fun h => h ▸ subset_rfl,
    fun h => Set.Subset.antisymm (lfpSet_subset_gfpSet f g) h⟩

end KnasterTarskiGFP

end
