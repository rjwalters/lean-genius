/-
  Mirsky's height function is a strict order morphism — the longest chain is a
  transversal of the minimum antichain cover.
  (dilworth-theorem-oq-01-oq-01-oq-03)

  ## Background

  The companion file `Proofs.DilworthMirskyHardOQ01` proves Mirsky's theorem on a
  finite poset by the *height/level decomposition*.  For each element it defines

      `height x = max { |C| : C a chain whose maximum element is x }`,

  shows `1 ≤ height x ≤ maxChainLen`, and that each **level set**
  `level k = { x : height x = k }` is an antichain, so the `maxChainLen` nonempty
  levels form a minimum antichain cover (`mirsky_min_antichain_cover`).

  The crucial inequality buried inside `level_isAntichain` is that appending a
  strictly-larger element to a longest chain *increases* the height.  That fact
  deserves to be stated in its own right, and it has structural consequences the
  parent never extracted.

  ## What this file proves

  1. **`height_strictMono`** : `height : α → ℕ` is strictly monotone,
     `x < y → height x < height y`.  Thus `height` is an order-strict morphism
     of the poset into the chain `ℕ` — a *rank function* whose existence is
     exactly the content of Mirsky's level decomposition, now phrased as a map
     rather than a family of antichains.

  2. **`height_injOn_chain`** : `height` is injective on every chain (immediate
     from strict monotonicity plus comparability).

  3. **`maxChain_image_height`** : along a *maximum* chain `C`
     (`C.card = maxChainLen`) the height function is a bijection onto the whole
     segment `{1, …, maxChainLen}`; consequently
     **`height_image_univ_eq`**: every value in `{1, …, maxChainLen}` is realised
     as the height of some element (`height` is onto its segment).

  4. **`maxChain_inter_level`** (capstone) : a maximum chain meets every Mirsky
     level antichain in *exactly one* point.  The longest chain is therefore a
     **transversal** of the minimum antichain cover: chain and cover interleave
     so that the two extremal quantities of Mirsky's theorem are realised by a
     single saturated decomposition.  This is a genuine sharpening of
     `mirsky_min_antichain_cover`, which only equates the two *cardinalities*.

  Everything is derived from the parent's API with no new axioms.

  ## Status: BUILD-TARGET.  0 axioms, 0 sorries.
-/
import Proofs.DilworthMirskyHardOQ01

open Classical

attribute [local instance] Classical.propDecidable

namespace DilworthTheoremOQ01

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- **Strict monotonicity of height (pointwise).**  If `x < y` then a longest
    chain ending at `x` extends by `y` to a strictly longer chain ending at `y`,
    so `height x < height y`.  This is the inequality that powers
    `level_isAntichain`, now isolated. -/
theorem height_lt_of_lt {x y : α} (hxy : x < y) :
    height x < height y := by
  obtain ⟨C, hC, hCcard⟩ := exists_chainsTo_card_eq_height x
  rw [mem_chainsTo] at hC
  obtain ⟨hChain, _hxmem, hCle⟩ := hC
  have hyC : y ∉ C := fun hyC' => absurd (hCle y hyC') hxy.not_ge
  have hC' : insert y C ∈ chainsTo y := by
    rw [mem_chainsTo]
    refine ⟨?_, Finset.mem_insert_self y C, ?_⟩
    · intro a ha b hb
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | haC
      · rcases hb with rfl | hbC
        · exact Or.inl le_rfl
        · exact Or.inr ((hCle b hbC).trans hxy.le)
      · rcases hb with rfl | hbC
        · exact Or.inl ((hCle a haC).trans hxy.le)
        · exact hChain haC hbC
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hzC
      · exact le_rfl
      · exact (hCle z hzC).trans hxy.le
  have hge : (insert y C).card ≤ height y := Finset.le_sup hC'
  rw [Finset.card_insert_of_notMem hyC, hCcard] at hge
  omega

/-- **`height` is a strict order morphism** of the poset into `ℕ`.  Equivalently,
    Mirsky's level decomposition is a genuine rank function. -/
theorem height_strictMono : StrictMono (height : α → ℕ) :=
  fun _ _ h => height_lt_of_lt h

/-- **Height is injective on chains.**  Two comparable elements with equal height
    are equal, so on any chain `height` separates points. -/
theorem height_injOn_chain {C : Finset α} (hC : IsChainOn C) :
    ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → height x = height y → x = y := by
  intro x hx y hy hh
  rcases hC hx hy with hxy | hyx
  · rcases lt_or_eq_of_le hxy with hlt | heq
    · exact absurd hh (height_lt_of_lt hlt).ne
    · exact heq
  · rcases lt_or_eq_of_le hyx with hlt | heq
    · exact absurd hh.symm (height_lt_of_lt hlt).ne
    · exact heq.symm

/-- The `Set.InjOn` repackaging, for use with `Finset.card_image_of_injOn`. -/
theorem height_setInjOn_chain {C : Finset α} (hC : IsChainOn C) :
    Set.InjOn height (C : Set α) :=
  fun _ hx _ hy hh =>
    height_injOn_chain hC (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) hh

/-- On a chain the image of `height` has the same cardinality as the chain. -/
theorem chain_image_height_card {C : Finset α} (hC : IsChainOn C) :
    (C.image height).card = C.card :=
  Finset.card_image_of_injOn (height_setInjOn_chain hC)

/-- **Along a maximum chain, `height` bijects onto the whole segment.**  A chain of
    size `maxChainLen` realises every height value `1, …, maxChainLen` exactly
    once. -/
theorem maxChain_image_height {C : Finset α} (hC : IsChainOn C)
    (hcard : C.card = maxChainLen (α := α)) :
    C.image height = Finset.Icc 1 (maxChainLen (α := α)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨x, _, rfl⟩ := hk
    rw [Finset.mem_Icc]
    exact ⟨one_le_height x, height_le_maxChainLen x⟩
  · rw [Nat.card_Icc, chain_image_height_card hC, hcard]
    omega

/-- **Surjectivity of height onto its segment.**  Every value in
    `{1, …, maxChainLen}` is the height of some element of the poset. -/
theorem height_image_univ_eq :
    (Finset.univ : Finset α).image height
      = Finset.Icc 1 (maxChainLen (α := α)) := by
  apply Finset.Subset.antisymm
  · intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨x, _, rfl⟩ := hk
    rw [Finset.mem_Icc]
    exact ⟨one_le_height x, height_le_maxChainLen x⟩
  · obtain ⟨C, hC, hCcard⟩ := exists_chain_card_eq_maxChainLen (α := α)
    rw [← maxChain_image_height hC hCcard]
    exact Finset.image_subset_image (Finset.subset_univ C)

/-- A maximum chain has exactly one element at each height in its segment. -/
theorem maxChain_height_fiber_card {C : Finset α} (hC : IsChainOn C)
    (hcard : C.card = maxChainLen (α := α)) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (maxChainLen (α := α))) :
    (C.filter (fun x => height x = k)).card = 1 := by
  apply le_antisymm
  · rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact height_injOn_chain hC ha.1 hb.1 (ha.2.trans hb.2.symm)
  · rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro hempty
    rw [← maxChain_image_height hC hcard, Finset.mem_image] at hk
    obtain ⟨x, hxC, hxk⟩ := hk
    have hxmem : x ∈ C.filter (fun x => height x = k) :=
      Finset.mem_filter.mpr ⟨hxC, hxk⟩
    rw [hempty] at hxmem
    exact absurd hxmem (Finset.notMem_empty x)

/-- **Capstone — the longest chain is a transversal of the Mirsky cover.**  A
    maximum chain meets every level antichain `level k` (for `k` in the segment
    `{1, …, maxChainLen}`) in exactly one point.  Chain and minimum antichain
    cover therefore interleave into a single saturated decomposition, sharpening
    `mirsky_min_antichain_cover` from an equality of cardinalities to an explicit
    one-to-one interleaving. -/
theorem maxChain_inter_level {C : Finset α} (hC : IsChainOn C)
    (hcard : C.card = maxChainLen (α := α)) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (maxChainLen (α := α))) :
    (C ∩ level k).card = 1 := by
  have heq : C ∩ level k = C.filter (fun x => height x = k) := by
    ext z
    simp only [Finset.mem_inter, mem_level, Finset.mem_filter]
  rw [heq]
  exact maxChain_height_fiber_card hC hcard hk

end DilworthTheoremOQ01
