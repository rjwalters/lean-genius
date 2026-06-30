/-
  Dilworth's Theorem — elementary (pigeonhole) directions of the
  chain / antichain duality.  (dilworth-theorem-oq-01)

  ## Background

  In a partially ordered set, a *chain* is a set of pairwise comparable
  elements and an *antichain* a set of pairwise incomparable elements.
  Two classical duality theorems describe how chains and antichains trade
  off against one another on a finite poset:

  * **Dilworth's theorem** (1950): the minimum number of chains needed to
    cover the poset equals the maximum size of an antichain.
  * **Mirsky's theorem** (1971): the minimum number of antichains needed to
    cover the poset equals the maximum size of a chain.

  Each theorem has an *easy* and a *hard* direction.  The easy direction is a
  one-line pigeonhole argument; the hard direction (that the bound is actually
  attained) is the deep combinatorial content.

  ## What this file proves

  We formalize the **easy directions** of both theorems, which both rest on a
  single elementary fact:

      `chain_antichain_inter_subsingleton` :
          a chain `C` and an antichain `A` share at most one element.

  From this we obtain, by pigeonhole, the two inequalities:

  * `antichain_card_le_of_chainCover` — every antichain is no larger than any
    family of chains covering it.  This is the `≤` direction of Dilworth.
  * `chain_card_le_of_antichainCover` — every chain is no larger than any family
    of antichains covering it.  This is the `≤` direction of Mirsky.

  Both are fully machine-checked over an arbitrary `PartialOrder` with no
  finiteness assumption beyond the `Finset`s involved, hence **0 sorries,
  0 axioms**.  The hard directions (equality / attainment) are the classical
  deep content and are *not* claimed here.

  ## Status: BUILD-TARGET.  0 axioms, 0 sorries.
-/
import Mathlib

namespace DilworthTheoremOQ01

variable {α : Type*} [PartialOrder α]

/-- A `Finset` is a **chain** when its elements are pairwise comparable. -/
def IsChainOn (C : Finset α) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≤ y ∨ y ≤ x

/-- A `Finset` is an **antichain** when comparable members are equal, i.e.
    distinct members are incomparable. -/
def IsAntichainOn (A : Finset α) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x ≤ y → x = y

/-- **Fundamental lemma.**  A chain and an antichain meet in at most one point:
    any two common elements are comparable (chain) hence equal (antichain). -/
theorem chain_antichain_inter_subsingleton
    {C A : Finset α} (hC : IsChainOn C) (hA : IsAntichainOn A)
    {x y : α} (hxC : x ∈ C) (hxA : x ∈ A) (hyC : y ∈ C) (hyA : y ∈ A) :
    x = y := by
  rcases hC hxC hyC with hxy | hyx
  · exact hA hxA hyA hxy
  · exact (hA hyA hxA hyx).symm

/-- **Dilworth, easy direction.**  If every element of an antichain `A` lies in
    some chain of the family `𝒞`, then `A` is no larger than `𝒞`: you need at
    least `|A|` chains to cover an antichain of size `|A|`. -/
theorem antichain_card_le_of_chainCover
    {A : Finset α} (hA : IsAntichainOn A)
    {𝒞 : Finset (Finset α)} (hchains : ∀ C ∈ 𝒞, IsChainOn C)
    (hcover : ∀ a ∈ A, ∃ C ∈ 𝒞, a ∈ C) :
    A.card ≤ 𝒞.card := by
  classical
  -- Pick, for each `a`, a chain of `𝒞` containing it (default `∅` otherwise).
  let f : α → Finset α := fun a => if h : ∃ C ∈ 𝒞, a ∈ C then h.choose else ∅
  have hchar : ∀ a ∈ A, f a ∈ 𝒞 ∧ a ∈ f a := by
    intro a ha
    have h : ∃ C ∈ 𝒞, a ∈ C := hcover a ha
    have hfa : f a = h.choose := by
      show (if h' : ∃ C ∈ 𝒞, a ∈ C then h'.choose else ∅) = h.choose
      exact dif_pos h
    rw [hfa]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  have hmem : ∀ a ∈ A, f a ∈ 𝒞 := fun a ha => (hchar a ha).1
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmem
  -- `x`, `y` both lie in the common chain `f x = f y`, and both in `A`.
  have hxfx : x ∈ f x := (hchar x hx).2
  have hyfx : y ∈ f x := hfxy ▸ (hchar y hy).2
  have hCchain : IsChainOn (f x) := hchains _ (hmem x hx)
  exact hxy (chain_antichain_inter_subsingleton hCchain hA hxfx hx hyfx hy)

/-- **Mirsky, easy direction.**  If every element of a chain `C` lies in some
    antichain of the family `𝒜`, then `C` is no larger than `𝒜`: you need at
    least `|C|` antichains to cover a chain of size `|C|`. -/
theorem chain_card_le_of_antichainCover
    {C : Finset α} (hC : IsChainOn C)
    {𝒜 : Finset (Finset α)} (hanti : ∀ A ∈ 𝒜, IsAntichainOn A)
    (hcover : ∀ c ∈ C, ∃ A ∈ 𝒜, c ∈ A) :
    C.card ≤ 𝒜.card := by
  classical
  let f : α → Finset α := fun c => if h : ∃ A ∈ 𝒜, c ∈ A then h.choose else ∅
  have hchar : ∀ c ∈ C, f c ∈ 𝒜 ∧ c ∈ f c := by
    intro c hc
    have h : ∃ A ∈ 𝒜, c ∈ A := hcover c hc
    have hfc : f c = h.choose := by
      show (if h' : ∃ A ∈ 𝒜, c ∈ A then h'.choose else ∅) = h.choose
      exact dif_pos h
    rw [hfc]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  have hmem : ∀ c ∈ C, f c ∈ 𝒜 := fun c hc => (hchar c hc).1
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmem
  have hxfx : x ∈ f x := (hchar x hx).2
  have hyfx : y ∈ f x := hfxy ▸ (hchar y hy).2
  have hAanti : IsAntichainOn (f x) := hanti _ (hmem x hx)
  -- Same fundamental lemma, roles of chain and antichain swapped.
  exact hxy (chain_antichain_inter_subsingleton hC hAanti hx hxfx hy hyfx)

end DilworthTheoremOQ01
