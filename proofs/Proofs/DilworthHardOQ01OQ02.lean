/-
  Dilworth's Theorem — structural core of the HARD direction, for a finite poset.
  (dilworth-theorem-oq-01-oq-02)

  ## Background

  The companion file `Proofs.DilworthTheoremOQ01` proves the *easy* directions of
  the Dilworth / Mirsky dualities, resting on the fact that a chain and an
  antichain meet in at most one point.  Its Dilworth half is

      `antichain_card_le_of_chainCover` :
          every antichain is no larger than any chain family covering it,

  i.e. `width ≤ (min chain cover)`.  Its sibling `Proofs.DilworthMirskyHardOQ01`
  supplies the hard direction of **Mirsky's** theorem (via a height/level
  decomposition).  The hard direction of **Dilworth's** theorem — that a chain
  cover whose size equals the maximum antichain width actually *exists* — is the
  genuinely deep combinatorial content and is **not** available in Mathlib.

  ## What this file proves

  The Galvin/Perles proof of Dilworth's theorem is organised around the
  **down-set / up-set decomposition of a maximum antichain** `A` of the ground
  set `s`:

      `downSet A s = {x ∈ s | x ≤ y for some y ∈ A}`,
      `upSet   A s = {x ∈ s | y ≤ x for some y ∈ A}`.

  This file proves, fully and unconditionally, the geometric heart of that
  argument:

  * `downSet_inter_upSet` — the two sets meet exactly in `A`.
  * `downSet_union_upSet` — for a **maximum** antichain they cover all of `s`
    (an element missed by both would enlarge `A`).
  * `le_of_mem_chain_downSet` / `ge_of_mem_chain_upSet` — a chain inside the
    down-set (resp. up-set) that contains `a' ∈ A` lies entirely below (resp.
    above) `a'`.
  * `glue_isChain` — consequently a down-set chain through `a'` and an up-set
    chain through the same `a'` glue into a single chain.  This is the gluing
    step that assembles the inductive sub-covers of `downSet` and `upSet` into a
    chain cover of `s`.

  The full theorem `dilworth_chainCover` (strong form: an antichain bound `w`
  yields a chain cover of size `≤ w`) is stated; its proof is the Galvin
  induction on `|s|`, whose remaining work is the bookkeeping that the sub-covers
  of `downSet`/`upSet` each meet `A` exactly once together with the degenerate
  case `downSet = A`.  It is left as `sorry` here (a known-hard formalization;
  see Singh–Natarajan's Coq mechanization, arXiv:1703.06133).

  ## Status: in progress — structural core verified (0 sorries in the lemmas),
  main theorem `sorry`.
-/
import Mathlib
import Proofs.DilworthTheoremOQ01

open DilworthTheoremOQ01

namespace DilworthHardOQ01OQ02

variable {α : Type*} [PartialOrder α]

section Decomposition

variable [DecidableLE α]

/-- The **down-set** of an antichain `A` inside the ground set `s`:
    all elements of `s` that lie below some element of `A`. -/
def downSet (A s : Finset α) : Finset α :=
  s.filter (fun x => ∃ y ∈ A, x ≤ y)

/-- The **up-set** of an antichain `A` inside the ground set `s`:
    all elements of `s` that lie above some element of `A`. -/
def upSet (A s : Finset α) : Finset α :=
  s.filter (fun x => ∃ y ∈ A, y ≤ x)

@[simp] theorem mem_downSet {A s : Finset α} {x : α} :
    x ∈ downSet A s ↔ x ∈ s ∧ ∃ y ∈ A, x ≤ y := by
  simp [downSet]

@[simp] theorem mem_upSet {A s : Finset α} {x : α} :
    x ∈ upSet A s ↔ x ∈ s ∧ ∃ y ∈ A, y ≤ x := by
  simp [upSet]

theorem downSet_subset (A s : Finset α) : downSet A s ⊆ s := by
  intro x hx; exact (mem_downSet.mp hx).1

theorem upSet_subset (A s : Finset α) : upSet A s ⊆ s := by
  intro x hx; exact (mem_upSet.mp hx).1

theorem subset_downSet {A s : Finset α} (hAs : A ⊆ s) : A ⊆ downSet A s := by
  intro y hy
  exact mem_downSet.mpr ⟨hAs hy, y, hy, le_refl y⟩

theorem subset_upSet {A s : Finset α} (hAs : A ⊆ s) : A ⊆ upSet A s := by
  intro y hy
  exact mem_upSet.mpr ⟨hAs hy, y, hy, le_refl y⟩

/-- In a chain `C ⊆ downSet A s` that contains an element `a' ∈ A`, *every*
    element lies below `a'`: comparability with `a'` plus the antichain property
    forces the down-set witness to coincide with `a'`. -/
theorem le_of_mem_chain_downSet {A s C : Finset α} (hA : IsAntichainOn A)
    (hC : IsChainOn C) (hCD : C ⊆ downSet A s) {a' : α} (ha' : a' ∈ A)
    (ha'C : a' ∈ C) {x : α} (hxC : x ∈ C) : x ≤ a' := by
  rcases hC hxC ha'C with hxa | hax
  · exact hxa
  · obtain ⟨y, hy, hxy⟩ := (mem_downSet.mp (hCD hxC)).2
    have hay : a' = y := hA ha' hy (le_trans hax hxy)
    exact le_of_eq (le_antisymm (hay ▸ hxy) hax)

/-- Dual of `le_of_mem_chain_downSet` for the up-set: a chain `C ⊆ upSet A s`
    containing `a' ∈ A` lies entirely above `a'`. -/
theorem ge_of_mem_chain_upSet {A s C : Finset α} (hA : IsAntichainOn A)
    (hC : IsChainOn C) (hCU : C ⊆ upSet A s) {a' : α} (ha' : a' ∈ A)
    (ha'C : a' ∈ C) {x : α} (hxC : x ∈ C) : a' ≤ x := by
  rcases hC ha'C hxC with ha'x | hxa'
  · exact ha'x
  · obtain ⟨y, hy, hyx⟩ := (mem_upSet.mp (hCU hxC)).2
    have hya : y = a' := hA hy ha' (le_trans hyx hxa')
    exact ge_of_eq (le_antisymm hxa' (hya ▸ hyx))

variable [DecidableEq α]

/-- The down-set and up-set of an antichain meet exactly in the antichain. -/
theorem downSet_inter_upSet {A s : Finset α} (hA : IsAntichainOn A) (hAs : A ⊆ s) :
    downSet A s ∩ upSet A s = A := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨y₁, hy₁, hxy₁⟩ := (mem_downSet.mp hx.1).2
    obtain ⟨y₂, hy₂, hy₂x⟩ := (mem_upSet.mp hx.2).2
    -- y₂ ≤ x ≤ y₁, so y₂ ≤ y₁; antichain ⟹ y₂ = y₁ and x = y₁ ∈ A.
    have heq : y₂ = y₁ := hA hy₂ hy₁ (le_trans hy₂x hxy₁)
    have : x = y₁ := le_antisymm hxy₁ (heq ▸ hy₂x)
    exact this ▸ hy₁
  · intro x hx
    exact Finset.mem_inter.mpr ⟨subset_downSet hAs hx, subset_upSet hAs hx⟩

/-- For a **maximum** antichain `A` (no antichain in `s` is larger), the down-set
    and up-set together cover all of `s`: any element missed by both could be
    added to `A` to form a strictly larger antichain. -/
theorem downSet_union_upSet {A s : Finset α} (hA : IsAntichainOn A) (hAs : A ⊆ s)
    (hmax : ∀ B ⊆ s, IsAntichainOn B → B.card ≤ A.card) :
    downSet A s ∪ upSet A s = s := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact downSet_subset A s h
    · exact upSet_subset A s h
  · intro x hxs
    by_contra hx
    rw [Finset.mem_union] at hx
    push_neg at hx
    obtain ⟨hxD, hxU⟩ := hx
    -- x is incomparable to every element of A.
    have hnotle : ∀ y ∈ A, ¬ x ≤ y := by
      intro y hy hxy; exact hxD (mem_downSet.mpr ⟨hxs, y, hy, hxy⟩)
    have hnotge : ∀ y ∈ A, ¬ y ≤ x := by
      intro y hy hyx; exact hxU (mem_upSet.mpr ⟨hxs, y, hy, hyx⟩)
    have hxnotin : x ∉ A := fun hxA => hnotle x hxA (le_refl x)
    -- A ∪ {x} is an antichain of card |A|+1, contradicting maximality.
    have hBanti : IsAntichainOn (insert x A) := by
      intro p hp q hq hpq
      rw [Finset.mem_insert] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · subst hp; subst hq; rfl
      · subst hp; exact absurd hpq (hnotle q hq)
      · subst hq; exact absurd hpq (hnotge p hp)
      · exact hA hp hq hpq
    have hBs : insert x A ⊆ s := Finset.insert_subset hxs hAs
    have hcard : (insert x A).card = A.card + 1 :=
      Finset.card_insert_of_notMem hxnotin
    have := hmax _ hBs hBanti
    rw [hcard] at this
    omega

/-- **Gluing step.**  A chain `C` inside the down-set and a chain `C'` inside the
    up-set, both passing through the same `a' ∈ A`, glue into a single chain
    `C ∪ C'`: every member of `C` is `≤ a'` and every member of `C'` is `≥ a'`,
    so any cross-pair is comparable through `a'`. -/
theorem glue_isChain {A s C C' : Finset α} (hA : IsAntichainOn A)
    (hC : IsChainOn C) (hCD : C ⊆ downSet A s)
    (hC' : IsChainOn C') (hC'U : C' ⊆ upSet A s)
    {a' : α} (ha' : a' ∈ A) (ha'C : a' ∈ C) (ha'C' : a' ∈ C') :
    IsChainOn (C ∪ C') := by
  intro x hx y hy
  rw [Finset.mem_union] at hx hy
  rcases hx with hxC | hxC' <;> rcases hy with hyC | hyC'
  · exact hC hxC hyC
  · exact Or.inl (le_trans (le_of_mem_chain_downSet hA hC hCD ha' ha'C hxC)
                           (ge_of_mem_chain_upSet hA hC' hC'U ha' ha'C' hyC'))
  · exact Or.inr (le_trans (le_of_mem_chain_downSet hA hC hCD ha' ha'C hyC)
                           (ge_of_mem_chain_upSet hA hC' hC'U ha' ha'C' hxC'))
  · exact hC' hxC' hyC'

end Decomposition

/-- **Dilworth's theorem, hard direction (strong form).**
    If every antichain contained in the ground `Finset` `s` has at most `w`
    elements, then `s` is covered by at most `w` chains, each a subset of `s`.

    Combined with `DilworthTheoremOQ01.antichain_card_le_of_chainCover` (the easy
    direction), taking `w` to be the maximum antichain size gives the classical
    equality `min chain cover = max antichain`.

    The proof is the Galvin/Perles induction on `s.card`, assembled from the
    verified structural lemmas above; the remaining bookkeeping (each sub-cover
    meets the maximum antichain exactly once, plus the degenerate case
    `downSet A s = A`) is left open here. -/
theorem dilworth_chainCover
    [DecidableEq α] [DecidableLE α] (s : Finset α) (w : ℕ)
    (hw : ∀ A ⊆ s, IsAntichainOn A → A.card ≤ w) :
    ∃ 𝒞 : Finset (Finset α),
      (∀ C ∈ 𝒞, IsChainOn C ∧ C ⊆ s) ∧
      (∀ x ∈ s, ∃ C ∈ 𝒞, x ∈ C) ∧
      𝒞.card ≤ w := by
  sorry

end DilworthHardOQ01OQ02
