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

  Beyond the structural core, this file now proves the full theorem:

  * `chain_meets_antichain_of_card_le` — the **saturation pigeonhole**: if a chain
    family of size `≤ |A|` covers an antichain `A`, then *every* chain meets `A`
    (necessarily once).  This bridges the easy bound to the gluing step.
  * `dilworth_chainPartition` — Dilworth's hard direction in **partition** form:
    if every antichain of `s` has `≤ w` elements then `s` admits a chain
    *partition* into `≤ w` parts.  Proved by strong induction on `s` (strict
    subset).  A maximum antichain is either *non-extreme* — its `downSet`/`upSet`
    are proper, so the inductive partitions of each are indexed by `A` (via
    saturation) and welded by `glue_isChain` — or *extreme*, in which case every
    maximum antichain is the minimal- or maximal-element set; deleting a minimal-
    to-maximal chain `{x, y}` drops the width and induction reinserts `{x, y}`.
  * `dilworth_chainCover` — the headline cover form, immediate from the partition.

  Combined with `DilworthTheoremOQ01.antichain_card_le_of_chainCover` (the easy
  direction), taking `w` to be the maximum antichain width gives the classical
  equality `min chain cover = max antichain`.  This hard direction is **not**
  available in Mathlib (cf. Singh–Natarajan's Coq mechanization, arXiv:1703.06133).

  ## Status: complete.  0 sorries, 0 axioms (only `propext`, `Classical.choice`,
  `Quot.sound`); original.
-/
import Mathlib
import Proofs.DilworthTheoremOQ01

open DilworthTheoremOQ01

namespace DilworthHardOQ01OQ02

variable {α : Type*} [PartialOrder α]

/-- A **chain partition** of `s`: a family `𝒞` of chains, each a subset of `s`,
    that *covers* `s` and is *disjoint* (every element of `s` lies in a unique
    member).  The disjointness clause is what the Dilworth induction needs: it
    lets the gluing step match each chain to the unique element of the maximum
    antichain it contains. -/
def IsChainPartition (𝒞 : Finset (Finset α)) (s : Finset α) : Prop :=
  (∀ C ∈ 𝒞, IsChainOn C) ∧ (∀ C ∈ 𝒞, C ⊆ s) ∧
  (∀ x ∈ s, ∃ C ∈ 𝒞, x ∈ C) ∧
  (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∀ x, x ∈ C → x ∈ C' → C = C')

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

omit [DecidableLE α] in
/-- **Saturation pigeonhole.**  If a family of chains `𝒞` covers an antichain `A`
    (each `a ∈ A` lies in some chain) and `𝒞` has at most `|A|` members, then the
    cover is *tight*: every chain of `𝒞` contains an element of `A` (necessarily
    exactly one, by `chain_antichain_inter_subsingleton`).

    This is the bridge from the easy bound to the gluing step: in a *minimum*
    chain cover of a poset, every chain meets every *maximum* antichain.  It is
    what guarantees the inductive sub-covers of `downSet`/`upSet` are indexed by
    `A`, so that `glue_isChain` can match a down-chain to an up-chain through their
    common element of `A`. -/
theorem chain_meets_antichain_of_card_le
    {A : Finset α} (hA : IsAntichainOn A)
    {𝒞 : Finset (Finset α)} (hchains : ∀ C ∈ 𝒞, IsChainOn C)
    (hcover : ∀ a ∈ A, ∃ C ∈ 𝒞, a ∈ C) (hcard : 𝒞.card ≤ A.card) :
    ∀ C ∈ 𝒞, ∃ a ∈ A, a ∈ C := by
  classical
  -- assign to each `a ∈ A` a chain of `𝒞` containing it
  let g : α → Finset α := fun a => if h : ∃ C ∈ 𝒞, a ∈ C then h.choose else ∅
  have hg : ∀ a ∈ A, g a ∈ 𝒞 ∧ a ∈ g a := by
    intro a ha
    have h : ∃ C ∈ 𝒞, a ∈ C := hcover a ha
    have hga : g a = h.choose := dif_pos h
    rw [hga]; exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  -- `g` is injective on `A`: two members landing in the same chain coincide
  have hinj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, g a₁ = g a₂ → a₁ = a₂ := by
    intro a₁ h₁ a₂ h₂ he
    have hmem₁ := hg a₁ h₁
    have hmem₂ := hg a₂ h₂
    have ha₂ : a₂ ∈ g a₁ := he ▸ hmem₂.2
    exact chain_antichain_inter_subsingleton (hchains _ hmem₁.1) hA hmem₁.2 h₁ ha₂ h₂
  -- the image of `A` under `g` therefore has card `|A|` and lies inside `𝒞`
  have hsub : A.image g ⊆ 𝒞 := by
    intro C hC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
    exact (hg a ha).1
  have hcardimg : (A.image g).card = A.card :=
    Finset.card_image_of_injOn (fun a₁ h₁ a₂ h₂ he => hinj a₁ h₁ a₂ h₂ he)
  -- equal cardinalities force `A.image g = 𝒞`, so `g` is onto `𝒞`
  have heq : A.image g = 𝒞 := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcardimg]; exact hcard
  intro C hC
  rw [← heq] at hC
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨a, ha, (hg a ha).2⟩

end Decomposition

/-- **Dilworth's theorem, hard direction — partition form.**
    If every antichain contained in `s` has at most `w` elements, then `s` admits
    a chain *partition* of at most `w` parts.  This is the inductive workhorse;
    the partition (rather than mere cover) is essential so that the gluing step
    can match chains to antichain elements bijectively.

    Proof: strong induction on `s` (by strict subset).  Fix a *maximum* antichain
    `A` of size `m`.  Either some maximum antichain `B` is non-extreme
    (`downSet B s ≠ s` and `upSet B s ≠ s`), or every maximum antichain is the set
    of all maximal / all minimal elements.

    * **Non-extreme (gluing).**  `downSet B s` and `upSet B s` are proper subsets
      covering `s` and meeting in `B`.  Induction partitions each into `≤ m`
      chains; `chain_meets_antichain_of_card_le` shows every part meets `B`, so
      partitions are indexed by `B`, and `glue_isChain` welds the down-part and
      up-part through their shared element of `B`.
    * **Extreme (chain removal).**  Pick a minimal `x ≤ y` maximal and delete the
      chain `{x, y}`.  Every maximum antichain contains `x` or `y` (it is the
      minimal- or maximal-element set), so `s \ {x,y}` has width `≤ m - 1`;
      induction plus reinserting `{x,y}` gives `≤ m` chains. -/
theorem dilworth_chainPartition
    [DecidableEq α] [DecidableLE α] (s : Finset α) :
    ∀ w : ℕ, (∀ A ⊆ s, IsAntichainOn A → A.card ≤ w) →
      ∃ 𝒞 : Finset (Finset α), IsChainPartition 𝒞 s ∧ 𝒞.card ≤ w := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro w hw
    rcases s.eq_empty_or_nonempty with hse | hsne
    · -- empty ground set: the empty partition works
      subst hse
      exact ⟨∅, ⟨by simp, by simp, by simp, by simp⟩, by simp⟩
    -- Build a maximum antichain `A` of `s`.
    set P : Finset (Finset α) := s.powerset.filter (fun B => IsAntichainOn B) with hP
    have hPne : P.Nonempty :=
      ⟨∅, by rw [hP, Finset.mem_filter, Finset.mem_powerset]
             exact ⟨Finset.empty_subset s, by intro x hx; simp at hx⟩⟩
    obtain ⟨A, hAP, hAmax⟩ := P.exists_max_image Finset.card hPne
    rw [hP, Finset.mem_filter, Finset.mem_powerset] at hAP
    obtain ⟨hAs, hAanti⟩ := hAP
    set m := A.card with hm
    have hmax : ∀ B ⊆ s, IsAntichainOn B → B.card ≤ m := fun B hBs hBanti =>
      hAmax B (by rw [hP, Finset.mem_filter, Finset.mem_powerset]; exact ⟨hBs, hBanti⟩)
    have hmw : m ≤ w := hw A hAs hAanti
    obtain ⟨z₀, hz₀⟩ := hsne
    have hm1 : 1 ≤ m := by
      have h1 : ({z₀} : Finset α).card ≤ m :=
        hmax {z₀} (by simpa using hz₀) (by intro a ha b hb _; simp_all)
      simpa using h1
    by_cases hnd : ∃ B, B ⊆ s ∧ IsAntichainOn B ∧ B.card = m ∧
        downSet B s ≠ s ∧ upSet B s ≠ s
    · ------------------------------------------------------------------
      -- NON-EXTREME maximum antichain `B`: glue down/up partitions.
      ------------------------------------------------------------------
      obtain ⟨B, hBs, hBanti, hBm, hBD, hBU⟩ := hnd
      have hmaxB : ∀ E ⊆ s, IsAntichainOn E → E.card ≤ B.card := by
        rw [hBm]; exact hmax
      have hDU : downSet B s ∪ upSet B s = s := downSet_union_upSet hBanti hBs hmaxB
      have hDIU : downSet B s ∩ upSet B s = B := downSet_inter_upSet hBanti hBs
      have hBD' : B ⊆ downSet B s := subset_downSet hBs
      have hBU' : B ⊆ upSet B s := subset_upSet hBs
      have hDs : downSet B s ⊆ s := downSet_subset B s
      have hUs : upSet B s ⊆ s := upSet_subset B s
      have hDss : downSet B s ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hDs, hBD⟩
      have hUss : upSet B s ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hUs, hBU⟩
      have hwD : ∀ E ⊆ downSet B s, IsAntichainOn E → E.card ≤ m :=
        fun E hE hEa => hmax E (hE.trans hDs) hEa
      have hwU : ∀ E ⊆ upSet B s, IsAntichainOn E → E.card ≤ m :=
        fun E hE hEa => hmax E (hE.trans hUs) hEa
      obtain ⟨𝒟, hParD, hcardD⟩ := ih (downSet B s) hDss m hwD
      obtain ⟨𝒰, hParU, hcardU⟩ := ih (upSet B s) hUss m hwU
      obtain ⟨hDchain, hDsub, hDcov, hDdisj⟩ := hParD
      obtain ⟨hUchain, hUsub, hUcov, hUdisj⟩ := hParU
      -- every down-part / up-part meets `B` (saturation pigeonhole)
      have hsatD : ∀ C ∈ 𝒟, ∃ a ∈ B, a ∈ C :=
        chain_meets_antichain_of_card_le hBanti hDchain
          (fun a ha => hDcov a (hBD' ha)) (by rw [hBm]; exact hcardD)
      -- choose, for each `a ∈ B`, its (unique) down-part and up-part
      let da : α → Finset α := fun a => if h : ∃ C ∈ 𝒟, a ∈ C then h.choose else ∅
      let ua : α → Finset α := fun a => if h : ∃ C ∈ 𝒰, a ∈ C then h.choose else ∅
      have hda : ∀ a ∈ B, da a ∈ 𝒟 ∧ a ∈ da a := by
        intro a ha
        have h : ∃ C ∈ 𝒟, a ∈ C := hDcov a (hBD' ha)
        have he : da a = h.choose := dif_pos h
        rw [he]; exact ⟨h.choose_spec.1, h.choose_spec.2⟩
      have hua : ∀ a ∈ B, ua a ∈ 𝒰 ∧ a ∈ ua a := by
        intro a ha
        have h : ∃ C ∈ 𝒰, a ∈ C := hUcov a (hBU' ha)
        have he : ua a = h.choose := dif_pos h
        rw [he]; exact ⟨h.choose_spec.1, h.choose_spec.2⟩
      let G : α → Finset α := fun a => da a ∪ ua a
      -- cross-membership ⟹ same index: members of two glued chains share `a`
      have hcross : ∀ a ∈ B, ∀ a' ∈ B, ∀ x, x ∈ G a → x ∈ G a' → a = a' := by
        intro a ha a' ha' x hxa hxa'
        have hdam := hda a ha; have hda'm := hda a' ha'
        have huam := hua a ha; have hua'm := hua a' ha'
        simp only [G, Finset.mem_union] at hxa hxa'
        rcases hxa with hxd | hxu <;> rcases hxa' with hxd' | hxu'
        · have heqC : da a = da a' :=
            hDdisj (da a) hdam.1 (da a') hda'm.1 x hxd hxd'
          have haa' : a ∈ da a' := heqC ▸ hdam.2
          exact chain_antichain_inter_subsingleton (hDchain _ hda'm.1) hBanti
            haa' ha hda'm.2 ha'
        · have hxD : x ∈ downSet B s := hDsub _ hdam.1 hxd
          have hxU : x ∈ upSet B s := hUsub _ hua'm.1 hxu'
          have hxB : x ∈ B := by
            have hxI : x ∈ downSet B s ∩ upSet B s := Finset.mem_inter.mpr ⟨hxD, hxU⟩
            rwa [hDIU] at hxI
          have hax : a = x := chain_antichain_inter_subsingleton (hDchain _ hdam.1) hBanti
            hdam.2 ha hxd hxB
          have ha'x : a' = x := chain_antichain_inter_subsingleton (hUchain _ hua'm.1) hBanti
            hua'm.2 ha' hxu' hxB
          rw [hax, ha'x]
        · have hxU : x ∈ upSet B s := hUsub _ huam.1 hxu
          have hxD : x ∈ downSet B s := hDsub _ hda'm.1 hxd'
          have hxB : x ∈ B := by
            have hxI : x ∈ downSet B s ∩ upSet B s := Finset.mem_inter.mpr ⟨hxD, hxU⟩
            rwa [hDIU] at hxI
          have hax : a = x := chain_antichain_inter_subsingleton (hUchain _ huam.1) hBanti
            huam.2 ha hxu hxB
          have ha'x : a' = x := chain_antichain_inter_subsingleton (hDchain _ hda'm.1) hBanti
            hda'm.2 ha' hxd' hxB
          rw [hax, ha'x]
        · have heqC : ua a = ua a' :=
            hUdisj (ua a) huam.1 (ua a') hua'm.1 x hxu hxu'
          have haa' : a ∈ ua a' := heqC ▸ huam.2
          exact chain_antichain_inter_subsingleton (hUchain _ hua'm.1) hBanti
            haa' ha hua'm.2 ha'
      refine ⟨B.image G, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · -- each glued part is a chain
        intro C hC
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
        exact glue_isChain hBanti (hDchain _ (hda a ha).1) (hDsub _ (hda a ha).1)
          (hUchain _ (hua a ha).1) (hUsub _ (hua a ha).1) ha (hda a ha).2 (hua a ha).2
      · -- each glued part is contained in `s`
        intro C hC
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
        intro x hx
        simp only [G, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hDs (hDsub _ (hda a ha).1 hx)
        · exact hUs (hUsub _ (hua a ha).1 hx)
      · -- the glued parts cover `s`
        intro x hxs
        rw [← hDU, Finset.mem_union] at hxs
        rcases hxs with hxD | hxU
        · obtain ⟨C, hC, hxC⟩ := hDcov x hxD
          obtain ⟨a, ha, haC⟩ := hsatD C hC
          have hCda : C = da a :=
            hDdisj C hC (da a) (hda a ha).1 a haC (hda a ha).2
          refine ⟨G a, Finset.mem_image_of_mem G ha, ?_⟩
          simp only [G, Finset.mem_union]; exact Or.inl (hCda ▸ hxC)
        · obtain ⟨C, hC, hxC⟩ := hUcov x hxU
          obtain ⟨a, ha, haC⟩ :=
            chain_meets_antichain_of_card_le hBanti hUchain
              (fun a ha => hUcov a (hBU' ha)) (by rw [hBm]; exact hcardU) C hC
          have hCua : C = ua a :=
            hUdisj C hC (ua a) (hua a ha).1 a haC (hua a ha).2
          refine ⟨G a, Finset.mem_image_of_mem G ha, ?_⟩
          simp only [G, Finset.mem_union]; exact Or.inr (hCua ▸ hxC)
      · -- glued parts are pairwise disjoint (unique containing part)
        intro C hC C' hC' x hxC hxC'
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
        obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hC'
        have : a = a' := hcross a ha a' ha' x hxC hxC'
        rw [this]
      · -- at most `m ≤ w` parts
        exact le_trans Finset.card_image_le (by rw [hBm]; exact hmw)
    · ------------------------------------------------------------------
      -- EXTREME: every maximum antichain is min- or max-element set.
      -- Remove a minimal-to-maximal chain `{x, y}`.
      ------------------------------------------------------------------
      push_neg at hnd
      obtain ⟨y, hy⟩ := Finset.exists_maximal (s := s) ⟨z₀, hz₀⟩
      have hys : y ∈ s := hy.1
      have hymax : ∀ z ∈ s, y ≤ z → z = y := fun z hz hyz => le_antisymm (hy.2 hz hyz) hyz
      set F : Finset α := s.filter (fun z => z ≤ y) with hFdef
      have hyF : y ∈ F := by rw [hFdef, Finset.mem_filter]; exact ⟨hys, le_refl y⟩
      obtain ⟨x, hx⟩ := Finset.exists_minimal (s := F) ⟨y, hyF⟩
      have hxF : x ∈ F := hx.1
      rw [hFdef, Finset.mem_filter] at hxF
      obtain ⟨hxs, hxy⟩ := hxF
      have hxmin : ∀ z ∈ s, z ≤ x → z = x := by
        intro z hzs hzx
        have hzF : z ∈ F := by rw [hFdef, Finset.mem_filter]; exact ⟨hzs, le_trans hzx hxy⟩
        exact le_antisymm hzx (hx.2 hzF hzx)
      set K : Finset α := {x, y} with hKdef
      have hxK : x ∈ K := by rw [hKdef]; exact Finset.mem_insert_self x {y}
      have hyK : y ∈ K := by rw [hKdef]; simp
      have hKs : K ⊆ s := by
        rw [hKdef]; intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxs
        · exact hys
      have hKchain : IsChainOn K := by
        intro a haK b hbK
        rw [hKdef, Finset.mem_insert, Finset.mem_singleton] at haK hbK
        rcases haK with rfl | rfl <;> rcases hbK with rfl | rfl
        · exact Or.inl (le_refl _)
        · exact Or.inl hxy
        · exact Or.inr hxy
        · exact Or.inl (le_refl _)
      have hsubK : s \ K ⊂ s := Finset.sdiff_ssubset hKs ⟨x, hxK⟩
      have hwK : ∀ B ⊆ s \ K, IsAntichainOn B → B.card ≤ m - 1 := by
        intro B hBsK hBanti
        have hBs : B ⊆ s := hBsK.trans Finset.sdiff_subset
        have hBm : B.card ≤ m := hmax B hBs hBanti
        rcases Nat.lt_or_ge B.card m with hlt | hge
        · omega
        · exfalso
          have hBeq : B.card = m := le_antisymm hBm hge
          have hext : downSet B s = s ∨ upSet B s = s := by
            by_cases hDeq : downSet B s = s
            · exact Or.inl hDeq
            · exact Or.inr (hnd B hBs hBanti hBeq hDeq)
          rcases hext with hD | hU
          · have hyD : y ∈ downSet B s := by rw [hD]; exact hys
            obtain ⟨b, hb, hyb⟩ := (mem_downSet.mp hyD).2
            have hyB : y ∈ B := (hymax b (hBs hb) hyb) ▸ hb
            exact (Finset.mem_sdiff.mp (hBsK hyB)).2 hyK
          · have hxU : x ∈ upSet B s := by rw [hU]; exact hxs
            obtain ⟨b, hb, hbx⟩ := (mem_upSet.mp hxU).2
            have hxB : x ∈ B := (hxmin b (hBs hb) hbx) ▸ hb
            exact (Finset.mem_sdiff.mp (hBsK hxB)).2 hxK
      obtain ⟨𝒞', hPar', hcard'⟩ := ih (s \ K) hsubK (m - 1) hwK
      obtain ⟨hC'chain, hC'sub, hC'cov, hC'disj⟩ := hPar'
      refine ⟨insert K 𝒞', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro C hC
        rw [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hKchain
        · exact hC'chain C hC
      · intro C hC
        rw [Finset.mem_insert] at hC
        rcases hC with rfl | hC
        · exact hKs
        · exact (hC'sub C hC).trans Finset.sdiff_subset
      · intro z hzs
        by_cases hzK : z ∈ K
        · exact ⟨K, Finset.mem_insert_self _ _, hzK⟩
        · obtain ⟨C, hC, hzC⟩ := hC'cov z (Finset.mem_sdiff.mpr ⟨hzs, hzK⟩)
          exact ⟨C, Finset.mem_insert_of_mem hC, hzC⟩
      · intro C hC C' hC' x' hxC hxC'
        rw [Finset.mem_insert] at hC hC'
        rcases hC with rfl | hC <;> rcases hC' with rfl | hC'
        · rfl
        · exact absurd hxC (Finset.mem_sdiff.mp ((hC'sub C' hC') hxC')).2
        · exact absurd hxC' (Finset.mem_sdiff.mp ((hC'sub C hC) hxC)).2
        · exact hC'disj C hC C' hC' x' hxC hxC'
      · have h1 := Finset.card_insert_le K 𝒞'
        omega

/-- **Dilworth's theorem, hard direction (strong form).**
    If every antichain contained in the ground `Finset` `s` has at most `w`
    elements, then `s` is covered by at most `w` chains, each a subset of `s`.

    Combined with `DilworthTheoremOQ01.antichain_card_le_of_chainCover` (the easy
    direction), taking `w` to be the maximum antichain size gives the classical
    equality `min chain cover = max antichain`.  Immediate from the partition form
    `dilworth_chainPartition` by forgetting disjointness. -/
theorem dilworth_chainCover
    [DecidableEq α] [DecidableLE α] (s : Finset α) (w : ℕ)
    (hw : ∀ A ⊆ s, IsAntichainOn A → A.card ≤ w) :
    ∃ 𝒞 : Finset (Finset α),
      (∀ C ∈ 𝒞, IsChainOn C ∧ C ⊆ s) ∧
      (∀ x ∈ s, ∃ C ∈ 𝒞, x ∈ C) ∧
      𝒞.card ≤ w := by
  obtain ⟨𝒞, ⟨hchain, hsub, hcover, _⟩, hcard⟩ := dilworth_chainPartition s w hw
  exact ⟨𝒞, fun C hC => ⟨hchain C hC, hsub C hC⟩, hcover, hcard⟩

end DilworthHardOQ01OQ02
