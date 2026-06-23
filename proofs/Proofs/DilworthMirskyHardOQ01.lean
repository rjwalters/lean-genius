/-
  Mirsky's Theorem — the HARD direction (attainment), for a finite poset.
  (dilworth-theorem-oq-01, follow-up)

  ## Background

  The companion file `Proofs.DilworthTheoremOQ01` proves the *easy* directions
  of the Dilworth/Mirsky dualities: a chain and an antichain meet in at most one
  point, hence every chain is no larger than any antichain cover
  (`chain_card_le_of_antichainCover`).

  Mirsky's theorem (1971) states that on a finite poset the **minimum number of
  antichains needed to cover the poset equals the maximum length of a chain**.
  The easy direction gives `maxChainLen ≤ (any antichain cover).card`.  This file
  supplies the *hard* direction: a cover by exactly `maxChainLen` antichains
  actually exists, so the minimum is attained.

  ## Method (height / level decomposition)

  For each element `x` set

      `height x = max { |C| : C a chain whose maximum element is x }`.

  Then:

  * `1 ≤ height x ≤ maxChainLen`  (a singleton is such a chain; any such chain is
    a chain of the whole poset).
  * The level set `level k = { x : height x = k }` is an **antichain**: if
    `x < y` with `height x = height y = k`, append `y` to a longest chain ending
    at `x` to get a chain of length `k+1` ending at `y`, forcing
    `height y ≥ k+1`, a contradiction.

  The `maxChainLen` nonempty levels `level 1, …, level maxChainLen` therefore
  cover the poset, giving `mirsky_antichain_cover`.  Combined with the easy
  direction we obtain `mirsky_min_antichain_cover`: this cover is minimal and has
  size exactly `maxChainLen`.

  ## Status: registered and verified.  0 axioms, 0 sorries.
-/
import Proofs.DilworthTheoremOQ01

open Classical

-- Register classical decidability as a local instance so that `Finset`
-- operations over `Finset α` (notably `Fintype (Finset α)`, which needs
-- `DecidableEq α`) resolve uniformly without threading decidability
-- hypotheses through the statements.  Everything here is `noncomputable`.
attribute [local instance] Classical.propDecidable

namespace DilworthTheoremOQ01

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- Chains whose maximum element is `x`: chains `C` with `x ∈ C` and every member
    of `C` below `x`. -/
noncomputable def chainsTo (x : α) : Finset (Finset α) :=
  Finset.univ.powerset.filter (fun C => IsChainOn C ∧ x ∈ C ∧ ∀ z ∈ C, z ≤ x)

/-- `height x` = the size of a longest chain whose maximum element is `x`. -/
noncomputable def height (x : α) : ℕ := (chainsTo x).sup Finset.card

/-- All chains of the (finite) poset. -/
noncomputable def allChains : Finset (Finset α) :=
  Finset.univ.powerset.filter (fun C => IsChainOn C)

/-- The maximum length of a chain. -/
noncomputable def maxChainLen : ℕ := (allChains (α := α)).sup Finset.card

theorem mem_chainsTo {x : α} {C : Finset α} :
    C ∈ chainsTo x ↔ IsChainOn C ∧ x ∈ C ∧ ∀ z ∈ C, z ≤ x := by
  unfold chainsTo
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.subset_univ _, h⟩⟩

/-- A singleton is a chain whose maximum element is `x`. -/
theorem singleton_mem_chainsTo (x : α) : ({x} : Finset α) ∈ chainsTo x := by
  rw [mem_chainsTo]
  refine ⟨?_, Finset.mem_singleton_self x, ?_⟩
  · intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst ha; subst hb; exact Or.inl le_rfl
  · intro z hz
    rw [Finset.mem_singleton] at hz; subst hz; exact le_rfl

theorem chainsTo_nonempty (x : α) : (chainsTo x).Nonempty :=
  ⟨{x}, singleton_mem_chainsTo x⟩

theorem one_le_height (x : α) : 1 ≤ height x := by
  have h := Finset.le_sup (f := Finset.card) (singleton_mem_chainsTo x)
  rw [Finset.card_singleton] at h
  exact h

/-- The supremum defining `height` is attained by an actual chain. -/
theorem exists_chainsTo_card_eq_height (x : α) :
    ∃ C ∈ chainsTo x, C.card = height x := by
  obtain ⟨C, hC, hCard⟩ :=
    Finset.exists_mem_eq_sup (chainsTo x) (chainsTo_nonempty x) Finset.card
  exact ⟨C, hC, hCard.symm⟩

theorem height_le_maxChainLen (x : α) : height x ≤ maxChainLen (α := α) := by
  unfold height maxChainLen
  apply Finset.sup_mono
  intro C hC
  rw [mem_chainsTo] at hC
  unfold allChains
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, hC.1⟩

/-- The `k`-th level: elements of height exactly `k`. -/
noncomputable def level (k : ℕ) : Finset α := Finset.univ.filter (fun x => height x = k)

theorem mem_level {k : ℕ} {x : α} : x ∈ level k ↔ height x = k := by
  unfold level
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **Key lemma.**  Each level set is an antichain. -/
theorem level_isAntichain (k : ℕ) : IsAntichainOn (level (α := α) k) := by
  intro x hx y hy hxy
  rw [mem_level] at hx hy
  by_contra hne
  have hxlty : x < y := lt_of_le_of_ne hxy hne
  obtain ⟨C, hC, hCcard⟩ := exists_chainsTo_card_eq_height x
  rw [mem_chainsTo] at hC
  obtain ⟨hChain, _hxmem, hCle⟩ := hC
  have hyC : y ∉ C := by
    intro hyC'
    exact absurd (hCle y hyC') hxlty.not_ge
  have hC' : insert y C ∈ chainsTo y := by
    rw [mem_chainsTo]
    refine ⟨?_, Finset.mem_insert_self y C, ?_⟩
    · intro a ha b hb
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | haC
      · rcases hb with rfl | hbC
        · exact Or.inl le_rfl
        · exact Or.inr ((hCle b hbC).trans hxlty.le)
      · rcases hb with rfl | hbC
        · exact Or.inl ((hCle a haC).trans hxlty.le)
        · exact hChain haC hbC
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hzC
      · exact le_rfl
      · exact (hCle z hzC).trans hxlty.le
  have hge : (insert y C).card ≤ height y := Finset.le_sup hC'
  rw [Finset.card_insert_of_notMem hyC, hCcard, hx] at hge
  omega

/-- **Mirsky, hard direction.**  A finite poset is covered by at most
    `maxChainLen` antichains. -/
theorem mirsky_antichain_cover :
    ∃ 𝒜 : Finset (Finset α),
      (∀ A ∈ 𝒜, IsAntichainOn A) ∧
      (∀ x : α, ∃ A ∈ 𝒜, x ∈ A) ∧
      𝒜.card ≤ maxChainLen (α := α) := by
  refine ⟨((Finset.univ : Finset α).image height).image level, ?_, ?_, ?_⟩
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨k, _, rfl⟩ := hA
    exact level_isAntichain k
  · intro x
    refine ⟨level (height x), ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨height x, Finset.mem_image_of_mem height (Finset.mem_univ x), rfl⟩
    · exact mem_level.mpr rfl
  · calc (((Finset.univ : Finset α).image height).image level).card
        ≤ ((Finset.univ : Finset α).image height).card := Finset.card_image_le
      _ ≤ (Finset.Icc 1 (maxChainLen (α := α))).card := by
          apply Finset.card_le_card
          intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨x, _, rfl⟩ := hk
          rw [Finset.mem_Icc]
          exact ⟨one_le_height x, height_le_maxChainLen x⟩
      _ = maxChainLen (α := α) := by rw [Nat.card_Icc]; omega

/-- `maxChainLen` is attained by an actual chain. -/
theorem exists_chain_card_eq_maxChainLen :
    ∃ C : Finset α, IsChainOn C ∧ C.card = maxChainLen (α := α) := by
  have hne : (allChains (α := α)).Nonempty := by
    refine ⟨∅, ?_⟩
    unfold allChains
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro a ha; exact absurd ha (Finset.notMem_empty a)
  obtain ⟨C, hC, hCard⟩ :=
    Finset.exists_mem_eq_sup (allChains (α := α)) hne Finset.card
  unfold allChains at hC
  rw [Finset.mem_filter, Finset.mem_powerset] at hC
  exact ⟨C, hC.2, hCard.symm⟩

/-- The easy direction, re-stated: any antichain cover has at least
    `maxChainLen` members. -/
theorem maxChainLen_le_card_of_antichainCover {𝒜 : Finset (Finset α)}
    (hanti : ∀ A ∈ 𝒜, IsAntichainOn A) (hcover : ∀ x : α, ∃ A ∈ 𝒜, x ∈ A) :
    maxChainLen (α := α) ≤ 𝒜.card := by
  obtain ⟨C, hC, hCard⟩ := exists_chain_card_eq_maxChainLen (α := α)
  have hcoverC : ∀ c ∈ C, ∃ A ∈ 𝒜, c ∈ A := fun c _ => hcover c
  have h := chain_card_le_of_antichainCover hC hanti hcoverC
  rwa [hCard] at h

/-- **Mirsky's theorem.**  There is an antichain cover of size exactly
    `maxChainLen`, and it is minimal among all antichain covers. -/
theorem mirsky_min_antichain_cover :
    ∃ 𝒜 : Finset (Finset α),
      (∀ A ∈ 𝒜, IsAntichainOn A) ∧
      (∀ x : α, ∃ A ∈ 𝒜, x ∈ A) ∧
      𝒜.card = maxChainLen (α := α) ∧
      (∀ ℬ : Finset (Finset α),
        (∀ A ∈ ℬ, IsAntichainOn A) → (∀ x : α, ∃ A ∈ ℬ, x ∈ A) →
        𝒜.card ≤ ℬ.card) := by
  obtain ⟨𝒜, hanti, hcover, hle⟩ := mirsky_antichain_cover (α := α)
  have hge := maxChainLen_le_card_of_antichainCover hanti hcover
  have hcard : 𝒜.card = maxChainLen (α := α) := le_antisymm hle hge
  refine ⟨𝒜, hanti, hcover, hcard, ?_⟩
  intro ℬ hℬanti hℬcover
  rw [hcard]
  exact maxChainLen_le_card_of_antichainCover hℬanti hℬcover

end DilworthTheoremOQ01
