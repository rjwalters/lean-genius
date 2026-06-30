/-
  The common min–max framework: from Mirsky to Erdős–Szekeres.
  (dilworth-theorem-oq-01-oq-01-oq-03)

  ## Background

  The companion files supply the two halves of the Dilworth/Mirsky picture for a
  finite poset:

  * `Proofs.DilworthTheoremOQ01` — the *easy* directions (a chain meets an
    antichain in at most one point), together with `IsChainOn` / `IsAntichainOn`.
  * `Proofs.DilworthMirskyHardOQ01` — **Mirsky's hard direction**: the height /
    level decomposition covers the poset by exactly `maxChainLen` antichains
    (`mirsky_antichain_cover`).

  ## What this file adds

  The open question asks to tie Mirsky and Dilworth together through a *common
  min–max framework* and to obtain **Erdős–Szekeres** as an application.  The
  bridge is a single counting inequality:

      `card α ≤ maxChainLen · maxAntichainLen`        (`card_le_maxChainLen_mul_maxAntichainLen`)

  Mirsky covers the poset by `maxChainLen` antichains, and each antichain has at
  most `maxAntichainLen` elements; multiplying gives the bound.  Its contrapositive
  is the **Erdős–Szekeres dichotomy**

      `r·s < card α  ⟹  (a chain of size > r)  ∨  (an antichain of size > s)`

  (`exists_long_chain_or_antichain`).  Specialised to the poset on positions of a
  finite sequence `f : Fin N → ℝ`, ordered by `i ≼ j ↔ i ≤ j ∧ f i ≤ f j`, chains
  are non-decreasing subsequences and antichains are strictly decreasing ones, and
  the dichotomy becomes the classical Erdős–Szekeres theorem
  (`erdos_szekeres_seq`): every sequence of more than `r·s` reals has a
  non-decreasing run of length `> r` or a strictly decreasing run of length `> s`.

  ## Status: 0 axioms, 0 sorries.
-/
import Proofs.DilworthMirskyHardOQ01

open Classical

attribute [local instance] Classical.propDecidable

namespace DilworthTheoremOQ01

variable {α : Type*} [PartialOrder α] [Fintype α]

/-! ### Maximum antichain length -/

/-- All antichains of the (finite) poset. -/
noncomputable def allAntichains : Finset (Finset α) :=
  Finset.univ.powerset.filter (fun A => IsAntichainOn A)

/-- `maxAntichainLen` = the size of a largest antichain. -/
noncomputable def maxAntichainLen : ℕ := (allAntichains (α := α)).sup Finset.card

theorem mem_allAntichains {A : Finset α} : A ∈ allAntichains ↔ IsAntichainOn A := by
  unfold allAntichains
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.subset_univ _, h⟩⟩

/-- Every antichain is no larger than `maxAntichainLen`. -/
theorem antichain_card_le_maxAntichainLen {A : Finset α} (hA : IsAntichainOn A) :
    A.card ≤ maxAntichainLen (α := α) :=
  Finset.le_sup (f := Finset.card) (mem_allAntichains.mpr hA)

/-- `maxAntichainLen` is attained by an actual antichain. -/
theorem exists_antichain_card_eq_maxAntichainLen :
    ∃ A : Finset α, IsAntichainOn A ∧ A.card = maxAntichainLen (α := α) := by
  have hne : (allAntichains (α := α)).Nonempty :=
    ⟨∅, mem_allAntichains.mpr (by intro x hx; exact absurd hx (Finset.notMem_empty x))⟩
  obtain ⟨A, hA, hCard⟩ :=
    Finset.exists_mem_eq_sup (allAntichains (α := α)) hne Finset.card
  exact ⟨A, mem_allAntichains.mp hA, hCard.symm⟩

/-! ### The common min–max counting bound -/

/-- **Common min–max bound.**  A finite poset has at most
    `maxChainLen · maxAntichainLen` elements.  Mirsky covers it by `maxChainLen`
    antichains, each of size at most `maxAntichainLen`. -/
theorem card_le_maxChainLen_mul_maxAntichainLen :
    Fintype.card α ≤ maxChainLen (α := α) * maxAntichainLen (α := α) := by
  obtain ⟨𝒜, hanti, hcover, hle⟩ := mirsky_antichain_cover (α := α)
  have hsub : (Finset.univ : Finset α) ⊆ 𝒜.biUnion id := by
    intro x _
    obtain ⟨A, hA, hxA⟩ := hcover x
    rw [Finset.mem_biUnion]
    exact ⟨A, hA, hxA⟩
  calc Fintype.card α
      = (Finset.univ : Finset α).card := (Finset.card_univ).symm
    _ ≤ (𝒜.biUnion id).card := Finset.card_le_card hsub
    _ ≤ ∑ A ∈ 𝒜, (id A).card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ 𝒜, maxAntichainLen (α := α) :=
        Finset.sum_le_sum (fun A hA => antichain_card_le_maxAntichainLen (hanti A hA))
    _ = 𝒜.card * maxAntichainLen (α := α) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ maxChainLen (α := α) * maxAntichainLen (α := α) :=
        Nat.mul_le_mul_right _ hle

/-- **Erdős–Szekeres dichotomy (poset form).**  If a finite poset has more than
    `r · s` elements, then it contains a chain of size `> r` or an antichain of
    size `> s`.  This is the contrapositive of the counting bound. -/
theorem exists_long_chain_or_antichain {r s : ℕ}
    (h : r * s < Fintype.card α) :
    (∃ C : Finset α, IsChainOn C ∧ r < C.card) ∨
    (∃ A : Finset α, IsAntichainOn A ∧ s < A.card) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hC, hA⟩ := hcon
  have hcl : maxChainLen (α := α) ≤ r := by
    obtain ⟨C, hCchain, hCcard⟩ := exists_chain_card_eq_maxChainLen (α := α)
    have := hC C hCchain; omega
  have hal : maxAntichainLen (α := α) ≤ s := by
    obtain ⟨A, hAanti, hAcard⟩ := exists_antichain_card_eq_maxAntichainLen (α := α)
    have := hA A hAanti; omega
  have hbound := card_le_maxChainLen_mul_maxAntichainLen (α := α)
  have : Fintype.card α ≤ r * s := le_trans hbound (Nat.mul_le_mul hcl hal)
  omega

end DilworthTheoremOQ01

/-! ### Erdős–Szekeres for sequences

  We specialise the dichotomy to the poset on the positions of a finite sequence
  `f : Fin N → β` (`β` linearly ordered), ordered by

      `i ≼ j  ↔  i ≤ j  ∧  f i ≤ f j`.

  A chain of this poset is a non-decreasing subsequence, and an antichain is a
  strictly decreasing subsequence; transporting the chains/antichains produced by
  the dichotomy through the position map yields Erdős–Szekeres. -/

open DilworthTheoremOQ01

/-- A position of a sequence `f : Fin N → β`, carrying the product order
    `i ≼ j ↔ i ≤ j ∧ f i ≤ f j`. -/
@[ext]
structure SeqPos {N : ℕ} {β : Type*} (f : Fin N → β) where
  pos : Fin N

namespace SeqPos

variable {N : ℕ} {β : Type*} [LinearOrder β] {f : Fin N → β}

instance : PartialOrder (SeqPos f) where
  le a b := a.pos ≤ b.pos ∧ f a.pos ≤ f b.pos
  le_refl a := ⟨le_refl _, le_refl _⟩
  le_trans a b c hab hbc := ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    have : a.pos = b.pos := le_antisymm hab.1 hba.1
    exact SeqPos.ext this

@[simp] theorem le_def {a b : SeqPos f} : a ≤ b ↔ a.pos ≤ b.pos ∧ f a.pos ≤ f b.pos :=
  Iff.rfl

/-- Positions are in bijection with `Fin N`. -/
def equivFin : SeqPos f ≃ Fin N where
  toFun := SeqPos.pos
  invFun := SeqPos.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (SeqPos f) := Fintype.ofEquiv (Fin N) equivFin.symm

omit [LinearOrder β] in
theorem card_eq : Fintype.card (SeqPos f) = N := by
  rw [Fintype.card_congr (equivFin (f := f)), Fintype.card_fin]

omit [LinearOrder β] in
theorem pos_injective : Function.Injective (SeqPos.pos (f := f)) :=
  fun _ _ h => SeqPos.ext h

/-- The position set of a **chain** is a non-decreasing index set. -/
theorem image_pos_nondecr {C : Finset (SeqPos f)} (hC : IsChainOn C) :
    ∀ i ∈ C.image SeqPos.pos, ∀ j ∈ C.image SeqPos.pos, i ≤ j → f i ≤ f j := by
  intro i hi j hj hij
  rw [Finset.mem_image] at hi hj
  obtain ⟨a, haC, rfl⟩ := hi
  obtain ⟨b, hbC, rfl⟩ := hj
  rcases hC haC hbC with hab | hba
  · exact hab.2
  · -- `b ≤ a` gives `b.pos ≤ a.pos`; with `a.pos ≤ b.pos` the positions coincide.
    have : a.pos = b.pos := le_antisymm hij hba.1
    rw [this]

/-- The position set of an **antichain** is a strictly decreasing index set. -/
theorem image_pos_strictdecr {A : Finset (SeqPos f)} (hA : IsAntichainOn A) :
    ∀ i ∈ A.image SeqPos.pos, ∀ j ∈ A.image SeqPos.pos, i < j → f j < f i := by
  intro i hi j hj hij
  rw [Finset.mem_image] at hi hj
  obtain ⟨a, haC, rfl⟩ := hi
  obtain ⟨b, hbC, rfl⟩ := hj
  -- `a.pos < b.pos`, so `a ≠ b`; in an antichain that forces incomparability.
  have hne : a ≠ b := fun h => absurd (h ▸ hij) (lt_irrefl _)
  -- If `a ≤ b` held, the antichain would force `a = b`.
  have hnle : ¬ a ≤ b := fun hab => hne (hA haC hbC hab)
  rw [le_def] at hnle
  push_neg at hnle
  exact hnle hij.le

omit [LinearOrder β] in
theorem card_image_pos {C : Finset (SeqPos f)} :
    (C.image SeqPos.pos).card = C.card :=
  Finset.card_image_of_injective C pos_injective

end SeqPos

/-- **Erdős–Szekeres for sequences.**  Any sequence `f : Fin N → β` (with `β`
    linearly ordered) of length `N > r · s` contains either a **non-decreasing**
    subsequence on more than `r` positions or a **strictly decreasing**
    subsequence on more than `s` positions.

    Taking `N = r·s + 1` recovers the classical statement: a sequence of `r·s + 1`
    terms has a non-decreasing run of length `r+1` or a strictly decreasing run of
    length `s+1`. -/
theorem erdos_szekeres_seq {N : ℕ} {β : Type*} [LinearOrder β] (f : Fin N → β)
    {r s : ℕ} (h : r * s < N) :
    (∃ t : Finset (Fin N), r < t.card ∧ ∀ i ∈ t, ∀ j ∈ t, i ≤ j → f i ≤ f j) ∨
    (∃ t : Finset (Fin N), s < t.card ∧ ∀ i ∈ t, ∀ j ∈ t, i < j → f j < f i) := by
  have hcard : r * s < Fintype.card (SeqPos f) := by rw [SeqPos.card_eq]; exact h
  rcases exists_long_chain_or_antichain (α := SeqPos f) hcard with
    ⟨C, hChain, hrC⟩ | ⟨A, hAnti, hsA⟩
  · refine Or.inl ⟨C.image SeqPos.pos, ?_, SeqPos.image_pos_nondecr hChain⟩
    rwa [SeqPos.card_image_pos]
  · refine Or.inr ⟨A.image SeqPos.pos, ?_, SeqPos.image_pos_strictdecr hAnti⟩
    rwa [SeqPos.card_image_pos]
