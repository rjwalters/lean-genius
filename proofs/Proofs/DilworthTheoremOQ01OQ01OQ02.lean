/-
  Dilworth / Mirsky — bridging the gallery's combinatorial `maxChainLen` to
  Mathlib's order-theoretic `Set.chainHeight`.
  (dilworth-theorem-oq-01-oq-01-oq-02)

  ## Background

  The companion file `Proofs.DilworthMirskyHardOQ01` develops the hard
  (attainment) direction of Mirsky's theorem on a finite poset.  Its central
  combinatorial invariant is

      `maxChainLen = (allChains).sup Finset.card : ℕ`,

  the largest cardinality of a chain (a pairwise-`≤`-comparable `Finset`).

  Mathlib has its own order-theoretic notion of the same quantity,

      `Set.chainHeight r s = ⨆ {t // t ⊆ s ∧ IsChain r t}, t.encard : ℕ∞`,

  the supremum (in `ℕ∞`) of the extended cardinalities of `r`-chains contained
  in a set `s`.

  ## What this file proves

  The single **definitional bridge lemma** that the two notions coincide on the
  whole finite poset, taken with respect to `≤`:

      `maxChainLen_eq_univ_chainHeight` :
          (maxChainLen : ℕ∞) = (Set.univ).chainHeight (· ≤ ·)`.

  The proof is two opposite inequalities, each one line of real content thanks
  to Mathlib's chain-height API:

  * `≤` : the chain attaining `maxChainLen` (from the parent's
    `exists_chain_card_eq_maxChainLen`) is, as a set, an `IsChain (· ≤ ·)`, so
    `encard_le_chainHeight_of_isChain` bounds `chainHeight` from below.
  * `≥` : `exists_eq_chainHeight_of_finite` produces a chain *set* attaining
    `chainHeight`; pushing it to a `Finset` lands it in `allChains`, whose
    cardinalities are bounded by `maxChainLen` via `Finset.le_sup`.

  The bridge is purely a translation between two encodings of the same maximum,
  so it carries `0 sorries, 0 axioms`.  As an immediate consequence we restate
  the parent's Mirsky theorem (`mirsky_min_antichain_cover`) in Mathlib's
  vocabulary: the chain height of the poset equals the minimum size of an
  antichain cover (`mirsky_chainHeight`).

  ## Status: BUILD-TARGET.  0 axioms, 0 sorries.
-/
import Mathlib
import Proofs.DilworthMirskyHardOQ01

open Classical Set

attribute [local instance] Classical.propDecidable

namespace DilworthTheoremOQ01

variable {α : Type*} [PartialOrder α] [Fintype α]

omit [Fintype α] in
/-- The parent's `IsChainOn` (a pairwise-`≤`-comparable `Finset`) is exactly
Mathlib's `IsChain (· ≤ ·)` on the underlying set of points. -/
theorem isChainOn_iff_isChain (C : Finset α) :
    IsChainOn C ↔ IsChain (· ≤ ·) (↑C : Set α) := by
  constructor
  · intro h x hx y hy _hne
    exact h (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy)
  · intro h x hx y hy
    rcases eq_or_ne x y with rfl | hne
    · exact Or.inl le_rfl
    · exact h (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hne

/-- **Bridge to `Set.chainHeight`.** The gallery's combinatorial maximum chain
length `maxChainLen` agrees with Mathlib's order-theoretic `Set.chainHeight` of
the whole (finite) poset, taken with respect to `≤`. -/
theorem maxChainLen_eq_univ_chainHeight :
    (maxChainLen (α := α) : ℕ∞) = (Set.univ : Set α).chainHeight (· ≤ ·) := by
  apply le_antisymm
  · -- `maxChainLen ≤ chainHeight`: the attaining chain witnesses the supremum.
    obtain ⟨C, hC, hCard⟩ := exists_chain_card_eq_maxChainLen (α := α)
    have hchain : IsChain (· ≤ ·) (↑C : Set α) := (isChainOn_iff_isChain C).mp hC
    have hle :=
      encard_le_chainHeight_of_isChain (Set.univ) (↑C : Set α) (Set.subset_univ _) hchain
    rwa [Set.encard_coe_eq_coe_finsetCard, hCard] at hle
  · -- `chainHeight ≤ maxChainLen`: a chain set attaining `chainHeight` becomes a
    -- `Finset` in `allChains`, hence bounded by the `sup`.
    obtain ⟨t, hsub, ht_enc, ht_chain⟩ :=
      exists_eq_chainHeight_of_finite (Set.univ : Set α) (· ≤ ·) Set.finite_univ
    have ht_fin : t.Finite := Set.finite_univ.subset hsub
    rw [← ht_enc, ht_fin.encard_eq_coe_toFinset_card]
    have hCo : IsChainOn ht_fin.toFinset := by
      rw [isChainOn_iff_isChain, ht_fin.coe_toFinset]; exact ht_chain
    have hmem : ht_fin.toFinset ∈ allChains (α := α) := by
      unfold allChains
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, hCo⟩
    have hle : ht_fin.toFinset.card ≤ maxChainLen (α := α) :=
      Finset.le_sup (f := Finset.card) hmem
    exact_mod_cast hle

/-- The chain height of a finite poset is finite (never `⊤`). -/
theorem univ_chainHeight_ne_top :
    (Set.univ : Set α).chainHeight (· ≤ ·) ≠ ⊤ := by
  rw [← maxChainLen_eq_univ_chainHeight]; exact ENat.coe_ne_top _

/-- **Mirsky's theorem, in Mathlib's vocabulary.** The order-theoretic chain
height of a finite poset equals the minimum size of an antichain cover:
there is an antichain cover whose cardinality equals `Set.chainHeight`, and no
antichain cover is smaller. -/
theorem mirsky_chainHeight :
    ∃ 𝒜 : Finset (Finset α),
      (∀ A ∈ 𝒜, IsAntichainOn A) ∧
      (∀ x : α, ∃ A ∈ 𝒜, x ∈ A) ∧
      (𝒜.card : ℕ∞) = (Set.univ : Set α).chainHeight (· ≤ ·) ∧
      (∀ ℬ : Finset (Finset α),
        (∀ A ∈ ℬ, IsAntichainOn A) → (∀ x : α, ∃ A ∈ ℬ, x ∈ A) →
        𝒜.card ≤ ℬ.card) := by
  obtain ⟨𝒜, hanti, hcover, hcard, hmin⟩ := mirsky_min_antichain_cover (α := α)
  refine ⟨𝒜, hanti, hcover, ?_, hmin⟩
  rw [hcard]; exact maxChainLen_eq_univ_chainHeight

end DilworthTheoremOQ01
