/-
# The Club Filter and the Nonstationary Ideal
## CantorDiagonalizationOQ02OQ03OQ02OQ01

Building on `CantorDiagonalizationOQ02OQ03OQ02` (Fodor's pressing-down lemma), this
file answers that proof's **first open question**:

> *Formalize the club filter: show that clubs generate a filter (finite intersection
> of clubs is a club), and that stationary sets are exactly the sets not in the dual
> ideal.*

For an uncountable regular cardinal κ the clubs (closed unbounded subsets of the
ordinals below `κ.ord`) form a base for a **σ-complete filter** — the *club filter*
`Club(κ)`. Its dual ideal is the **nonstationary ideal** `NS(κ)`, and a set is
*stationary* exactly when it is **not** in `NS(κ)`. This file establishes the finite
part of that picture from the ground up:

## What is proved (0 sorries, 0 axioms)

1. **Top element** — `Set.univ` is a club (`isClub_univ`).
2. **Binary intersection** — the intersection of two clubs is a club
   (`inter_isClub`). The closed part is immediate; the **unbounded part**
   (`inter_isUnbounded`) is the genuine content: given α₀ we interleave the two
   clubs into a single ω-chain α₀ < c₀ < d₀ < c₁ < d₁ < … whose supremum γ < κ.ord
   is approached cofinally from *inside each club separately*, so closedness puts γ
   in both. This is the binary instance of the diagonal-intersection argument the
   parent proved for κ-indexed families.
3. **Finite intersection** — `⋂ i ∈ t, C i` is a club for any `Finset` of clubs
   (`isClub_biInter`), by induction on the finite index set. This is exactly the
   statement "the clubs are closed under finite intersection", i.e. they generate a
   (proper) filter.
4. **Nonstationary ideal** (`IsNonStationary`) — defined as "disjoint from some
   club". We show it is genuinely an ideal:
   - downward closed under `⊆` (`isNonStationary_subset`),
   - closed under binary union (`isNonStationary_union`) — this is precisely where
     `inter_isClub` is needed: `S` avoids `C`, `T` avoids `D`, so `S ∪ T` avoids the
     club `C ∩ D`,
   - contains `∅` (`isNonStationary_empty`),
   - proper: the whole space is **not** nonstationary (`isStationary_univ`), so the
     dual club filter does not contain `∅`.
5. **Duality** — `isStationary_iff_not_isNonStationary`: a set is stationary iff it
   is not in the nonstationary ideal. This is the precise sense in which
   "stationary = not in the dual ideal".

## References
- Jech, T. (2003). *Set Theory*. Springer. §8 (Stationary Sets), Theorem 8.3
  (intersection of two clubs is a club) and the club filter / nonstationary ideal.
- Kunen, K. (2011). *Set Theory*. College Publications. Ch. II §6.
-/

import Mathlib
import Proofs.CantorDiagonalizationOQ02OQ03OQ02

namespace FodorLemma

open Cardinal Order Ordinal Set

-- ============================================================================
-- § 1. The whole space is a club (the top of the club filter)
-- ============================================================================

/-- `Set.univ` is a club below any regular cardinal: it is trivially closed, and it
    is unbounded because `κ.ord` is a limit ordinal (so `α + 1 < κ.ord`). -/
theorem isClub_univ {κ : Cardinal.{u}} (hκ : κ.IsRegular) :
    IsClub κ (Set.univ : Set Ordinal.{u}) := by
  have hκlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_le
  refine ⟨?_, ?_⟩
  · intro α hα
    exact ⟨α + 1, Set.mem_univ _, lt_succ α, hκlim.succ_lt hα⟩
  · intro γ _ _
    exact Set.mem_univ _

-- ============================================================================
-- § 2. Intersection of two clubs is closed (easy part)
-- ============================================================================

/-- The intersection of two closed sets is closed: cofinality in `C ∩ D` gives
    cofinality in each of `C` and `D` separately. -/
theorem inter_isClosedBelow {κ : Cardinal.{u}} {C D : Set Ordinal.{u}}
    (hC : IsClosedBelow κ C) (hD : IsClosedBelow κ D) :
    IsClosedBelow κ (C ∩ D) := by
  intro γ hγ hcof
  refine ⟨hC γ hγ ?_, hD γ hγ ?_⟩
  · intro α hα
    obtain ⟨δ, hδ, h1, h2⟩ := hcof α hα
    exact ⟨δ, hδ.1, h1, h2⟩
  · intro α hα
    obtain ⟨δ, hδ, h1, h2⟩ := hcof α hα
    exact ⟨δ, hδ.2, h1, h2⟩

-- ============================================================================
-- § 3. Intersection of two clubs is unbounded (the genuine content)
-- ============================================================================

/-- **Theorem (unbounded part):** the intersection of two clubs is unbounded.

    Given `α₀ < κ.ord`, interleave the two clubs into one ω-chain:
    starting above `α₀`, repeatedly take an element `c ∈ C` above the current point,
    then an element `d ∈ D` above `c`, and continue from `d`. This produces
    `α₀ < c₀ < d₀ < c₁ < d₁ < ⋯` with the `cₙ ∈ C` and `dₙ ∈ D` both cofinal below
    the supremum `γ = ⨆ n, sₙ`. Regularity bounds `γ < κ.ord`, and closedness of
    each club forces `γ ∈ C` and `γ ∈ D`. -/
theorem inter_isUnbounded {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {C D : Set Ordinal.{u}} (hC : IsClub κ C) (hD : IsClub κ D) :
    IsUnboundedBelow κ (C ∩ D) := by
  intro α₀ hα₀
  classical
  have hκlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_le
  -- C is unbounded: from any δ < κ.ord pick an element of C strictly above δ.
  have pickC : ∀ δ, δ < κ.ord → ∃ γ ∈ C, δ < γ ∧ γ < κ.ord := fun δ hδ => hC.1 δ hδ
  have pickD : ∀ δ, δ < κ.ord → ∃ γ ∈ D, δ < γ ∧ γ < κ.ord := fun δ hδ => hD.1 δ hδ
  -- The C-element above `t.val`, and its three properties.
  let cElt : { α : Ordinal.{u} // α < κ.ord } → Ordinal.{u} :=
    fun t => (pickC t.val t.prop).choose
  have cElt_mem : ∀ t, cElt t ∈ C := fun t => (pickC t.val t.prop).choose_spec.1
  have cElt_gt : ∀ t, t.val < cElt t := fun t => (pickC t.val t.prop).choose_spec.2.1
  have cElt_lt : ∀ t, cElt t < κ.ord := fun t => (pickC t.val t.prop).choose_spec.2.2
  -- The D-element above `cElt t`, and its three properties.
  let dElt : { α : Ordinal.{u} // α < κ.ord } → Ordinal.{u} :=
    fun t => (pickD (cElt t) (cElt_lt t)).choose
  have dElt_mem : ∀ t, dElt t ∈ D := fun t => (pickD (cElt t) (cElt_lt t)).choose_spec.1
  have dElt_gt : ∀ t, cElt t < dElt t := fun t => (pickD (cElt t) (cElt_lt t)).choose_spec.2.1
  have dElt_lt : ∀ t, dElt t < κ.ord := fun t => (pickD (cElt t) (cElt_lt t)).choose_spec.2.2
  -- One step: t ↦ ⟨dElt t, _⟩.  The chain of d's, carrying the < κ.ord proof.
  let step : { α : Ordinal.{u} // α < κ.ord } → { α : Ordinal.{u} // α < κ.ord } :=
    fun t => ⟨dElt t, dElt_lt t⟩
  let seq : ℕ → { α : Ordinal.{u} // α < κ.ord } :=
    Nat.rec ⟨α₀ + 1, hκlim.succ_lt hα₀⟩ fun _ prev => step prev
  let s : ℕ → Ordinal.{u} := fun n => (seq n).val
  have hs_lt : ∀ n, s n < κ.ord := fun n => (seq n).prop
  -- Key defeq: s (n+1) = dElt (seq n), and cElt (seq n) sits strictly between.
  have hcGt : ∀ n, s n < cElt (seq n) := fun n => cElt_gt (seq n)
  have hcNext : ∀ n, cElt (seq n) < s (n + 1) := fun n => dElt_gt (seq n)
  have hs_inc : ∀ n, s n < s (n + 1) := fun n => lt_trans (hcGt n) (hcNext n)
  -- The supremum γ.
  let γ : Ordinal.{u} := iSup s
  have hγ_lt : γ < κ.ord := iSup_lt_ord_lift_of_isRegular hκ hκ_unc hs_lt
  have hγ_gt : α₀ < γ := lt_of_lt_of_le (lt_succ α₀) (Ordinal.le_iSup s 0)
  -- A cofinality helper: every p < γ is below some s n.
  have cof : ∀ p, p < γ → ∃ n, p < s n := by
    intro p hp
    by_contra h
    push_neg at h
    exact absurd (Ordinal.iSup_le fun n => h n) (not_le.mpr hp)
  -- γ ∈ C: the cElt's are in C and cofinal below γ, so closedness gives γ ∈ C.
  have hγC : γ ∈ C := by
    apply hC.2 γ hγ_lt
    intro p hp
    obtain ⟨n, hn⟩ := cof p hp
    refine ⟨cElt (seq n), cElt_mem (seq n), lt_trans hn (hcGt n), ?_⟩
    exact lt_of_lt_of_le (hcNext n) (Ordinal.le_iSup s (n + 1))
  -- γ ∈ D: the s (n+1) = dElt (seq n) are in D and cofinal below γ.
  have hγD : γ ∈ D := by
    apply hD.2 γ hγ_lt
    intro p hp
    obtain ⟨n, hn⟩ := cof p hp
    refine ⟨s (n + 1), dElt_mem (seq n), lt_trans hn (hs_inc n), ?_⟩
    exact lt_of_lt_of_le (hs_inc (n + 1)) (Ordinal.le_iSup s (n + 2))
  exact ⟨γ, ⟨hγC, hγD⟩, hγ_gt, hγ_lt⟩

/-- **The club filter is closed under binary intersection.** -/
theorem inter_isClub {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {C D : Set Ordinal.{u}} (hC : IsClub κ C) (hD : IsClub κ D) :
    IsClub κ (C ∩ D) :=
  ⟨inter_isUnbounded hκ hκ_unc hC hD, inter_isClosedBelow hC.2 hD.2⟩

-- ============================================================================
-- § 4. Finite intersection of clubs is a club (the filter property)
-- ============================================================================

/-- **Clubs are closed under finite intersection.** For any `Finset` `t` of indices
    with `C i` a club for each `i ∈ t`, the intersection `⋂ i ∈ t, C i` is a club.
    This is the defining closure property of the club filter `Club(κ)`. -/
theorem isClub_biInter {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {ι : Type*} [DecidableEq ι] (t : Finset ι) {C : ι → Set Ordinal.{u}}
    (hC : ∀ i ∈ t, IsClub κ (C i)) :
    IsClub κ (⋂ i ∈ t, C i) := by
  induction t using Finset.induction with
  | empty => simpa using isClub_univ hκ
  | insert a s ha ih =>
      rw [Finset.set_biInter_insert]
      have hCa : IsClub κ (C a) := hC a (Finset.mem_insert_self a s)
      have hCs : ∀ i ∈ s, IsClub κ (C i) := fun i hi =>
        hC i (Finset.mem_insert_of_mem hi)
      exact inter_isClub hκ hκ_unc hCa (ih hCs)

-- ============================================================================
-- § 5. The nonstationary ideal (the dual ideal of the club filter)
-- ============================================================================

/-- A set `S` is **nonstationary** if it is disjoint from some club. The
    nonstationary sets form the dual ideal `NS(κ)` of the club filter. -/
def IsNonStationary (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  ∃ C, IsClub κ C ∧ ∀ α ∈ S, α ∉ C

/-- **Duality:** `S` is stationary iff it is **not** nonstationary. This is the exact
    sense in which the stationary sets are the sets not in the dual ideal. -/
theorem isStationary_iff_not_isNonStationary {κ : Cardinal.{u}} {S : Set Ordinal.{u}} :
    IsStationary κ S ↔ ¬ IsNonStationary κ S := by
  constructor
  · rintro h ⟨C, hC, hdisj⟩
    obtain ⟨α, hαS, hαC⟩ := h C hC
    exact hdisj α hαS hαC
  · intro h
    by_contra hns
    exact h (not_isStationary_iff.mp hns)

/-- The nonstationary ideal is **downward closed**: a subset of a nonstationary set is
    nonstationary (the same avoiding club works). -/
theorem isNonStationary_subset {κ : Cardinal.{u}} {S T : Set Ordinal.{u}}
    (hT : IsNonStationary κ T) (hST : S ⊆ T) : IsNonStationary κ S := by
  obtain ⟨C, hC, hdisj⟩ := hT
  exact ⟨C, hC, fun α hα => hdisj α (hST hα)⟩

/-- The nonstationary ideal is **closed under binary union**. This is where the club
    filter's intersection property is used: if `S` avoids the club `C` and `T` avoids
    the club `D`, then `S ∪ T` avoids the club `C ∩ D`. -/
theorem isNonStationary_union {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S T : Set Ordinal.{u}} (hS : IsNonStationary κ S) (hT : IsNonStationary κ T) :
    IsNonStationary κ (S ∪ T) := by
  obtain ⟨C, hC, hSdisj⟩ := hS
  obtain ⟨D, hD, hTdisj⟩ := hT
  refine ⟨C ∩ D, inter_isClub hκ hκ_unc hC hD, ?_⟩
  rintro α (hαS | hαT) ⟨hαC, hαD⟩
  · exact hSdisj α hαS hαC
  · exact hTdisj α hαT hαD

/-- The empty set is nonstationary (it belongs to every ideal). -/
theorem isNonStationary_empty {κ : Cardinal.{u}} (hκ : κ.IsRegular) :
    IsNonStationary κ (∅ : Set Ordinal.{u}) :=
  ⟨Set.univ, isClub_univ hκ, fun α hα => absurd hα (Set.notMem_empty α)⟩

/-- **Properness of the filter / ideal:** the whole space is stationary, hence **not**
    nonstationary. Equivalently, `∅` is not in the club filter: the club filter is a
    proper filter. The witness is any club's unboundedness at `0 < κ.ord`. -/
theorem isStationary_univ {κ : Cardinal.{u}} (hκ : κ.IsRegular) :
    IsStationary κ (Set.univ : Set Ordinal.{u}) := by
  have h0 : (0 : Ordinal.{u}) < κ.ord := by
    have hω : Ordinal.omega0 ≤ κ.ord := by
      rw [← Cardinal.ord_aleph0]
      exact Cardinal.ord_le_ord.mpr hκ.aleph0_le
    exact lt_of_lt_of_le Ordinal.omega0_pos hω
  intro C hC
  obtain ⟨β, hβC, _, _⟩ := hC.1 0 h0
  exact ⟨β, Set.mem_univ _, hβC⟩

end FodorLemma
