/-
Fodor's Pressing-Down Lemma (Fodor 1956)

For any regular uncountable cardinal κ, any regressive function f : S → κ.ord
on a stationary set S ⊆ κ.ord (consisting of positive ordinals) is constant
on some stationary subset.

**Mathematical Context**

This is one of the fundamental combinatorial lemmas of set theory. References:
- Fodor (1956): "Eine Bemerkung zur Theorie der regressiven Funktionen"
- Jech, *Set Theory* (2003), Theorem 8.7
- Kunen, *Set Theory* (2011), Theorem II.6.15

**Infrastructure Built Here** (not in Mathlib as of 2026-04):
- `IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow`
- `diagInter`: diagonal intersection
- `diagInter_isClosedBelow`: closed part of diagonal intersection lemma (0 sorries)
- `fodor`: Fodor's pressing-down lemma (1 sorry in diagonal intersection unboundedness)

**Proof Strategy (Diagonal Intersection)**

  Δ_{β<κ.ord}(f β) = {γ < κ.ord | ∀ β < γ, γ ∈ f β}

is a club when each f β is a club (key lemma, 1 sorry for the unbounded part).
Fodor follows by contradiction: pick clubs avoiding each fiber, form their diagonal
intersection D, which meets S at some γ. Then γ ∈ C_{f γ} by regressiveness,
contradicting that C_{f γ} avoids γ.
-/

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Tactic

namespace FodorPressingDown

open Cardinal Order Ordinal Set

-- ══════════════════════════════════════════════════════════════════
-- § Part I: Club and Stationary Sets
-- ══════════════════════════════════════════════════════════════════

/-- A set S is unbounded below ordinal o. -/
def IsUnboundedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ α < o, ∃ β ∈ S, α < β ∧ β < o

/-- A club (closed unbounded) set below ordinal o.
    We require S ⊆ Iio o so that club members are definitionally below o. -/
structure IsClubBelow (S : Set Ordinal) (o : Ordinal) : Prop where
  subset_Iio : S ⊆ Iio o
  closed : IsClosedBelow S o
  unbounded : IsUnboundedBelow S o

/-- A set S is stationary below o if it meets every club below o. -/
def IsStationaryBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty

theorem IsClubBelow.mem_lt {S : Set Ordinal} {o : Ordinal}
    (hS : IsClubBelow S o) {α : Ordinal} (hα : α ∈ S) : α < o :=
  hS.subset_Iio hα

theorem IsClubBelow.mem_of_isAcc {S : Set Ordinal} {o : Ordinal}
    (hS : IsClubBelow S o) {α : Ordinal} (hα : α < o) (hAcc : α.IsAcc S) : α ∈ S :=
  hS.closed.forall_lt α hα hAcc

/-- Iio o is a club when o is a limit ordinal. -/
theorem isClubBelow_Iio_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) :
    IsClubBelow (Iio o) o where
  subset_Iio := fun _ h => h
  closed := by
    rw [isClosedBelow_iff]
    intro p pltq _hacc
    exact pltq
  unbounded := fun α hα => by
    have h1 : α + 1 < o := ho.succ_lt hα
    exact ⟨α + 1, h1, lt_add_one α, h1⟩

-- ══════════════════════════════════════════════════════════════════
-- § Part II: Diagonal Intersection
-- ══════════════════════════════════════════════════════════════════

/-- Diagonal intersection: {γ < o | ∀ β < γ, γ ∈ f β} -/
def diagInter (f : Ordinal → Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {γ | γ < o ∧ ∀ β, β < γ → γ ∈ f β}

@[simp]
theorem mem_diagInter {f : Ordinal → Set Ordinal} {o γ : Ordinal} :
    γ ∈ diagInter f o ↔ γ < o ∧ ∀ β < γ, γ ∈ f β := Iff.rfl

theorem diagInter_subset_Iio (f : Ordinal → Set Ordinal) (o : Ordinal) :
    diagInter f o ⊆ Iio o :=
  fun _ h => h.1

-- ══════════════════════════════════════════════════════════════════
-- § Part III: Diagonal Intersection of Clubs is a Club
-- ══════════════════════════════════════════════════════════════════

/-- **Diagonal Intersection is Closed** (0 sorries).

    Proof: Given γ < o an acc point of Δ(f β),
    for each β < γ and each p < γ, pick δ ∈ Δ ∩ (max p β, γ).
    Then β < δ → δ ∈ f β, so f β ∩ (p,γ) ≠ ∅.
    Hence γ is an acc point of f β → γ ∈ f β (by closure). -/
theorem diagInter_isClosedBelow {f : Ordinal → Set Ordinal} {o : Ordinal}
    (hf : ∀ β < o, IsClubBelow (f β) o) : IsClosedBelow (diagInter f o) o := by
  rw [isClosedBelow_iff]
  intro γ γlto γAcc
  simp only [mem_diagInter]
  refine ⟨γlto, fun β βltγ => ?_⟩
  apply (hf β (βltγ.trans γlto)).closed.forall_lt γ γlto
  rw [isAcc_iff]
  refine ⟨γAcc.pos.ne', fun p pltγ => ?_⟩
  -- max p β < γ since both p < γ and β < γ
  obtain ⟨δ, hδ_mem⟩ := γAcc.forall_lt (max p β) (max_lt pltγ βltγ)
  -- hδ_mem : δ ∈ diagInter f o ∩ Ioo (max p β) γ
  simp only [mem_inter_iff, mem_diagInter, mem_Ioo] at hδ_mem
  obtain ⟨⟨_, hδ_mem2⟩, hδ_lo, hδ_hi⟩ := hδ_mem
  -- β < δ since β ≤ max p β < δ
  have hβδ : β < δ := lt_of_le_of_lt (le_max_right p β) hδ_lo
  exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt (le_max_left p β) hδ_lo, hδ_hi⟩

/-- **Diagonal Intersection is Unbounded** (1 sorry).

    **Complete Proof Sketch** (zipper construction):
    Given α₀ < κ.ord, inductively build α₀ < α₁ < α₂ < ... where
      α_{n+1} ∈ ⋂_{β ≤ α_n} f(β), α_{n+1} > α_n.
    This is possible: ⋂_{β ≤ α_n} f(β) is an intersection of ≤ card(α_n)+1 < κ many clubs
    (since α_n < κ.ord ↔ card(α_n) < κ); this intersection is a club by regularity.

    γ = iSup α_n < κ.ord (by `iSup_lt_ord_of_isRegular`, ℵ₀ < κ, ω-indexed sequence).
    γ ∈ f β for each β < γ: find n with β ≤ α_n; then {α_{n+1}, α_{n+2}, ...} ⊆ f β
    converges to γ; by closure γ ∈ f β. Hence γ ∈ diagInter f κ.ord.

    Missing formalization: "⋂_{β ≤ α_n} f(β) is unbounded" (induction on # clubs).
    Full proof would use `Ordinal.nfpFamily` from Cofinality.lean. -/
theorem diagInter_isUnboundedBelow {f : Ordinal → Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hf : ∀ β < κ.ord, IsClubBelow (f β) κ.ord) :
    IsUnboundedBelow (diagInter f κ.ord) κ.ord := by
  sorry

/-- **Diagonal Intersection Theorem**: diagonal intersection of clubs is a club
    (1 sorry in the unbounded part). -/
theorem diagInter_isClubBelow {f : Ordinal → Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hf : ∀ β < κ.ord, IsClubBelow (f β) κ.ord) :
    IsClubBelow (diagInter f κ.ord) κ.ord where
  subset_Iio := diagInter_subset_Iio f κ.ord
  closed := diagInter_isClosedBelow hf
  unbounded := diagInter_isUnboundedBelow hκ hκ_unc hf

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: Fodor's Pressing-Down Lemma
-- ══════════════════════════════════════════════════════════════════

/-- **Fodor's Pressing-Down Lemma** (Fodor 1956):

    For regular uncountable κ, if S ⊆ κ.ord \ {0} is stationary and
    f is regressive on S (f α < α for all α ∈ S, with f α ∈ S' ⊆ κ.ord),
    then ∃ c < κ.ord such that {α ∈ S : f α = c} is stationary.

    1 sorry (diagonal intersection unboundedness, see above). -/
theorem fodor {κ : Cardinal.{0}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord)
    (hS_pos : ∀ α ∈ S, 0 < α)
    {f : Ordinal → Ordinal}
    (hf_lt : ∀ α ∈ S, f α < κ.ord)
    (hf_reg : ∀ α ∈ S, f α < α) :
    ∃ c < κ.ord, IsStationaryBelow (S ∩ f ⁻¹' {c}) κ.ord := by
  by_contra hcontra
  push_neg at hcontra
  -- For each c < κ.ord, the fiber is non-stationary → choose a club Cₖ avoiding it
  have hclub : ∀ c, c < κ.ord → ∃ C : Set Ordinal,
      IsClubBelow C κ.ord ∧ (S ∩ f ⁻¹' {c} ∩ C) = ∅ := by
    intro c hc
    have hnot : ¬IsStationaryBelow (S ∩ f ⁻¹' {c}) κ.ord := hcontra c hc
    rw [IsStationaryBelow, not_forall] at hnot
    push_neg at hnot
    obtain ⟨C, hC_club, hC_not⟩ := hnot
    exact ⟨C, hC_club, hC_not⟩
  -- Uniformly select Cₖ for each c < κ.ord using Classical.choice
  let pickC : ∀ c, c < κ.ord → Set Ordinal := fun c hc =>
    Classical.choose (hclub c hc)
  have pickC_club : ∀ c (hc : c < κ.ord), IsClubBelow (pickC c hc) κ.ord :=
    fun c hc => (Classical.choose_spec (hclub c hc)).1
  have pickC_avoid : ∀ c (hc : c < κ.ord), (S ∩ f ⁻¹' {c} ∩ pickC c hc) = ∅ :=
    fun c hc => (Classical.choose_spec (hclub c hc)).2
  -- Define F β = Cβ for β < κ.ord, else Iio κ.ord (any club suffices as default)
  let κlim := isSuccLimit_ord hκ.aleph0_le
  let F : Ordinal → Set Ordinal := fun c =>
    if h : c < κ.ord then pickC c h else Iio κ.ord
  have hF_club : ∀ β < κ.ord, IsClubBelow (F β) κ.ord := by
    intro β hβ
    simp only [F, dif_pos hβ]
    exact pickC_club β hβ
  -- D = diagInter F κ.ord is a club
  have hD_club : IsClubBelow (diagInter F κ.ord) κ.ord :=
    diagInter_isClubBelow hκ hκ_unc hF_club
  -- S meets D: pick γ ∈ S ∩ diagInter F κ.ord
  obtain ⟨γ, hγS, hγD⟩ := hS (diagInter F κ.ord) hD_club
  rw [mem_diagInter] at hγD
  -- γ ∈ κ.ord from hγD.1 (diagInter elements are < κ.ord by definition)
  have hγlt : γ < κ.ord := hγD.1
  -- f γ < γ < κ.ord
  have hfγ : f γ < γ := hf_reg γ hγS
  have hfγlt : f γ < κ.ord := hf_lt γ hγS
  -- γ ∈ F (f γ) since γ ∈ diagInter and f γ < γ
  have hγ_in_F : γ ∈ F (f γ) := hγD.2 (f γ) hfγ
  -- F (f γ) = pickC (f γ) hfγlt
  have hF_eq : γ ∈ pickC (f γ) hfγlt := by
    have hFval : F (f γ) = pickC (f γ) hfγlt := dif_pos hfγlt
    exact hFval ▸ hγ_in_F
  -- γ ∈ S ∩ f⁻¹{f γ} ∩ pickC (f γ) hfγlt — but this set is empty!
  have hγ_in_avoided : γ ∈ S ∩ f ⁻¹' {f γ} ∩ pickC (f γ) hfγlt :=
    ⟨⟨hγS, rfl⟩, hF_eq⟩
  rw [pickC_avoid (f γ) hfγlt] at hγ_in_avoided
  exact absurd hγ_in_avoided (Set.notMem_empty _)

-- ══════════════════════════════════════════════════════════════════
-- § Part V: Specializations
-- ══════════════════════════════════════════════════════════════════

/-- Fodor's lemma for ω₁ = (ℵ₁).ord. -/
theorem fodor_aleph1
    {S : Set Ordinal.{0}} (hS : IsStationaryBelow S (ℵ₁).ord)
    (hS_pos : ∀ α ∈ S, 0 < α)
    {f : Ordinal.{0} → Ordinal.{0}}
    (hf_lt : ∀ α ∈ S, f α < (ℵ₁).ord)
    (hf_reg : ∀ α ∈ S, f α < α) :
    ∃ c < (ℵ₁).ord, IsStationaryBelow (S ∩ f ⁻¹' {c}) (ℵ₁).ord :=
  fodor isRegular_aleph_one aleph0_lt_aleph_one hS hS_pos hf_lt hf_reg

-- ══════════════════════════════════════════════════════════════════
-- § Part VI: Key Subsidiary Lemmas for Future Work
-- ══════════════════════════════════════════════════════════════════

/-- Every stationary set is nonempty. -/
theorem IsStationaryBelow.nonempty {S : Set Ordinal} {o : Ordinal}
    (hS : IsStationaryBelow S o) (ho : IsSuccLimit o) : S.Nonempty := by
  have hC : IsClubBelow (Iio o) o := isClubBelow_Iio_of_isSuccLimit ho
  obtain ⟨γ, hγS, _⟩ := hS (Iio o) hC
  exact ⟨γ, hγS⟩

/-- Stationary sets are closed under subelements in the following sense:
    if T ⊆ S, S is stationary, and every club meeting S meets T,
    then T is stationary. -/
theorem IsStationaryBelow.of_subset {S T : Set Ordinal} {o : Ordinal}
    (hS : IsStationaryBelow S o) (hTS : T ⊆ S)
    (hMeet : ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty → (T ∩ C).Nonempty) :
    IsStationaryBelow T o := by
  intro C hC
  exact hMeet C hC (hS C hC)

-- ══════════════════════════════════════════════════════════════════
-- § Summary and Open Next Steps
-- ══════════════════════════════════════════════════════════════════

/-
**Fodor's Pressing-Down Lemma — Formalization Summary**

New infrastructure built (not in Mathlib):
  - `IsClubBelow S o` (S ⊆ Iio o, closed, unbounded)
  - `IsStationaryBelow S o` (meets every club)
  - `diagInter f o` (diagonal intersection)

Key results:
  ✓ `isClubBelow_Iio_of_isSuccLimit`: Iio o is a club at limit ordinals
  ✓ `diagInter_isClosedBelow`: diagonal intersection of clubs is closed (0 sorries)
  ✓ `fodor`: Fodor's pressing-down lemma (1 sorry in diagInter_isUnboundedBelow)
  ✓ `fodor_aleph1`: specialization to ω₁

Sorries remaining (1):
  1. `diagInter_isUnboundedBelow`: the "zipper" construction
     → Proof sketch given with full mathematical justification
     → Next step: use `Ordinal.nfpFamily` to iterate the "next element" functions
     → Key lemma needed: "finite intersection of clubs is a club" (easy base case)

Connection to parent (CantorDiagonalizationOQ02OQ03):
  The parent proves that for regular uncountable κ, ordinals below κ.ord cannot
  be enumerated by a < κ-indexed sequence. This follows from Fodor: any such
  enumeration would give an injective regressive function on ordinals < κ.ord,
  which Fodor prevents.

This formalization contributes:
  - First Lean 4 treatment of club sets in the context of regular cardinals
  - The "closed" part of the diagonal intersection lemma (complete, 0 sorries)
  - A clean proof architecture for Fodor's lemma
  - Infrastructure for stationary set theory in Lean 4
-/

end FodorPressingDown
