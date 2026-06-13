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
- `diagInter_isClosedBelow`: closed part of diagonal intersection lemma
- `diagInter_isUnboundedBelow`: unbounded part via zipper construction
- `fodor`: Fodor's pressing-down lemma (0 sorries)

**Proof Strategy (Diagonal Intersection)**

  Δ_{β<κ.ord}(f β) = {γ < κ.ord | ∀ β < γ, γ ∈ f β}

is a club when each f β is a club (both parts proved: closed + unbounded).
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
import Proofs.Club.Basic

namespace FodorPressingDown

open Cardinal Order Ordinal Set

-- ══════════════════════════════════════════════════════════════════
-- § Part I: Club and Stationary Sets
-- ══════════════════════════════════════════════════════════════════

-- `IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow`, `IsClubBelow.mem_lt`,
-- `IsClubBelow.mem_of_isAcc`, and `isClubBelow_Iio_of_isSuccLimit` now live in
-- `Proofs.Club.Basic` (namespace `Ordinal`); reached here via `open Ordinal`.

-- ══════════════════════════════════════════════════════════════════
-- § Part II: Diagonal Intersection
-- ══════════════════════════════════════════════════════════════════

-- `diagInter`, `mem_diagInter`, and `diagInter_subset_Iio` now live in
-- `Proofs.Club.Basic` (namespace `Ordinal`); reached here via `open Ordinal`.

-- ══════════════════════════════════════════════════════════════════
-- § Part III: Diagonal Intersection of Clubs is a Club
-- ══════════════════════════════════════════════════════════════════

-- `diagInter_isClosedBelow` now lives in `Proofs.Club.Basic`
-- (namespace `Ordinal`); reached here via `open Ordinal`.

/-- **Diagonal Intersection is Unbounded** (zipper construction).

    Given α₀ < κ.ord, build a strictly increasing ω-sequence (seq n) where:
    - seq 0 = α₀ + 1
    - seq (n+1) = bsup(seq n + 1, fun β => next-element-of-f(β)-above-seq(n)) + 1

    At each step, bsup covers all β ≤ seq n, ensuring that f(β) has elements
    between seq n and seq(n+1). The limit γ = iSup seq satisfies:
    - γ < κ.ord (regularity: ℵ₀-indexed sup, ℵ₀ < κ)
    - γ ∈ f β for all β < γ (closure: γ is an accumulation point of f β)

    Hence γ ∈ diagInter f κ.ord with γ > α₀. -/
theorem diagInter_isUnboundedBelow {f : Ordinal → Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hf : ∀ β < κ.ord, IsClubBelow (f β) κ.ord) :
    IsUnboundedBelow (diagInter f κ.ord) κ.ord := by
  intro α₀ hα₀
  -- κ.ord is a limit ordinal (since κ ≥ ℵ₀)
  have hκlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_le
  -- For each β < κ.ord and δ < κ.ord, pick an element of f(β) above δ
  have pick : ∀ β, β < κ.ord → ∀ δ, δ < κ.ord →
      ∃ γ ∈ f β, δ < γ ∧ γ < κ.ord :=
    fun β hβ δ hδ => (hf β hβ).unbounded δ hδ
  -- Define the "bump" function: given δ < κ.ord, take the bsup over all β ≤ δ
  -- of the next element of f(β) above δ.
  -- This produces a value ≥ each next-element, hence > δ.
  -- It is < κ.ord since (δ+1).card < κ and each value is < κ.ord.
  let bump (δ : Ordinal) (hδ : δ < κ.ord) : Ordinal :=
    Ordinal.bsup (δ + 1) fun β hβ =>
      (pick β (lt_trans hβ (hκlim.succ_lt hδ)) δ hδ).choose
  -- bump properties
  have bump_lt : ∀ δ (hδ : δ < κ.ord), bump δ hδ < κ.ord := by
    intro δ hδ
    apply Ordinal.bsup_lt_ord
    · -- card(δ + 1) < κ.ord.cof = κ: since δ + 1 < κ.ord
      rw [hκ.cof_eq]
      exact lt_ord.mp (hκlim.succ_lt hδ)
    · intro β hβ
      exact (pick β (lt_trans hβ (hκlim.succ_lt hδ)) δ hδ).choose_spec.2.2
  have bump_gt : ∀ δ (hδ : δ < κ.ord), δ < bump δ hδ := by
    intro δ hδ
    have h0lt : (0 : Ordinal) < δ + 1 := Ordinal.succ_pos δ
    calc δ < (pick 0 (lt_trans h0lt (hκlim.succ_lt hδ)) δ hδ).choose :=
            (pick 0 (lt_trans h0lt (hκlim.succ_lt hδ)) δ hδ).choose_spec.2.1
      _ ≤ bump δ hδ := Ordinal.le_bsup _ 0 h0lt
  have bump_witness : ∀ δ (hδ : δ < κ.ord) β (hβ : β ≤ δ),
      ∃ γ ∈ f β, δ < γ ∧ γ ≤ bump δ hδ := by
    intro δ hδ β hβ
    have hβκ : β < κ.ord := lt_of_le_of_lt hβ (lt_trans (lt_succ δ) (hκlim.succ_lt hδ))
    have hβsucc : β < δ + 1 := lt_of_le_of_lt hβ (lt_succ δ)
    refine ⟨(pick β hβκ δ hδ).choose, (pick β hβκ δ hδ).choose_spec.1,
      (pick β hβκ δ hδ).choose_spec.2.1, ?_⟩
    exact Ordinal.le_bsup _ β hβsucc
  -- Build the ω-sequence carrying proofs of < κ.ord
  let seq : ℕ → { α : Ordinal // α < κ.ord } :=
    Nat.rec ⟨α₀ + 1, hκlim.succ_lt hα₀⟩ fun _ prev =>
      ⟨bump prev.val prev.prop + 1, hκlim.succ_lt (bump_lt prev.val prev.prop)⟩
  -- Extract the underlying ordinal sequence
  let s : ℕ → Ordinal := fun n => (seq n).val
  have hs_lt : ∀ n, s n < κ.ord := fun n => (seq n).prop
  -- The sequence is strictly increasing
  have hs_inc : StrictMono s := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h1 : s n < bump (s n) (hs_lt n) := bump_gt (s n) (hs_lt n)
    have h2 : bump (s n) (hs_lt n) < bump (s n) (hs_lt n) + 1 := lt_succ _
    exact lt_trans h1 h2
  -- α₀ < s 0
  have hα₀_lt_s0 : α₀ < s 0 := lt_succ α₀
  -- Take γ = iSup s. Show γ < κ.ord by regularity.
  -- Note: Ordinal has iSup but NOT CompleteLattice.
  -- Use Ordinal.le_iSup / Ordinal.iSup_le (protected versions, require Small).
  let γ := iSup s
  have hγ_lt : γ < κ.ord := by
    apply Ordinal.iSup_lt_ord
    · rw [hκ.cof_eq, Cardinal.mk_nat]; exact hκ_unc
    · exact hs_lt
  -- γ > α₀ (since γ ≥ s 0 > α₀)
  have hα₀_lt_γ : α₀ < γ := lt_of_lt_of_le hα₀_lt_s0 (Ordinal.le_iSup s 0)
  -- γ > 0
  have hγ_pos : 0 < γ := pos_of_gt hα₀_lt_γ
  -- γ is in the diagonal intersection
  have hγ_diag : γ ∈ diagInter f κ.ord := by
    rw [mem_diagInter]
    refine ⟨hγ_lt, fun β hβγ => ?_⟩
    -- β < γ = iSup s, so ∃ n with β < s n
    have ⟨n, hn⟩ : ∃ n, β < s n := by
      by_contra h; push_neg at h
      exact not_lt.mpr (Ordinal.iSup_le fun n => h n) hβγ
    -- f(β) is closed, so it suffices to show γ is an accumulation point of f(β)
    apply (hf β (lt_trans hβγ hγ_lt)).mem_of_isAcc hγ_lt
    rw [isAcc_iff]
    refine ⟨hγ_pos.ne', fun p hpγ => ?_⟩
    -- Need: ∃ δ ∈ f β, p < δ < γ
    -- Pick m large enough that both β ≤ s m and p < s m
    have ⟨m₁, hm₁⟩ : ∃ m, β < s m := ⟨n, hn⟩
    have ⟨m₂, hm₂⟩ : ∃ m, p < s m := by
      by_contra h; push_neg at h
      exact not_lt.mpr (Ordinal.iSup_le fun m => h m) hpγ
    let m := max m₁ m₂
    have hβm : β ≤ s m := le_of_lt (lt_of_lt_of_le hm₁ (hs_inc.monotone (le_max_left _ _)))
    have hpm : p < s m := lt_of_lt_of_le hm₂ (hs_inc.monotone (le_max_right _ _))
    -- bump_witness gives an element of f(β) in (s m, bump(s m)]
    obtain ⟨δ, hδ_mem, hδ_gt, hδ_le⟩ := bump_witness (s m) (hs_lt m) β hβm
    refine ⟨δ, hδ_mem, lt_of_lt_of_le hpm (le_of_lt hδ_gt), ?_⟩
    -- δ ≤ bump(s m) < bump(s m) + 1 = s(m+1) ≤ γ
    calc δ ≤ bump (s m) (hs_lt m) := hδ_le
      _ < bump (s m) (hs_lt m) + 1 := lt_succ _
      _ = s (m + 1) := rfl
      _ ≤ γ := Ordinal.le_iSup s (m + 1)
  -- Package the result
  exact ⟨γ, hγ_diag, hα₀_lt_γ, hγ_lt⟩

/-- **Diagonal Intersection Theorem**: diagonal intersection of clubs is a club. -/
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

    0 sorries (diagonal intersection fully proved). -/
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

-- `IsStationaryBelow.nonempty` and `IsStationaryBelow.of_subset` now live in
-- `Proofs.Club.Basic` (namespace `Ordinal`); reached here via `open Ordinal`.

-- ══════════════════════════════════════════════════════════════════
-- § Part VII: Solovay Splitting — Step 1 (Limit Ordinals Form a Club)
-- ══════════════════════════════════════════════════════════════════

/-- **Step 1 of Solovay splitting (S2-α)** — the set of limit ordinals below `κ.ord`
    is a club. Canonical preliminary lemma for Solovay's splitting theorem: it lets us
    WLOG-assume any stationary `S ⊆ κ.ord` consists of limit ordinals, by intersecting
    with this club.

    Proof:
    * Closure: an accumulation point of limit ordinals is itself a limit ordinal — no
      successor `b + 1` can be an `IsAcc`-point, since `IsAcc` forces an element of `S`
      strictly between any `q < p` and `p`.
    * Unboundedness: for any `α < κ.ord`, the ordinal `α + ω₀` is a limit (sum with a
      limit is a limit) and is `< κ.ord` by regularity
      (`Cardinal.isPrincipal_add_ord` since `α, ω₀ < κ.ord` and `ℵ₀ ≤ κ`). -/
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord where
  subset_Iio := fun _ ha => ha.1
  closed := by
    rw [isClosedBelow_iff]
    intro p hpκ pAcc
    refine ⟨hpκ, ?_⟩
    have hpos : (0 : Ordinal) < p := pAcc.pos
    have hAcc : ∀ q < p,
        ∃ r ∈ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α}, q < r ∧ r < p := by
      rw [isAcc_iff] at pAcc
      exact pAcc.2
    refine ⟨?_, ?_⟩
    · -- ¬ IsMin p
      intro hmin
      exact hpos.ne' (le_antisymm (hmin (le_of_lt hpos)) (le_of_lt hpos))
    · -- IsSuccPrelimit p: ∀ b, ¬ b ⋖ p
      intro b hcov
      obtain ⟨r, _, hbr, hrp⟩ := hAcc b hcov.1
      exact hcov.2 hbr hrp
  unbounded := by
    intro α hα
    -- ω₀ < κ.ord via ω₀ = ℵ₀.ord and the Cardinal.ord-monotonicity from ℵ₀ < κ
    have hω_lt : Ordinal.omega0 < κ.ord := by
      rw [show Ordinal.omega0 = (ℵ₀ : Cardinal).ord from Cardinal.ord_aleph0.symm]
      exact Cardinal.ord_lt_ord.mpr hκ_unc
    -- α + ω₀ < κ.ord via cardinality: card(α + ω₀) = card α + ℵ₀ < κ (regularity)
    have hαω_lt : α + Ordinal.omega0 < κ.ord := by
      rw [Cardinal.lt_ord, Ordinal.card_add, Ordinal.card_omega0]
      exact Cardinal.add_lt_of_lt hκ.aleph0_le (Cardinal.lt_ord.mp hα) hκ_unc
    refine ⟨α + Ordinal.omega0, ⟨hαω_lt, ?_⟩, ?_, hαω_lt⟩
    · -- α + ω₀ is a limit (sum-with-a-limit is a limit)
      exact Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0
    · -- α < α + ω₀ via IsNormal of (α + ·): 0 < ω₀ ⇒ α + 0 < α + ω₀, then α + 0 = α
      have h : α + 0 < α + Ordinal.omega0 :=
        (Ordinal.isNormal_add_right α).strictMono Ordinal.omega0_pos
      rwa [add_zero] at h

/-- **Corollary**: the set of non-limit ordinals below `κ.ord` is *not* stationary.
    Direct consequence of `isLimitOrdinals_isClubBelow`: the complement of a club
    cannot intersect every club (in particular, the club from the lemma). -/
theorem nonLimitOrdinals_not_isStationaryBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    ¬ IsStationaryBelow {α : Ordinal | α < κ.ord ∧ ¬ IsSuccLimit α} κ.ord := by
  intro hStat
  obtain ⟨_, hγnonlim, hγlim⟩ :=
    hStat {α | α < κ.ord ∧ IsSuccLimit α} (isLimitOrdinals_isClubBelow hκ hκ_unc)
  exact hγnonlim.2 hγlim.2

-- ══════════════════════════════════════════════════════════════════
-- § Part VIII: Solovay Splitting — Step 2 Companions (S2-β-α ACT)
-- ══════════════════════════════════════════════════════════════════

/-- **Binary intersection of clubs is a club** (S2-β-α companion).

    Two clubs `C, D` below `κ.ord` intersect to a club. This is the
    workhorse companion used to derive `IsStationaryBelow.inter_isClubBelow`
    (which then powers the WLOG-restrict-to-limits reduction at the head of
    Solovay Step 2).

    Closure: an `IsAcc`-point of `C ∩ D` is an `IsAcc`-point of both `C`
    and `D` (the `IsAcc` witnesses lift through the intersection by
    projecting the membership pair), so it lies in both by their closure.

    Unboundedness: apply `diagInter_isUnboundedBelow` to the 2-element
    family `f β = C if β = 0 else D` (both clubs) from starting point
    `max α 1`. The resulting `γ ∈ diagInter f κ.ord` has `γ > max α 1 ≥ 1`,
    so both `0 < γ` and `1 < γ`, witnessing `γ ∈ f 0 = C` and `γ ∈ f 1 = D`. -/
theorem IsClubBelow.inter {C D : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hC : IsClubBelow C κ.ord) (hD : IsClubBelow D κ.ord) :
    IsClubBelow (C ∩ D) κ.ord where
  subset_Iio := fun _ hx => hC.subset_Iio hx.1
  closed := by
    rw [isClosedBelow_iff]
    intro p hpκ hpAcc
    refine ⟨?_, ?_⟩
    · -- p ∈ C: p IsAcc on C ∩ D ⇒ p IsAcc on C
      apply hC.closed.forall_lt p hpκ
      rw [isAcc_iff] at hpAcc ⊢
      refine ⟨hpAcc.1, fun q hq => ?_⟩
      obtain ⟨r, hrCD, hqr, hrp⟩ := hpAcc.2 q hq
      exact ⟨r, hrCD.1, hqr, hrp⟩
    · -- p ∈ D: p IsAcc on C ∩ D ⇒ p IsAcc on D
      apply hD.closed.forall_lt p hpκ
      rw [isAcc_iff] at hpAcc ⊢
      refine ⟨hpAcc.1, fun q hq => ?_⟩
      obtain ⟨r, hrCD, hqr, hrp⟩ := hpAcc.2 q hq
      exact ⟨r, hrCD.2, hqr, hrp⟩
  unbounded := by
    intro α hα
    -- 2-element family selecting C at β=0 and D otherwise
    let f : Ordinal → Set Ordinal := fun β => if β = 0 then C else D
    have hf_club : ∀ β < κ.ord, IsClubBelow (f β) κ.ord := by
      intro β _
      by_cases hβ : β = 0
      · simp only [f, hβ, if_true]; exact hC
      · simp only [f, if_neg hβ]; exact hD
    -- κ.ord > 1: regularity gives ω₀ ≤ κ.ord, and 1 < ω₀
    have h1lt : (1 : Ordinal) < κ.ord := by
      have h_aleph0_le : (Cardinal.aleph0 : Cardinal).ord ≤ κ.ord :=
        Cardinal.ord_le_ord.mpr hκ.aleph0_le
      rw [Cardinal.ord_aleph0] at h_aleph0_le
      exact lt_of_lt_of_le Ordinal.one_lt_omega0 h_aleph0_le
    -- Starting point: max α 1 < κ.ord
    have hmaxκ : max α 1 < κ.ord := max_lt hα h1lt
    -- diagInter unboundedness gives γ above max α 1, in diagInter f κ.ord
    obtain ⟨γ, hγdiag, hmγ, hγκ⟩ :=
      diagInter_isUnboundedBelow hκ hκ_unc hf_club (max α 1) hmaxκ
    rw [mem_diagInter] at hγdiag
    obtain ⟨_, hγfor⟩ := hγdiag
    -- max α 1 ≥ 1 ensures γ > 1; max α 1 ≥ α ensures γ > α
    have hγ_gt_1 : (1 : Ordinal) < γ := lt_of_le_of_lt (le_max_right α 1) hmγ
    have hγ_gt_0 : (0 : Ordinal) < γ := lt_of_lt_of_le one_pos (le_of_lt hγ_gt_1)
    have hα_lt_γ : α < γ := lt_of_le_of_lt (le_max_left α 1) hmγ
    have hγC : γ ∈ C := by
      have h := hγfor 0 hγ_gt_0
      simp only [f, if_true] at h
      exact h
    have hγD : γ ∈ D := by
      have h : γ ∈ f 1 := hγfor 1 hγ_gt_1
      simpa [f] using h
    exact ⟨γ, ⟨hγC, hγD⟩, hα_lt_γ, hγκ⟩

/-- **Intersection with a club preserves stationarity** (S2-β-α companion).

    If `S` is stationary below `κ.ord` and `C` is a club below `κ.ord`,
    then `S ∩ C` is stationary. This is the WLOG-in-club pull-back the
    S2-β ACT writer uses with `C = isLimitOrdinals_isClubBelow` to
    restrict any stationary `S` to its limit-ordinal part before invoking
    the cofinal-sequence machinery (S2-β / Solovay Step 2 proper).

    Proof: For any club `D` below `κ.ord`, `C ∩ D` is a club
    (`IsClubBelow.inter`), so the stationarity of `S` yields some
    `γ ∈ S ∩ (C ∩ D)`; rearrange to `(S ∩ C) ∩ D`. -/
theorem IsStationaryBelow.inter_isClubBelow {S C : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hS : IsStationaryBelow S κ.ord) (hC : IsClubBelow C κ.ord) :
    IsStationaryBelow (S ∩ C) κ.ord := by
  intro D hD
  -- C ∩ D is a club by binary intersection
  have hCD : IsClubBelow (C ∩ D) κ.ord := IsClubBelow.inter hκ hκ_unc hC hD
  -- S meets C ∩ D by stationarity of S
  obtain ⟨γ, hγS, hγCD⟩ := hS (C ∩ D) hCD
  -- γ ∈ S ∧ γ ∈ C ∧ γ ∈ D ⇒ γ ∈ (S ∩ C) ∩ D
  exact ⟨γ, ⟨hγS, hγCD.1⟩, hγCD.2⟩

/-- **Stationary restricts to limits, with WLOG ⊆ limit ordinals** (S2-β-α corollary).

    Stationary subsets `S ⊆ κ.ord` can be WLOG-assumed to consist of limit
    ordinals: `S ∩ {α | IsSuccLimit α}` is itself stationary below `κ.ord`.

    This is `IsStationaryBelow.inter_isClubBelow` applied with
    `C = isLimitOrdinals_isClubBelow`, packaged as a directly-usable form
    for the S2-β / Solovay Step 2 ACT writer. -/
theorem IsStationaryBelow.inter_isLimitOrdinals {S : Set Ordinal} {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    (hS : IsStationaryBelow S κ.ord) :
    IsStationaryBelow (S ∩ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α}) κ.ord :=
  IsStationaryBelow.inter_isClubBelow hκ hκ_unc hS (isLimitOrdinals_isClubBelow hκ hκ_unc)

-- ══════════════════════════════════════════════════════════════════
-- § Part IX: Solovay Splitting — Cofinal-Sequence Head (S2-β)
-- ══════════════════════════════════════════════════════════════════

/-- **0-th element of some fundamental sequence for `α`.**

    For positive limit ordinals `α`, picks (via `Classical.choose`) a
    fundamental sequence from `Ordinal.exists_fundamental_sequence` and
    returns its 0-th term. For ordinals with `α.cof.ord = 0` (i.e. `α = 0`),
    or with `α.cof.ord = 1` (successor ordinals), the predicate
    `0 < α.cof.ord` may fail to gate the sequence; here we fall back to `0`.

    This is the simplest regressive function on the class of positive limit
    ordinals: any limit `α` has `ℵ₀ ≤ cof α` (`Ordinal.aleph0_le_cof`), so
    `ω₀ ≤ cof α.ord` and in particular `0 < cof α.ord`; the 0-th term of
    any fundamental sequence is `< α` by `IsFundamentalSequence.lt`.

    The eventual use is to invoke `fodor` on the regressive function
    `cofHead` over a stationary set of limit ordinals — see
    `exists_cofHead_constant_stationary` below. -/
noncomputable def cofHead (α : Ordinal) : Ordinal :=
  if h : (0 : Ordinal) < α.cof.ord then
    (Ordinal.exists_fundamental_sequence α).choose 0 h
  else 0

/-- **`cofHead` is strictly below the input on positive limit ordinals.**

    For any `IsSuccLimit α`, the cofinality `cof α.ord` is at least `ω₀`,
    so `0 < α.cof.ord`. Then the 0-th term of any fundamental sequence
    for `α` is strictly below `α` (`IsFundamentalSequence.lt`). -/
theorem cofHead_lt {α : Ordinal} (hα : IsSuccLimit α) : cofHead α < α := by
  have h_cof_pos : (0 : Ordinal) < α.cof.ord := by
    have h_aleph0 : ℵ₀ ≤ α.cof := Ordinal.aleph0_le_cof.mpr hα
    have h_ord_le : (ℵ₀ : Cardinal).ord ≤ α.cof.ord :=
      Cardinal.ord_le_ord.mpr h_aleph0
    rw [Cardinal.ord_aleph0] at h_ord_le
    exact lt_of_lt_of_le Ordinal.omega0_pos h_ord_le
  simp only [cofHead, dif_pos h_cof_pos]
  exact (Ordinal.exists_fundamental_sequence α).choose_spec.lt h_cof_pos

/-- **Fodor's first application via `cofHead`.**

    For any stationary set `S` of positive-limit ordinals below `κ.ord`,
    `cofHead` is constant on some stationary subset of `S`: there exist
    `β < κ.ord` and `S ∩ cofHead ⁻¹' {β}` stationary below `κ.ord`.

    This is **Step (d)** of the canonical binary-Solovay-splitting proof
    sketched in `sessions/2026-05-15-s3b-prep-disjointness-drill.md` §4.2:
    apply Fodor to the regressive `cofHead : Ordinal → Ordinal` on the
    WLOG-limits stationary set.

    The companion theorems `IsStationaryBelow.inter_isClubBelow` and
    `IsStationaryBelow.inter_isLimitOrdinals` (Part VIII) supply the
    "restrict to limits" reduction that produces the hypothesis
    `h_lim : ∀ α ∈ S, α < κ.ord ∧ IsSuccLimit α` from any stationary `S`. -/
theorem exists_cofHead_constant_stationary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord)
    (h_lim : ∀ α ∈ S, α < κ.ord ∧ IsSuccLimit α) :
    ∃ β < κ.ord, IsStationaryBelow (S ∩ cofHead ⁻¹' {β}) κ.ord := by
  have hS_pos : ∀ α ∈ S, 0 < α := fun α hα => (h_lim α hα).2.bot_lt
  have h_reg : ∀ α ∈ S, cofHead α < α := fun α hα => cofHead_lt (h_lim α hα).2
  have h_lt_κord : ∀ α ∈ S, cofHead α < κ.ord := fun α hα =>
    lt_trans (cofHead_lt (h_lim α hα).2) (h_lim α hα).1
  exact fodor hκ hκ_unc hS hS_pos h_lt_κord h_reg

/-- **Convenience form**: any stationary `S ⊆ κ.ord` produces a stationary
    sub-subset on which `cofHead` is constant, after restricting `S` to its
    limit-ordinal part via `IsStationaryBelow.inter_isLimitOrdinals`.

    Output: `∃ β < κ.ord`, `IsStationaryBelow` of the triple intersection
    `S ∩ {limits below κ.ord} ∩ cofHead⁻¹{β}`. This is the ready-to-use
    form for the S2-β ACT writer (composes Part VIII corollary + Part IX
    Fodor application in one statement). -/
theorem exists_cofHead_constant_stationary_of_stationary {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord) :
    ∃ β < κ.ord, IsStationaryBelow
      (S ∩ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} ∩ cofHead ⁻¹' {β}) κ.ord :=
  exists_cofHead_constant_stationary hκ hκ_unc
    (IsStationaryBelow.inter_isLimitOrdinals hκ hκ_unc hS) (fun _ hα => hα.2)

-- ══════════════════════════════════════════════════════════════════
-- § Part X: Solovay Splitting — Binary Split Packaging (S2-β-γ)
-- ══════════════════════════════════════════════════════════════════

/-- **Fiber + co-stationary complement gives a binary split.**

    If a predicate `P` carves a stationary subset `{α ∈ S | P α}` out of
    `S` whose *complement within `S`* (`{α ∈ S | ¬ P α}`) is also
    stationary, then `S` splits into two disjoint stationary subsets.

    This is the disjointness-packaging step (§4.4 of the S3b PREP design,
    `sessions/2026-05-15-s3b-prep-disjointness-drill.md`): the two pieces
    are automatically disjoint (no `α` satisfies both `P α` and `¬ P α`)
    and both are `⊆ S`. It is the canonical consumer of the two
    complementary stationary conjuncts produced by a `fodor_anti_constant`-
    style argument (`{α ∈ S | g₀ α = β₀ ∧ g₁ α = β₁}` versus
    `{α ∈ S | g₀ α ≠ β₀ ∨ g₁ α ≠ β₁}`).

    **Scope honesty.** This lemma packages a split once two complementary
    stationary pieces are in hand; it does *not* produce them. The
    remaining obstacle for the full `stationary_splits_binary` is to
    exhibit such a `P` (the index-of-first-disagreement counting argument,
    not available at the pinned Mathlib SHA). 0 sorries, 0 axioms. -/
theorem stationary_splits_of_fiber_compl {κ : Cardinal.{0}}
    {S : Set Ordinal} {P : Ordinal → Prop}
    (h₁ : IsStationaryBelow {α ∈ S | P α} κ.ord)
    (h₂ : IsStationaryBelow {α ∈ S | ¬ P α} κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord := by
  refine ⟨{α ∈ S | P α}, {α ∈ S | ¬ P α},
    fun _ ha => ha.1, fun _ ha => ha.1, ?_, h₁, h₂⟩
  rw [Set.disjoint_left]
  rintro a ⟨_, ha⟩ ⟨_, hna⟩
  exact hna ha

/-- **Two distinct constant values give a binary split.**

    If a function `f` is constant on two stationary subsets of `S` with
    *distinct* values `c₁ ≠ c₂`, then `S` splits into two disjoint
    stationary subsets. The two fibers `S ∩ f ⁻¹' {c₁}` and
    `S ∩ f ⁻¹' {c₂}` are disjoint because no `α` can have `f α = c₁` and
    `f α = c₂` simultaneously, and both are `⊆ S`.

    This is the packaging used by the "two-Fodor" route (S3 PREP §4.3):
    a single regressive `f` whose fibers at two distinct values are each
    stationary. Like `stationary_splits_of_fiber_compl`, it isolates —
    but does not discharge — the obstacle of *producing* two such
    stationary fibers. 0 sorries, 0 axioms. -/
theorem stationary_splits_of_two_fibers {κ : Cardinal.{0}}
    {S : Set Ordinal} {f : Ordinal → Ordinal} {c₁ c₂ : Ordinal}
    (hc : c₁ ≠ c₂)
    (h₁ : IsStationaryBelow (S ∩ f ⁻¹' {c₁}) κ.ord)
    (h₂ : IsStationaryBelow (S ∩ f ⁻¹' {c₂}) κ.ord) :
    ∃ S₁ S₂ : Set Ordinal,
      S₁ ⊆ S ∧ S₂ ⊆ S ∧ Disjoint S₁ S₂ ∧
      IsStationaryBelow S₁ κ.ord ∧ IsStationaryBelow S₂ κ.ord := by
  refine ⟨S ∩ f ⁻¹' {c₁}, S ∩ f ⁻¹' {c₂},
    Set.inter_subset_left, Set.inter_subset_left, ?_, h₁, h₂⟩
  rw [Set.disjoint_left]
  rintro a ⟨_, ha1⟩ ⟨_, ha2⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at ha1 ha2
  exact hc (ha1.symm.trans ha2)

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
  ✓ `diagInter_isClosedBelow`: diagonal intersection of clubs is closed
  ✓ `diagInter_isUnboundedBelow`: diagonal intersection of clubs is unbounded (zipper construction)
  ✓ `diagInter_isClubBelow`: diagonal intersection of clubs is a club
  ✓ `fodor`: Fodor's pressing-down lemma (0 sorries)
  ✓ `fodor_aleph1`: specialization to ω₁
  ✓ `isLimitOrdinals_isClubBelow`: limit ordinals below κ.ord form a club (Solovay Step 1)
  ✓ `nonLimitOrdinals_not_isStationaryBelow`: non-limit ordinals are non-stationary (corollary)
  ✓ `IsClubBelow.inter`: binary intersection of clubs is a club (Solovay Step 2 companion)
  ✓ `IsStationaryBelow.inter_isClubBelow`: stationary ∩ club is stationary (Solovay Step 2 companion)
  ✓ `IsStationaryBelow.inter_isLimitOrdinals`: WLOG-restrict stationary to limit ordinals
  ✓ `cofHead`: 0-th element of a chosen fundamental sequence (Solovay Step 2 regressive)
  ✓ `cofHead_lt`: `cofHead α < α` for `IsSuccLimit α` (regressivity)
  ✓ `exists_cofHead_constant_stationary`: Fodor's first application via `cofHead`
  ✓ `exists_cofHead_constant_stationary_of_stationary`: ready-to-use S2-β form
  ✓ `stationary_splits_of_fiber_compl`: fiber + co-stationary complement ⇒ binary split
  ✓ `stationary_splits_of_two_fibers`: two distinct stationary fibers ⇒ binary split

Sorries remaining: 0

Open next step (`stationary_splits_binary`): the two packaging lemmas above
reduce binary Solovay splitting to *producing* two complementary (or two
distinct-value) stationary pieces from a regressive function. That production
step is the index-of-first-disagreement counting argument, not available at
the pinned Mathlib SHA — see the slug's `state.md` and
`sessions/2026-05-15-s3b-prep-disjointness-drill.md` §4.3.

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
