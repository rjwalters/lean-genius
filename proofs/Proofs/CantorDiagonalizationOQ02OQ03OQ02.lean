/-
# Fodor's Pressing-Down Lemma for Regular Cardinals
## CantorDiagonalizationOQ02OQ03OQ02

Building on CantorDiagonalizationOQ02OQ03 (generalized diagonal argument for regular
cardinals), we formalize Fodor's Pressing-Down Lemma (1956):

**Theorem (Fodor 1956):** Let κ be an uncountable regular cardinal. Let S be a
stationary subset of the ordinals below κ.ord. If f : Ordinal → Ordinal is regressive
on S (f(α) < α for all α ∈ S), then f is constant on a stationary subset of S.

This is a fundamental lemma in combinatorial set theory, with applications to:
- The non-principal nature of the club filter on ω₁
- Theorems about non-reflecting stationary sets
- PCF theory and Shelah's work on the singular cardinals hypothesis

## Mathematical Structure

1. **Club sets** (§1): closed unbounded subsets of ordinals below κ.ord
2. **Stationary sets** (§2): subsets intersecting every club
3. **Diagonal intersection** (§3): the set {α | ∀ β < α, α ∈ f(β)}
4. **Closed part** (§4): diagonal intersection of clubs is closed — PROVED
5. **Unbounded part** (§5): diagonal intersection of clubs is unbounded — PROVED
6. **Fodor's Lemma** (§6): the main theorem — PROVED from §4-5

## Proof Architecture

All theorems proved with 0 sorries.

Key techniques:
- `Ordinal.bsup` for bounded supremum in the bump function (avoids universe mismatch)
- `iSup_lt_ord_lift_of_isRegular` for ω-sequence supremum bound (handles ℕ : Type 0)
- `IsSuccLimit` (Order namespace) instead of non-existent `Ordinal.IsLimit`
- `IsClosedBelow` formulated without limit-ordinal hypothesis (vacuously true at successors)

## References
- Fodor, G. (1956). "Eine Bemerkung zur Theorie der regressiven Funktionen."
  Acta Sci. Math. (Szeged) 17, 139–142.
- Jech, T. (2003). *Set Theory*. Springer. §8 (Stationary Sets).
-/

import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Tactic

namespace FodorLemma

open Cardinal Order Ordinal Set

-- ============================================================================
-- § 1. Club Sets: Closed Unbounded Subsets of Ordinals Below κ
-- ============================================================================

/-- A set S is **unbounded** below κ.ord: cofinal in κ.ord.
    For any α < κ.ord, some element of S lies strictly between α and κ.ord. -/
def IsUnboundedBelow (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  ∀ α, α < κ.ord → ∃ β ∈ S, α < β ∧ β < κ.ord

/-- A set S is **closed** below κ.ord: contains all limit points below κ.ord.

    γ is a limit point of S (below o) if γ < κ.ord, γ is a limit ordinal, and
    S is cofinal in γ. The closed condition forces such γ to belong to S. -/
def IsClosedBelow (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  ∀ γ, γ < κ.ord →
  (∀ α, α < γ → ∃ δ ∈ S, α < δ ∧ δ < γ) → γ ∈ S

/-- A **club** (closed unbounded set) in κ.ord. Clubs are the "large" sets in the
    club filter of a regular cardinal — any two clubs have a club intersection. -/
def IsClub (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  IsUnboundedBelow κ S ∧ IsClosedBelow κ S

-- ============================================================================
-- § 2. Stationary Sets: Non-Empty Intersection with Every Club
-- ============================================================================

/-- S is **stationary** in κ if it intersects every club below κ.ord.
    The club filter's dual ideal consists exactly of the non-stationary sets. -/
def IsStationary (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  ∀ C, IsClub κ C → ∃ α, α ∈ S ∧ α ∈ C

/-- S is non-stationary iff some club avoids S entirely. -/
theorem not_isStationary_iff {κ : Cardinal.{u}} {S : Set Ordinal.{u}} :
    ¬ IsStationary κ S ↔ ∃ C, IsClub κ C ∧ ∀ α ∈ S, α ∉ C := by
  constructor
  · intro h
    simp only [IsStationary] at h
    push_neg at h
    exact h
  · rintro ⟨C, hC, h⟩ hstat
    obtain ⟨α, hαS, hαC⟩ := hstat C hC
    exact h α hαS hαC

-- ============================================================================
-- § 3. Diagonal Intersection: The Key Combinatorial Tool
-- ============================================================================

/-- The **diagonal intersection** of a family f : Ordinal → Set Ordinal.
    An ordinal α belongs to diagInter f iff α ∈ f(β) for every β < α.

    Contrast with ordinary intersection ∩_β f(β) (membership for ALL β):
    diagInter f "diagonalizes" — membership in f(β) is only required for β < α,
    not for β ≥ α. This makes the diagonal intersection of κ clubs a club
    (even though the ordinary intersection of κ clubs may not be one). -/
def diagInter (f : Ordinal.{u} → Set Ordinal.{u}) : Set Ordinal.{u} :=
  {α | ∀ β, β < α → α ∈ f β}

/-- Membership characterization: α ∈ diagInter f iff α ∈ f(β) for all β < α. -/
@[simp] theorem mem_diagInter {f : Ordinal.{u} → Set Ordinal.{u}} {α : Ordinal.{u}} :
    α ∈ diagInter f ↔ ∀ β, β < α → α ∈ f β :=
  Iff.rfl

-- ============================================================================
-- § 4. Diagonal Intersection of Clubs is Closed (PROVED)
-- ============================================================================

/-- **Theorem (Closed Part — PROVED):** If every f(β) is a club, then diagInter f
    satisfies the closed condition.

    **Proof:** Let γ < κ.ord be a limit ordinal with diagInter f cofinal in γ.
    We show γ ∈ f(β) for every β < γ.

    Fix β < γ. For any α with max(α,β) < γ, choose δ ∈ diagInter f with
    max(α,β) < δ < γ (exists since diagInter f is cofinal in γ). Then:
    - β < δ and δ ∈ diagInter f, so δ ∈ f(β)
    - α < δ < γ

    So f(β) is cofinal in γ. Since f(β) is a club (hence closed) and γ < κ.ord is a
    limit ordinal, γ ∈ f(β). Since β < γ was arbitrary, γ ∈ diagInter f. □ -/
theorem diagInter_isClosedBelow {κ : Cardinal.{u}} {f : Ordinal.{u} → Set Ordinal.{u}}
    (hf : ∀ β, β < κ.ord → IsClub κ (f β)) :
    IsClosedBelow κ (diagInter f) := by
  -- Let γ < κ.ord be cofinal for diagInter f
  intro γ hγκ hcof
  -- Show γ ∈ diagInter f: ∀ β < γ, γ ∈ f β
  rw [mem_diagInter]
  intro β hβγ
  -- Apply the closed condition of f β (which is a club)
  apply (hf β (lt_trans hβγ hγκ)).2 γ hγκ
  -- Show f β is cofinal in γ
  intro α hαγ
  -- Find δ ∈ diagInter f above max(α, β) and below γ
  obtain ⟨δ, hδmem, hlt, hδγ⟩ := hcof (max α β) (max_lt hαγ hβγ)
  -- Since δ ∈ diagInter f and β < max(α,β) < δ, we have δ ∈ f β
  exact ⟨δ, hδmem β (lt_of_le_of_lt (le_max_right α β) hlt),
         lt_of_le_of_lt (le_max_left α β) hlt, hδγ⟩

-- ============================================================================
-- § 5. Diagonal Intersection of Clubs is Unbounded (PROVED)
-- ============================================================================

/-- **Theorem (Unbounded Part — PROVED):** If every f(β) is a club, then diagInter f
    is unbounded below κ.ord.

    **Proof outline (matching the term below):**

    Given α₀ < κ.ord, construct a strictly increasing ω-sequence (α_n) by:
    - α_{n+1} ∈ ∩_{β ≤ α_n} f(β) with α_{n+1} > α_n and α_{n+1} < κ.ord
      (this intersection is a club since it involves ≤ α_n < κ clubs;
       for regular κ, any intersection of < κ clubs is a club)

    Let α_ω = iSup(n, α_n). Then:
    - α_ω < κ.ord: by `Ordinal.iSup_lt_ord` (regularity of κ, ℕ-many terms)
    - α_ω ∈ diagInter f: for any β < α_ω, choose n with β ≤ α_n; then
      (α_m)_{m≥n} is an ω-sequence in f(β) converging to α_ω (since
      each α_{m+1} ∈ f(β) as β ≤ α_n ≤ α_m); since f(β) is closed, α_ω ∈ f(β).

    **Technical Note:** The intermediate lemma "finite intersection of clubs is a club"
    requires showing: if C₁, C₂ are clubs, then C₁ ∩ C₂ is a club. This follows by
    the "ping-pong" argument: build an ω-sequence alternating between C₁ and C₂,
    take the limit (which lies in both, using regularity and closedness). -/
theorem diagInter_isUnbounded {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {f : Ordinal.{u} → Set Ordinal.{u}} (hf : ∀ β, β < κ.ord → IsClub κ (f β)) :
    IsUnboundedBelow κ (diagInter f) := by
  intro α₀ hα₀
  classical
  -- κ.ord is a successor-limit (limit ordinal) since κ ≥ ℵ₀
  have hκlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_le
  -- For each β < κ.ord and δ < κ.ord, pick an element of f β above δ
  have pick : ∀ β, β < κ.ord → ∀ δ, δ < κ.ord →
      ∃ γ ∈ f β, δ < γ ∧ γ < κ.ord :=
    fun β hβ δ hδ => (hf β hβ).1 δ hδ
  -- "bump": given δ < κ.ord, take bsup over β < δ+1 of next-element-of-f(β)-above-δ
  -- This gives a value > δ and < κ.ord, and f(β) has an element in (δ, bump δ] for β ≤ δ
  let bump (δ : Ordinal.{u}) (hδ : δ < κ.ord) : Ordinal.{u} :=
    Ordinal.bsup (δ + 1) fun β hβ =>
      (pick β (lt_trans hβ (hκlim.succ_lt hδ)) δ hδ).choose
  have bump_lt : ∀ δ (hδ : δ < κ.ord), bump δ hδ < κ.ord := by
    intro δ hδ
    apply Ordinal.bsup_lt_ord
    · rw [hκ.cof_eq]; exact Cardinal.lt_ord.mp (hκlim.succ_lt hδ)
    · intro β hβ; exact (pick β (lt_trans hβ (hκlim.succ_lt hδ)) δ hδ).choose_spec.2.2
  have bump_gt : ∀ δ (hδ : δ < κ.ord), δ < bump δ hδ := by
    intro δ hδ
    have h0lt : (0 : Ordinal.{u}) < δ + 1 := Ordinal.succ_pos δ
    calc δ < (pick 0 (lt_trans h0lt (hκlim.succ_lt hδ)) δ hδ).choose :=
            (pick 0 (lt_trans h0lt (hκlim.succ_lt hδ)) δ hδ).choose_spec.2.1
      _ ≤ bump δ hδ := Ordinal.le_bsup _ 0 h0lt
  have bump_witness : ∀ δ (hδ : δ < κ.ord) β (hβ : β ≤ δ),
      ∃ γ ∈ f β, δ < γ ∧ γ ≤ bump δ hδ := by
    intro δ hδ β hβ
    have hβκ : β < κ.ord := lt_of_le_of_lt hβ (lt_trans (lt_succ δ) (hκlim.succ_lt hδ))
    have hβsucc : β < δ + 1 := lt_of_le_of_lt hβ (lt_succ δ)
    exact ⟨(pick β hβκ δ hδ).choose, (pick β hβκ δ hδ).choose_spec.1,
           (pick β hβκ δ hδ).choose_spec.2.1, Ordinal.le_bsup _ β hβsucc⟩
  -- Build ω-sequence carrying proofs of < κ.ord
  let seq : ℕ → { α : Ordinal.{u} // α < κ.ord } :=
    Nat.rec ⟨α₀ + 1, hκlim.succ_lt hα₀⟩ fun _ prev =>
      ⟨bump prev.val prev.prop + 1, hκlim.succ_lt (bump_lt prev.val prev.prop)⟩
  let s : ℕ → Ordinal.{u} := fun n => (seq n).val
  have hs_lt : ∀ n, s n < κ.ord := fun n => (seq n).prop
  -- s n < bump(s n) < bump(s n) + 1 = s (n+1)
  have hs_inc' : ∀ n, s n < s (n + 1) :=
    fun n => lt_trans (bump_gt (s n) (hs_lt n)) (lt_succ _)
  -- Take γ = iSup s
  let γ : Ordinal.{u} := iSup s
  have hγ_lt : γ < κ.ord :=
    iSup_lt_ord_lift_of_isRegular hκ hκ_unc hs_lt
  have hγ_gt : α₀ < γ := lt_of_lt_of_le (lt_succ α₀) (Ordinal.le_iSup s 0)
  -- γ ∈ diagInter f
  have hγ_diag : γ ∈ diagInter f := by
    rw [mem_diagInter]
    intro β hβγ
    -- f β is a club; apply closedness since f β is cofinal in γ
    apply (hf β (lt_trans hβγ hγ_lt)).2 γ hγ_lt
    intro p hpγ
    -- Find m with β ≤ s m and p < s m
    obtain ⟨n, hn⟩ : ∃ n, β < s n := by
      by_contra h; push_neg at h
      exact absurd (Ordinal.iSup_le fun n => h n) (not_le.mpr hβγ)
    obtain ⟨n₂, hn₂⟩ : ∃ n, p < s n := by
      by_contra h; push_neg at h
      exact absurd (Ordinal.iSup_le fun n => h n) (not_le.mpr hpγ)
    let m := max n n₂
    have hβm : β ≤ s m := le_of_lt (lt_of_lt_of_le hn
      (StrictMono.monotone (strictMono_nat_of_lt_succ hs_inc') (le_max_left _ _)))
    have hpm : p < s m := lt_of_lt_of_le hn₂
      (StrictMono.monotone (strictMono_nat_of_lt_succ hs_inc') (le_max_right _ _))
    -- bump_witness gives element of f β in (s m, bump(s m)] ⊆ [p+1, s(m+1))
    obtain ⟨δ, hδ_mem, hδ_gt, hδ_le⟩ := bump_witness (s m) (hs_lt m) β hβm
    exact ⟨δ, hδ_mem, lt_of_lt_of_le hpm (le_of_lt hδ_gt),
           lt_of_le_of_lt hδ_le (lt_of_lt_of_le (lt_succ _) (Ordinal.le_iSup s (m + 1)))⟩
  exact ⟨γ, hγ_diag, hγ_gt, hγ_lt⟩

-- ============================================================================
-- § 6. Diagonal Intersection of Clubs is a Club
-- ============================================================================

/-- For a regular uncountable κ, the diagonal intersection of a κ-indexed family
    of clubs is itself a club. This combines the proved closed part with the proved
    unbounded part. -/
theorem diagInter_isClub {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {f : Ordinal.{u} → Set Ordinal.{u}} (hf : ∀ β, β < κ.ord → IsClub κ (f β)) :
    IsClub κ (diagInter f) :=
  ⟨diagInter_isUnbounded hκ hκ_unc hf, diagInter_isClosedBelow hf⟩

-- ============================================================================
-- § 7. Fodor's Pressing-Down Lemma (PROVED modulo § 5)
-- ============================================================================

/-- **Fodor's Pressing-Down Lemma (1956)** — the main theorem.

    Let κ be an uncountable regular cardinal.
    Let S be a stationary subset of {ordinals < κ.ord}.
    Let f : Ordinal → Ordinal be **regressive** on S: f(α) < α for all α ∈ S.
    (Note: f(α) < α for all α ∈ S implies 0 ∉ S, since no ordinal is < 0.)

    **Conclusion:** f is constant on a stationary subset of S.
    Equivalently: ∃ β < κ.ord such that {α ∈ S | f α = β} is stationary.

    **Proof:**
    Assume for contradiction that for every β < κ.ord, the preimage f⁻¹(β) ∩ S
    is NOT stationary. Then for each β, there exists a club C_β disjoint from
    f⁻¹(β) ∩ S (i.e., C_β ∩ S ∩ f⁻¹(β) = ∅).

    Form the diagonal intersection D = {α | ∀ β < α, α ∈ C_β}.
    By `diagInter_isClub`, D is a club.
    Since S is stationary, there exists α ∈ S ∩ D.
    Since f is regressive: β₀ := f(α) < α.
    Since α ∈ D: α ∈ C_{β₀} (as β₀ < α).
    But C_{β₀} was chosen to avoid f⁻¹(β₀) ∩ S.
    Since α ∈ S and f(α) = β₀, we have α ∈ f⁻¹(β₀) ∩ S — contradiction! □ -/
theorem fodors_pressing_down
    {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal.{u}} (hS : IsStationary κ S)
    (hS_sub : ∀ α ∈ S, α < κ.ord)
    {f : Ordinal.{u} → Ordinal.{u}} (hf_reg : ∀ α ∈ S, f α < α) :
    ∃ β, β < κ.ord ∧ IsStationary κ {α ∈ S | f α = β} := by
  -- Assume for contradiction that no fiber is stationary
  by_contra h
  push_neg at h
  -- h : ∀ β, β < κ.ord → ¬ IsStationary κ {α ∈ S | f α = β}
  -- Step 1: For each β < κ.ord, extract a club C_β avoiding f⁻¹(β) ∩ S
  have hC_exists : ∀ β, β < κ.ord →
      ∃ C : Set Ordinal.{u}, IsClub κ C ∧ ∀ α ∈ S, f α = β → α ∉ C := by
    intro β hβ
    have hnotstat : ¬ IsStationary κ {α ∈ S | f α = β} := h β hβ
    rw [not_isStationary_iff] at hnotstat
    obtain ⟨C, hC, hCdisj⟩ := hnotstat
    exact ⟨C, hC, fun α hαS hfα hαC =>
      hCdisj α (show α ∈ {x ∈ S | f x = β} from ⟨hαS, hfα⟩) hαC⟩
  -- Step 2: Choose clubs via classical choice
  classical
  -- Define the club family: C_β for β < κ.ord
  let clubFor : Ordinal.{u} → Set Ordinal.{u} := fun β =>
    if hβ : β < κ.ord then Classical.choose (hC_exists β hβ) else Set.univ
  have hclubFor_isClub : ∀ β, β < κ.ord → IsClub κ (clubFor β) := by
    intro β hβ
    simp only [clubFor, dif_pos hβ]
    exact (Classical.choose_spec (hC_exists β hβ)).1
  have hclubFor_disj : ∀ β, β < κ.ord → ∀ α ∈ S, f α = β → α ∉ clubFor β := by
    intro β hβ α hαS hfα
    simp only [clubFor, dif_pos hβ]
    exact (Classical.choose_spec (hC_exists β hβ)).2 α hαS hfα
  -- Step 3: Form the diagonal intersection D = Δ_β C_β
  let D := diagInter clubFor
  -- Step 4: D is a club (the key lemma)
  have hD : IsClub κ D := diagInter_isClub hκ hκ_unc hclubFor_isClub
  -- Step 5: S ∩ D is nonempty (S is stationary and D is a club)
  obtain ⟨α, hαS, hαD⟩ := hS D hD
  -- Step 6: Derive contradiction
  -- f is regressive on S, so f(α) < α
  have hβ₀_lt_α : f α < α := hf_reg α hαS
  -- f(α) < α < κ.ord, so f(α) < κ.ord
  have hβ₀_lt_κ : f α < κ.ord := lt_trans hβ₀_lt_α (hS_sub α hαS)
  -- α ∈ D = diagInter clubFor, and f(α) < α, so α ∈ clubFor(f α)
  have hα_in_C : α ∈ clubFor (f α) := hαD (f α) hβ₀_lt_α
  -- But clubFor(f α) was chosen to avoid f⁻¹(f α) ∩ S
  -- α ∈ S and f(α) = f(α), so α ∈ f⁻¹(f α) ∩ S — contradiction
  exact absurd hα_in_C (hclubFor_disj (f α) hβ₀_lt_κ α hαS rfl)

-- ============================================================================
-- § 8. Implications and Mathematical Notes
-- ============================================================================

/-!
## Consequences of Fodor's Lemma

### The Club Filter is Not Principal
Fodor's lemma immediately implies that there is no "least club" below ω₁.
If S were such a least club, the identity function restricted to limit ordinals in S
would be regressive (f(α) = the previous element of S < α), and constant on a
stationary subset T — but then T would be a smaller club, contradiction.

### Stationary Sets Cannot Be Covered by Fewer Than κ Non-Stationary Sets
Any partition of a stationary set S into pieces S_β (β < κ) via a regressive function
must have some S_β stationary. This is the "pressing down" intuition.

### Connection to Parent Proof (CantorDiagonalizationOQ02OQ03)
The parent proof established:
- `regular_sup_bounded`: for regular κ, sup of < κ-many ordinals below κ.ord is < κ.ord
- `regular_no_surjection`: diagonal argument for regular cardinals

Fodor's lemma is a *combinatorial* strengthening of the diagonal argument:
instead of constructing a single "escaping" ordinal (as in the diagonal argument),
it constructs an entire *stationary set* of ordinals where a function is constant.
Both proofs use regularity in an essential way.

## What Remains (Future Work)

The core result is complete: `diagInter_isUnbounded`, `diagInter_isClub`, and
`fodors_pressing_down` are all proved with no sorries and no axioms. The unbounded
part is established directly via a `bump` operator (a `bsup` over β < δ+1) rather than
a standalone finite-intersection lemma. Natural extensions:

1. **`isClub_inter`** as a reusable lemma: prove that ∩(C₁, C₂) is a club via the
   "ping-pong" argument (alternating ω-sequence, sup < κ.ord by `Ordinal.iSup_lt_ord`,
   limit in C₁ ∩ C₂ by closedness). The current file inlines an equivalent argument.

2. **Club filter / stationary ideal**: show clubs generate a filter and that stationary
   sets are exactly those not in the dual ideal.
-/

-- Type-check the main results
#check @fodors_pressing_down
#check @diagInter_isClosedBelow
#check @diagInter_isClub
#check @IsClub
#check @IsStationary

end FodorLemma
