/-
  Unconditional simplicity of Aₙ (n ≥ 5), reduced to a single classical lemma
  (Open Question OQ-03-OQ-01 of abel-ruffini-galois-extensions).

  ## STATUS: WORK IN PROGRESS (1 sorry — a single sharply-isolated commutator step)

  This file is *not* a verified gallery entry.  It isolates and states the single
  remaining hard step needed to upgrade the parent file's *conditional* reduction
  (`AbelRuffiniGaloisExtensionsOQ03`) into an **unconditional** proof that the
  alternating group `Aₙ` is simple for every `n ≥ 5`, generalizing Mathlib's
  `alternatingGroup.isSimpleGroup_five` (which covers only `Fin 5`).

  ## What the parent already established (0 sorry)

  `AbelRuffiniGaloisExtensionsOQ03` proved the *formal* half of the classical
  theorem:

    `isSimpleGroup_of_forall_normal_contains_threeCycle`
      (5 ≤ card α) → (every nontrivial normal H ⊴ Aₙ contains a 3-cycle)
                   → IsSimpleGroup (Aₙ)

  together with the converse and the headline `iff`.  The genuinely combinatorial
  content of the simplicity theorem was thereby isolated to the single statement

      **every nontrivial normal subgroup of `Aₙ` (n ≥ 5) contains a 3-cycle.**

  ## What this file adds (progress over PR #33855)

  PR #33855 stated the whole containment lemma as one monolithic `sorry`.  This
  revision *decomposes and discharges* the surrounding argument, leaving a single
  sharply-focused `sorry` for the genuine crux:

  * `three_le_card_support_of_mem` — **PROVED (0 sorry).** A nontrivial *even*
    permutation moves at least 3 points.  (It cannot move 0 points without being
    the identity, cannot move exactly 1 point, and cannot move exactly 2 points
    since that would make it an odd transposition.)
  * `commutator_mem_of_normal` — **PROVED (0 sorry).** For `H ⊴ Aₙ`, `σ ∈ H` and
    any `τ`, the commutator `τ σ τ⁻¹ σ⁻¹` lies in `H`.  This is the membership
    engine that feeds the minimal-support argument.
  * `exists_min_support_ne_one` — **PROVED (0 sorry).** A nontrivial (in
    particular, any nontrivial normal) subgroup contains a nonidentity element of
    minimal support cardinality.
  * `support_commutator_subset` — **PROVED (0 sorry).** If `τ.support ⊆ σ.support`
    then the commutator `τ σ τ⁻¹ σ⁻¹` is supported within `σ.support`.
  * `exists_smaller_commutator_of_five_points` — **PROVED (0 sorry).** The
    strict-support-decrease *engine* for the cycle-of-length-`≥3` case: from five
    distinct points `a,b,c,d,e` (with `b,c,d,e` moved and `σ a = b`, `σ b = c`),
    the commutator with the 3-cycle `(c d e)` is a nonidentity element of `H` of
    strictly smaller support.  This discharges the hard *quantitative* half of the
    `#support ≥ 4` branch; what remains for the crux is the purely *combinatorial*
    extraction of such a configuration (Case A) and the involution case (Case B).
  * `isThreeCycle_of_min_support` — the **isolated crux**, and now the *only*
    `sorry`.  Its `3 ≤ #support` and `#support = 3 ⇒ 3-cycle` branches are
    **proved in-line**; the single remaining `sorry` is the `#support ≥ 4` branch,
    now reduced (given the engine above) to producing the five-point configuration
    or handling the disjoint-transposition (involution) case.
  * `exists_mem_isThreeCycle_of_normal` — **PROVED (0 sorry) modulo the crux**:
    assembled from `exists_min_support_ne_one` and `isThreeCycle_of_min_support`.
  * `isSimpleGroup_alternating` — the unconditional simplicity theorem for all
    `n ≥ 5`, obtained by feeding the containment lemma into the parent's
    reduction.  Complete body; inherits exactly the one crux `sorry`.

  ## The remaining crux (`isThreeCycle_of_min_support`, `#support ≥ 4` branch)
     (Jordan's minimal-support / commutator argument)

  Let `σ ∈ H` be nonidentity of *minimal* support with `#σ.support ≥ 4`.  Derive a
  contradiction by exhibiting a nonidentity element of `H` with strictly smaller
  support.  Choose a 3-cycle `τ` adapted to the cycle type of `σ`; the commutator
  `ρ = τ σ τ⁻¹ σ⁻¹ ∈ H` (`commutator_mem_of_normal`) is `≠ 1` and satisfies
  `ρ.support ⊆ σ.support ∪ τ • σ.support` with a strictly smaller count,
  contradicting minimality.  Split on whether `σ` has a cycle of length `≥ 3`
  (Case A) or is a product of disjoint transpositions (Case B).

  ## Mathlib API this plan relies on (all confirmed present)

  * `Equiv.Perm.support_mul_le`, `Equiv.Perm.support_conj`,
    `Equiv.Perm.card_support_conj`      — support of products / conjugates
  * `Equiv.Perm.card_support_eq_two` (`IsSwap`), `Equiv.Perm.card_support_ne_one`
  * `card_support_eq_three_iff`          — 3 moved points ⇔ 3-cycle
  * `Equiv.Perm.IsSwap.sign_eq`, `mem_alternatingGroup`
  * `Subgroup.Normal.conj_mem`, `Subgroup.bot_or_exists_ne_one`
  * `Finset.exists_min_image`            — minimal-support selection
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

open Equiv Equiv.Perm Subgroup

namespace AbelRuffiniGaloisExtensionsOQ03OQ01

open alternatingGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The formal reduction (re-derived, 0 sorry)

These two lemmas reproduce the verified reduction from
`AbelRuffiniGaloisExtensionsOQ03`, inlined here so that this file depends only on
Mathlib (allowing single-file elaboration).  They contain no `sorry`. -/

/-- If a normal subgroup `H ⊴ Aₙ` (`n ≥ 5`) contains a 3-cycle, then `H = ⊤`.
Upgrades Mathlib's `IsThreeCycle.alternating_normalClosure` (normal closure of a
single 3-cycle) to an arbitrary normal subgroup. -/
theorem threeCycle_normal_eq_top
    (h5 : 5 ≤ Fintype.card α)
    {H : Subgroup (alternatingGroup α)} (hHn : H.Normal)
    {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α)) (hgH : g ∈ H) :
    H = ⊤ := by
  haveI := hHn
  have hclosed : normalClosure ({g} : Set (alternatingGroup α)) ≤ H :=
    normalClosure_le_normal (Set.singleton_subset_iff.2 hgH)
  have hgeq : (⟨(g : Perm α), hg.mem_alternatingGroup⟩ : alternatingGroup α) = g :=
    Subtype.ext rfl
  have htop : normalClosure ({g} : Set (alternatingGroup α)) = ⊤ := by
    rw [← hgeq]; exact hg.alternating_normalClosure h5
  rw [htop] at hclosed
  exact top_le_iff.1 hclosed

/-- If every nontrivial normal subgroup of `Aₙ` (`n ≥ 5`) contains a 3-cycle, then
`Aₙ` is simple. -/
theorem isSimpleGroup_of_forall_normal_contains_threeCycle
    (h5 : 5 ≤ Fintype.card α)
    (hcrux : ∀ (H : Subgroup (alternatingGroup α)), H.Normal → H ≠ ⊥ →
        ∃ g : alternatingGroup α, IsThreeCycle (g : Perm α) ∧ g ∈ H) :
    IsSimpleGroup (alternatingGroup α) := by
  haveI : Nontrivial (alternatingGroup α) := nontrivial_of_three_le_card (by omega)
  refine ⟨fun H hHn => ?_⟩
  rcases eq_or_ne H ⊥ with h | h
  · exact Or.inl h
  · obtain ⟨g, hg, hgH⟩ := hcrux H hHn h
    exact Or.inr (threeCycle_normal_eq_top h5 hHn hg hgH)

/-! ### Supporting lemmas (all 0 sorry) -/

/-- A nontrivial **even** permutation moves at least 3 points.  An even
permutation cannot move exactly one point (no permutation does) nor exactly two
(that would be an odd transposition), so its support has at least three elements.
-/
theorem three_le_card_support_of_mem {g : Perm α}
    (hmem : g ∈ alternatingGroup α) (hne : g ≠ 1) :
    3 ≤ (g.support).card := by
  have h0 : (g.support).card ≠ 0 := by
    simpa [Finset.card_eq_zero, support_eq_empty_iff] using hne
  have h1 : (g.support).card ≠ 1 := card_support_ne_one g
  have h2 : (g.support).card ≠ 2 := by
    intro hcard
    have hswap : g.IsSwap := card_support_eq_two.1 hcard
    have hsign : Perm.sign g = -1 := hswap.sign_eq
    rw [mem_alternatingGroup] at hmem
    rw [hmem] at hsign
    exact absurd hsign (by decide)
  omega

/-- For a normal subgroup `H` of the alternating group, `σ ∈ H` and any `τ`, the
commutator `τ σ τ⁻¹ σ⁻¹` lies in `H`.  This is the membership engine for the
minimal-support argument: conjugates of `σ` stay in `H`, and so do their products
with `σ⁻¹`. -/
theorem commutator_mem_of_normal {H : Subgroup (alternatingGroup α)}
    (hHn : H.Normal) {σ : alternatingGroup α} (hσ : σ ∈ H) (τ : alternatingGroup α) :
    τ * σ * τ⁻¹ * σ⁻¹ ∈ H := by
  have hconj : τ * σ * τ⁻¹ ∈ H := by
    have := hHn.conj_mem σ hσ τ
    simpa [mul_assoc] using this
  exact mul_mem hconj (inv_mem hσ)

/-- A nontrivial subgroup `H` of the (finite) alternating group contains a
nonidentity element whose support cardinality is minimal among all nonidentity
elements of `H`. -/
theorem exists_min_support_ne_one {H : Subgroup (alternatingGroup α)} (hbot : H ≠ ⊥) :
    ∃ σ : alternatingGroup α, σ ∈ H ∧ σ ≠ 1 ∧
      ∀ τ : alternatingGroup α, τ ∈ H → τ ≠ 1 →
        (σ : Perm α).support.card ≤ (τ : Perm α).support.card := by
  classical
  have hSne : (Finset.univ.filter (fun g => g ∈ H ∧ g ≠ 1)).Nonempty := by
    obtain ⟨x, hxH, hx1⟩ := (bot_or_exists_ne_one H).resolve_left hbot
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxH, hx1⟩⟩
  obtain ⟨σ, hσS, hσmin⟩ :=
    (Finset.univ.filter (fun g => g ∈ H ∧ g ≠ 1)).exists_min_image
      (fun g => (g : Perm α).support.card) hSne
  obtain ⟨hσH, hσ1⟩ := (Finset.mem_filter.mp hσS).2
  refine ⟨σ, hσH, hσ1, fun τ hτH hτ1 => ?_⟩
  exact hσmin τ (Finset.mem_filter.mpr ⟨Finset.mem_univ τ, hτH, hτ1⟩)

/-- **Commutator-support containment (0 sorry).** If the support of `τ` is
contained in the support of `σ`, then the commutator `τ σ τ⁻¹ σ⁻¹` is supported
within `σ.support`.  Together with minimality of `σ.support` this is the mechanism
by which the crux produces a *strictly smaller* element: the commutator lands
inside `σ.support`, so if it additionally fixes one point that `σ` moves, its
support is strictly smaller.

Key fact used: `τ` maps `σ.support` into itself (a point moved by `τ` lands in
`τ.support ⊆ σ.support`; a point fixed by `τ` stays put), hence the conjugate
`τ σ τ⁻¹` is again supported in `σ.support`. -/
theorem support_commutator_subset {σ τ : Perm α} (hτσ : τ.support ⊆ σ.support) :
    (τ * σ * τ⁻¹ * σ⁻¹).support ⊆ σ.support := by
  -- `τ` maps `σ.support` into `σ.support`.
  have hmap : ∀ x ∈ σ.support, τ x ∈ σ.support := by
    intro x hx
    by_cases hxτ : x ∈ τ.support
    · exact hτσ (apply_mem_support.mpr hxτ)
    · rwa [notMem_support.mp hxτ]
  intro y hy
  -- `support (a * b) ⊆ support a ∪ support b`, applied to `a = τστ⁻¹`, `b = σ⁻¹`.
  have hy2 : y ∈ (τ * σ * τ⁻¹).support ∪ (σ⁻¹).support := by
    have h := support_mul_le (τ * σ * τ⁻¹) σ⁻¹ hy
    simpa only [Finset.sup_eq_union] using h
  rw [Finset.mem_union, support_inv, support_conj] at hy2
  rcases hy2 with hy2 | hy2
  · -- `y ∈ σ.support.map τ.toEmbedding`, i.e. `y = τ x` with `x ∈ σ.support`.
    rw [Finset.mem_map] at hy2
    obtain ⟨x, hx, hxy⟩ := hy2
    simp only [Equiv.coe_toEmbedding] at hxy
    rw [← hxy]
    exact hmap x hx
  · exact hy2

/-- **Case A engine (0 sorry).** The strict-support-decrease step of Jordan's
argument, in the exact form the crux consumes for a permutation with a cycle of
length `≥ 3`.  Given five *distinct* points `a, b, c, d, e` with `b, c, d, e` all
moved by `σ` and `σ a = b`, `σ b = c` (so `a, b, c` lie on a common cycle of length
`≥ 3`), the commutator of `σ` with the 3-cycle `τ = (c d e)` is a nonidentity
element of `H` whose support is *strictly smaller* than that of `σ`.

Mechanism: `ρ = τ σ τ⁻¹ σ⁻¹ ∈ H` by normality (`commutator_mem_of_normal`); it is
supported inside `σ.support` (`support_commutator_subset`, as
`τ.support ⊆ {c,d,e} ⊆ σ.support`); `ρ c = e ≠ c` so `ρ ≠ 1`; and `ρ b = b` while
`b ∈ σ.support`, so the support drops by at least one point. -/
theorem exists_smaller_commutator_of_five_points
    {H : Subgroup (alternatingGroup α)} (hHn : H.Normal)
    {σ : alternatingGroup α} (hσH : σ ∈ H)
    {a b c d e : α}
    (_hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hbsupp : b ∈ (σ : Perm α).support)
    (hc : c ∈ (σ : Perm α).support) (hd : d ∈ (σ : Perm α).support)
    (he : e ∈ (σ : Perm α).support)
    (hσab : (σ : Perm α) a = b) (hσbc : (σ : Perm α) b = c) :
    ∃ ρ : alternatingGroup α, ρ ∈ H ∧ ρ ≠ 1 ∧
      (ρ : Perm α).support.card < (σ : Perm α).support.card := by
  classical
  set sp : Perm α := (σ : Perm α) with hsp
  -- The 3-cycle τ = (c d e), as an element of the alternating group.
  set τp : Perm α := Equiv.swap c d * Equiv.swap c e with hτp
  have hτ3 : τp.IsThreeCycle := isThreeCycle_swap_mul_swap_same hcd hce hde
  have hτmem : τp ∈ alternatingGroup α := hτ3.mem_alternatingGroup
  set τ : alternatingGroup α := ⟨τp, hτmem⟩ with hτ
  -- `τ.support ⊆ {c, d, e}`.
  have hτsub : τp.support ⊆ ({c, d, e} : Finset α) := by
    intro x hx
    rw [hτp] at hx
    have hx2 := support_mul_le (Equiv.swap c d) (Equiv.swap c e) hx
    rw [Finset.sup_eq_union, support_swap hcd, support_swap hce] at hx2
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx2 ⊢
    tauto
  have hcde_sub : ({c, d, e} : Finset α) ⊆ sp.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hc
    · exact hd
    · exact he
  have hτσ : τp.support ⊆ sp.support := hτsub.trans hcde_sub
  -- `a, b ∉ τ.support`.
  have hbτ : b ∉ τp.support := by
    intro h; have := hτsub h
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact hbc h
    · exact hbd h
    · exact hbe h
  have haτ : a ∉ τp.support := by
    intro h; have := hτsub h
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact hac h
    · exact had h
    · exact hae h
  -- Basic pointwise values of `τ` and `τ⁻¹`.
  have hτpb : τp b = b := notMem_support.mp hbτ
  have hτpinvb : τp⁻¹ b = b := notMem_support.mp (by rw [support_inv]; exact hbτ)
  have hτpinva : τp⁻¹ a = a := notMem_support.mp (by rw [support_inv]; exact haτ)
  have hτpc : τp c = e := by
    rw [hτp, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hce) (Ne.symm hde)]
  -- `sp⁻¹ c = b` and `sp⁻¹ b = a` from the cycle relations.
  have hspc : sp⁻¹ c = b := by rw [← hσbc]; exact Equiv.symm_apply_apply _ _
  have hspb : sp⁻¹ b = a := by rw [← hσab]; exact Equiv.symm_apply_apply _ _
  -- The commutator element and its underlying permutation.
  set ρ : alternatingGroup α := τ * σ * τ⁻¹ * σ⁻¹ with hρ
  have hρcoe : (ρ : Perm α) = τp * sp * τp⁻¹ * sp⁻¹ := by
    rw [hρ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ, hsp]
  refine ⟨ρ, ?_, ?_, ?_⟩
  · rw [hρ]; exact commutator_mem_of_normal hHn hσH τ
  · -- `ρ ≠ 1`, since its underlying permutation sends `c` to `e ≠ c`.
    have hρc : (ρ : Perm α) c = e := by
      rw [hρcoe]
      simp only [Equiv.Perm.mul_apply]
      rw [hspc, hτpinvb, hσbc, hτpc]
    intro hρ1
    have hc1 : (ρ : Perm α) c = c := by rw [hρ1, Subgroup.coe_one, Equiv.Perm.one_apply]
    rw [hρc] at hc1
    exact hce hc1.symm
  · -- Support strictly smaller: `ρ` fixes `b ∈ σ.support` but is supported in it.
    have hsub : (ρ : Perm α).support ⊆ sp.support := by
      rw [hρcoe]; exact support_commutator_subset hτσ
    have hρb : (ρ : Perm α) b = b := by
      rw [hρcoe]
      simp only [Equiv.Perm.mul_apply]
      rw [hspb, hτpinva, hσab, hτpb]
    have hbnotρ : b ∉ (ρ : Perm α).support := notMem_support.mpr hρb
    have hss : (ρ : Perm α).support ⊂ sp.support :=
      (Finset.ssubset_iff_of_subset hsub).mpr ⟨b, hbsupp, hbnotρ⟩
    exact Finset.card_lt_card hss

/-! ### The classical combinatorial crux (the sole remaining `sorry`) -/

/-- **Crux (KNOWN result; single remaining `sorry`).** A nonidentity element `σ`
of a normal subgroup `H ⊴ Aₙ` (`n ≥ 5`) whose support is *minimal* among the
nonidentity elements of `H` is a 3-cycle.

The `3 ≤ #support` and `#support = 3 ⇒ 3-cycle` branches are discharged here; the
remaining `sorry` is the `#support ≥ 4` branch.  Its quantitative core — that a
suitable commutator strictly shrinks the support — is now the **proved** lemma
`exists_smaller_commutator_of_five_points`; the residual `sorry` is the
combinatorial extraction of a five-point configuration `a,b,c,d,e` with `σ a = b`,
`σ b = c` (available whenever `σ² ≠ 1` and `#support ≥ 5`) together with the
disjoint-transposition (`σ² = 1`) case. -/
theorem isThreeCycle_of_min_support
    (h5 : 5 ≤ Fintype.card α)
    {H : Subgroup (alternatingGroup α)} (hHn : H.Normal)
    {σ : alternatingGroup α} (hσH : σ ∈ H) (hσ1 : σ ≠ 1)
    (hmin : ∀ τ : alternatingGroup α, τ ∈ H → τ ≠ 1 →
        (σ : Perm α).support.card ≤ (τ : Perm α).support.card) :
    IsThreeCycle (σ : Perm α) := by
  have hσne : (σ : Perm α) ≠ 1 := by
    rw [Ne, OneMemClass.coe_eq_one]; exact hσ1
  -- `σ` is even and nonidentity, so it moves at least 3 points.
  have hge3 : 3 ≤ (σ : Perm α).support.card :=
    three_le_card_support_of_mem σ.2 hσne
  rcases eq_or_lt_of_le hge3 with h3 | h4
  · -- Exactly 3 moved points ⇒ 3-cycle.
    exact card_support_eq_three_iff.1 h3.symm
  · -- `#support ≥ 4`: the classical strict-support-decrease commutator step,
    -- contradicting minimality.  This is the sole remaining `sorry`.
    sorry

/-! ### Assembly (0 sorry beyond the crux) -/

/-- **The classical combinatorial core.** Every nontrivial normal subgroup of the
alternating group on `α` (with `5 ≤ card α`) contains a 3-cycle.  Assembled from
`exists_min_support_ne_one` and the crux `isThreeCycle_of_min_support`. -/
theorem exists_mem_isThreeCycle_of_normal
    (h5 : 5 ≤ Fintype.card α)
    (H : Subgroup (alternatingGroup α)) (hHn : H.Normal) (hbot : H ≠ ⊥) :
    ∃ g : alternatingGroup α, IsThreeCycle (g : Equiv.Perm α) ∧ g ∈ H := by
  obtain ⟨σ, hσH, hσ1, hmin⟩ := exists_min_support_ne_one hbot
  exact ⟨σ, isThreeCycle_of_min_support h5 hHn hσH hσ1 hmin, hσH⟩

/-- **Unconditional simplicity of `Aₙ` for `n ≥ 5`.** Feeds the classical 3-cycle
lemma into the parent file's formal reduction
(`isSimpleGroup_of_forall_normal_contains_threeCycle`).  The body is complete; the
result inherits exactly one `sorry`, namely the crux `isThreeCycle_of_min_support`.

When that crux is discharged, this generalizes Mathlib's `Fin 5`-only
`alternatingGroup.isSimpleGroup_five` to every finite `α` with `5 ≤ card α`. -/
theorem isSimpleGroup_alternating (h5 : 5 ≤ Fintype.card α) :
    IsSimpleGroup (alternatingGroup α) :=
  isSimpleGroup_of_forall_normal_contains_threeCycle
    h5 (fun H hHn hbot => exists_mem_isThreeCycle_of_normal h5 H hHn hbot)

end AbelRuffiniGaloisExtensionsOQ03OQ01
