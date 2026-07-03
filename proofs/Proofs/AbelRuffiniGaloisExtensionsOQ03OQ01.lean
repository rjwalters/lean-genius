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
  * `isThreeCycle_of_min_support` — the **isolated crux**, and now the *only*
    `sorry`.  Its `3 ≤ #support` and `#support = 3 ⇒ 3-cycle` branches are
    **proved in-line**; the single remaining `sorry` is the classical
    strict-support-decrease commutator step for `#support ≥ 4`.
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

/-! ### The classical combinatorial crux (the sole remaining `sorry`) -/

/-- **Crux (KNOWN result; single remaining `sorry`).** A nonidentity element `σ`
of a normal subgroup `H ⊴ Aₙ` (`n ≥ 5`) whose support is *minimal* among the
nonidentity elements of `H` is a 3-cycle.

The `3 ≤ #support` and `#support = 3 ⇒ 3-cycle` branches are discharged here; the
remaining `sorry` is exactly the classical strict-support-decrease commutator step
handling `#support ≥ 4` (see the file header for the proof plan). -/
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
