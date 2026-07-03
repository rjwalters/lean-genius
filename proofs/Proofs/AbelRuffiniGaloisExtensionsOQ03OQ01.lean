/-
  Unconditional simplicity of Aₙ (n ≥ 5) — Open Question OQ-03-OQ-01 of
  abel-ruffini-galois-extensions.

  ## STATUS: VERIFIED (0 sorry, 0 axiom)

  `isSimpleGroup_alternating` is a complete, machine-checked proof that the
  alternating group `Aₙ` is simple for **every** finite `α` with `5 ≤ card α`,
  generalizing Mathlib's `alternatingGroup.isSimpleGroup_five` (which covers only
  `Fin 5`).  `#print axioms isSimpleGroup_alternating` reports only the three
  standard foundational axioms `propext`, `Classical.choice`, `Quot.sound` — no
  `sorryAx`, no `Lean.ofReduceBool`.

  The proof is the classical **Jordan minimal-support / commutator argument**:
  every nontrivial normal subgroup `H ⊴ Aₙ` contains an element of minimal support,
  which must be a 3-cycle (else a suitable commutator produces a strictly smaller
  nonidentity element of `H`, contradicting minimality); a single 3-cycle already
  normally generates all of `Aₙ`.

  ## What the parent already established (0 sorry)

  `AbelRuffiniGaloisExtensionsOQ03` proved the *formal* half of the classical
  theorem:

    `isSimpleGroup_of_forall_normal_contains_threeCycle`
      (5 ≤ card α) → (every nontrivial normal H ⊴ Aₙ contains a 3-cycle)
                   → IsSimpleGroup (Aₙ)

  together with the converse and the headline `iff`.  The genuinely combinatorial
  content of the simplicity theorem was thereby isolated to the single statement

      **every nontrivial normal subgroup of `Aₙ` (n ≥ 5) contains a 3-cycle.**

  ## Structure of the proof

  * `three_le_card_support_of_mem` — A nontrivial *even* permutation moves at least
    3 points (it cannot move exactly 1, and moving exactly 2 would make it an odd
    transposition).
  * `commutator_mem_of_normal` — For `H ⊴ Aₙ`, `σ ∈ H` and any `τ`, the commutator
    `τ σ τ⁻¹ σ⁻¹` lies in `H`; the membership engine of the minimal-support argument.
  * `exists_min_support_ne_one` — A nontrivial subgroup contains a nonidentity
    element of minimal support cardinality.
  * `support_commutator_subset` — If `τ.support ⊆ σ.support` then the commutator
    `τ σ τ⁻¹ σ⁻¹` is supported within `σ.support`.
  * `exists_smaller_commutator_of_five_points` — **Case A engine.** From five
    distinct points `a,b,c,d,e` (with `b,c,d,e` moved and `σ a = b`, `σ b = c`, i.e.
    a cycle of length `≥ 3`), the commutator with the 3-cycle `(c d e)` is a
    nonidentity element of `H` of strictly smaller support.
  * `exists_smaller_commutator_of_involution` — **Case B engine.** From five
    distinct points with `σ` swapping `a ↔ b` and `c ↔ d`, the commutator with the
    3-cycle `(c e d)` is a nonidentity element of `H` of strictly smaller support.
  * `isThreeCycle_of_min_support` — **the crux, fully proved.** A support-minimal
    nonidentity `σ ∈ H` is a 3-cycle.  The `#support = 3` case is immediate; for
    `#support ≥ 4` a contradiction is derived by producing a strictly smaller
    element:  Case B (`σ² = 1`, involution) and Case A (`σ² ≠ 1`) with `#support ≥ 5`
    feed the two engines; the residual `#support = 4 ∧ σ² ≠ 1` case is impossible
    because such a `σ` would be a 4-cycle, which is *odd* (via `IsCycle.sign`),
    contradicting `σ ∈ Aₙ`.
  * `exists_mem_isThreeCycle_of_normal` — every nontrivial normal `H ⊴ Aₙ` contains
    a 3-cycle; assembled from `exists_min_support_ne_one` and the crux.
  * `isSimpleGroup_alternating` — the unconditional simplicity theorem, fed into the
    parent's formal reduction `isSimpleGroup_of_forall_normal_contains_threeCycle`.

  ## Key Mathlib API used

  * `Equiv.Perm.support_mul_le`, `Equiv.Perm.support_conj`, `support_inv`,
    `apply_mem_support`                    — support of products / conjugates
  * `Equiv.Perm.card_support_eq_two` (`IsSwap`), `Equiv.Perm.card_support_ne_one`,
    `card_support_eq_three_iff`            — small-support characterizations
  * `Equiv.Perm.IsCycle.sign`, `IsSwap.sign_eq`, `mem_alternatingGroup` — parity
  * `Equiv.Perm.sameCycle_apply_right`, `SameCycle.refl` — cycle recognition
  * `Subgroup.Normal.conj_mem`, `Subgroup.bot_or_exists_ne_one`,
    `Finset.exists_min_image`              — normality & minimal-support selection
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

/-- **Case B engine (0 sorry).** The strict-support-decrease step of Jordan's
argument for the *involution* case, in the exact form the crux consumes for a
permutation that is a product of disjoint transpositions.  Given five *distinct*
points `a, b, c, d, e` such that `σ` swaps `a ↔ b` and `c ↔ d` (so `a, b, c, d`
are all moved by `σ`), together with any fifth point `e`, the commutator of `σ`
with the 3-cycle `τ = (c e d)` is a nonidentity element of `H` whose support is
*strictly smaller* than that of `σ`.

Mechanism: `ρ = τ σ τ⁻¹ σ⁻¹ ∈ H` by normality (`commutator_mem_of_normal`);
`ρ d = e ≠ d` so `ρ ≠ 1`; `ρ` *fixes both* `a` and `b` (which `σ` moves); and
`ρ.support ⊆ {c, d, e, σ e}` (the commutator is `τ` times the `σ`-conjugate of
`τ⁻¹`, so it lives on `τ.support ∪ σ • τ.support = {c,d,e} ∪ {d, c, σ e}`).
Two cases finish the count:

* `e ∉ σ.support`: then `σ e = e`, so `ρ.support ⊆ {c, d, e}` has at most 3
  elements, while `σ.support ⊇ {a, b, c, d}` has at least 4.
* `e ∈ σ.support`: then `σ` already moves the five distinct points
  `a, b, c, d, e`, so `#σ.support ≥ 5`, while `#ρ.support ≤ 4`.

Unlike the Case A engine this needs no `#support` side hypotheses: membership of
`a, b, c, d` in `σ.support` follows from the swap relations. -/
theorem exists_smaller_commutator_of_involution
    {H : Subgroup (alternatingGroup α)} (hHn : H.Normal)
    {σ : alternatingGroup α} (hσH : σ ∈ H)
    {a b c d e : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hσab : (σ : Perm α) a = b) (hσba : (σ : Perm α) b = a)
    (hσcd : (σ : Perm α) c = d) (hσdc : (σ : Perm α) d = c) :
    ∃ ρ : alternatingGroup α, ρ ∈ H ∧ ρ ≠ 1 ∧
      (ρ : Perm α).support.card < (σ : Perm α).support.card := by
  classical
  set sp : Perm α := (σ : Perm α) with hsp
  -- The 3-cycle τ = (c e d), as an element of the alternating group.
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
  -- `a, b ∉ τ.support` (they are distinct from `c, d, e`).
  have haτ : a ∉ τp.support := by
    intro h; have := hτsub h
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact hac h
    · exact had h
    · exact hae h
  have hbτ : b ∉ τp.support := by
    intro h; have := hτsub h
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact hbc h
    · exact hbd h
    · exact hbe h
  -- Pointwise values of `τ`, `τ⁻¹`.
  have hτpa : τp a = a := notMem_support.mp haτ
  have hτpb : τp b = b := notMem_support.mp hbτ
  have hτpinva : τp⁻¹ a = a := notMem_support.mp (by rw [support_inv]; exact haτ)
  have hτpinvb : τp⁻¹ b = b := notMem_support.mp (by rw [support_inv]; exact hbτ)
  have hτpc : τp c = e := by
    rw [hτp, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hce) (Ne.symm hde)]
  have hτpd : τp d = c := by
    rw [hτp, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hcd) hde, Equiv.swap_apply_right]
  have hτpinvc : τp⁻¹ c = d := by
    rw [← hτpd]; exact Equiv.symm_apply_apply _ _
  -- `σ⁻¹` values from the swap relations.
  have hspinva : sp⁻¹ a = b := by rw [← hσba]; exact Equiv.symm_apply_apply _ _
  have hspinvb : sp⁻¹ b = a := by rw [← hσab]; exact Equiv.symm_apply_apply _ _
  have hspinvd : sp⁻¹ d = c := by rw [← hσcd]; exact Equiv.symm_apply_apply _ _
  -- `a, b, c, d ∈ σ.support` (they are moved).
  have hasupp : a ∈ sp.support := mem_support.mpr (by rw [hσab]; exact hab.symm)
  have hbsupp : b ∈ sp.support := mem_support.mpr (by rw [hσba]; exact hab)
  have hcsupp : c ∈ sp.support := mem_support.mpr (by rw [hσcd]; exact hcd.symm)
  have hdsupp : d ∈ sp.support := mem_support.mpr (by rw [hσdc]; exact hcd)
  -- The commutator element.
  set ρ : alternatingGroup α := τ * σ * τ⁻¹ * σ⁻¹ with hρ
  have hρcoe : (ρ : Perm α) = τp * sp * τp⁻¹ * sp⁻¹ := by
    rw [hρ]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτ, hsp]
  -- Support containment: `ρ.support ⊆ {c, d, e, σ e}`.
  have hsuppbound : (ρ : Perm α).support ⊆ ({c, d, e, sp e} : Finset α) := by
    rw [hρcoe]
    have hassoc : τp * sp * τp⁻¹ * sp⁻¹ = τp * (sp * τp⁻¹ * sp⁻¹) := by
      group
    rw [hassoc]
    intro x hx
    have hx2 : x ∈ τp.support ∪ (sp * τp⁻¹ * sp⁻¹).support := by
      have h := support_mul_le τp (sp * τp⁻¹ * sp⁻¹) hx
      simpa only [Finset.sup_eq_union] using h
    rw [Finset.mem_union] at hx2
    rcases hx2 with hx2 | hx2
    · have := hτsub hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    · rw [support_conj, support_inv, Finset.mem_map] at hx2
      obtain ⟨y, hy, hxy⟩ := hx2
      simp only [Equiv.coe_toEmbedding] at hxy
      have hy3 := hτsub hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy3
      rw [← hxy]
      rcases hy3 with rfl | rfl | rfl
      · rw [hσcd]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      · rw [hσdc]; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      · simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine ⟨ρ, ?_, ?_, ?_⟩
  · rw [hρ]; exact commutator_mem_of_normal hHn hσH τ
  · -- `ρ ≠ 1`, since its underlying permutation sends `d` to `e ≠ d`.
    have hρd : (ρ : Perm α) d = e := by
      rw [hρcoe]
      simp only [Equiv.Perm.mul_apply]
      rw [hspinvd, hτpinvc, hσdc, hτpc]
    intro hρ1
    have hd1 : (ρ : Perm α) d = d := by
      rw [hρ1, Subgroup.coe_one, Equiv.Perm.one_apply]
    rw [hρd] at hd1
    exact hde hd1.symm
  · -- Support strictly smaller.
    -- `ρ` fixes `a` and `b`.
    have hρa : (ρ : Perm α) a = a := by
      rw [hρcoe]; simp only [Equiv.Perm.mul_apply]
      rw [hspinva, hτpinvb, hσba, hτpa]
    have hρb : (ρ : Perm α) b = b := by
      rw [hρcoe]; simp only [Equiv.Perm.mul_apply]
      rw [hspinvb, hτpinva, hσab, hτpb]
    by_cases he : e ∈ sp.support
    · -- `σ` moves all five distinct points, so `#σ.support ≥ 5`.
      have hT5 : ({a, b, c, d, e} : Finset α).card = 5 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hab, hac, had, hae⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hbc, hbd, hbe⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hcd, hce⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hde),
            Finset.card_singleton]
      have hTsub : ({a, b, c, d, e} : Finset α) ⊆ sp.support := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact hasupp
        · exact hbsupp
        · exact hcsupp
        · exact hdsupp
        · exact he
      have hσ5 : 5 ≤ sp.support.card := by
        calc 5 = ({a, b, c, d, e} : Finset α).card := hT5.symm
          _ ≤ sp.support.card := Finset.card_le_card hTsub
      have hρ4 : (ρ : Perm α).support.card ≤ 4 := by
        have hb0 : (ρ : Perm α).support.card ≤ ({c, d, e, sp e} : Finset α).card :=
          Finset.card_le_card hsuppbound
        have h1 : ({c, d, e, sp e} : Finset α).card ≤ ({d, e, sp e} : Finset α).card + 1 :=
          Finset.card_insert_le _ _
        have h2 : ({d, e, sp e} : Finset α).card ≤ ({e, sp e} : Finset α).card + 1 :=
          Finset.card_insert_le _ _
        have h3 : ({e, sp e} : Finset α).card ≤ ({sp e} : Finset α).card + 1 :=
          Finset.card_insert_le _ _
        have h4 : ({sp e} : Finset α).card = 1 := Finset.card_singleton _
        omega
      omega
    · -- `σ e = e`, so `ρ.support ⊆ {c, d, e}`.
      have hspe : sp e = e := notMem_support.mp he
      have hsub3 : (ρ : Perm α).support ⊆ ({c, d, e} : Finset α) := by
        intro x hx
        have := hsuppbound hx
        rw [hspe] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
        tauto
      have hρ3 : (ρ : Perm α).support.card ≤ 3 := by
        have hb0 : (ρ : Perm α).support.card ≤ ({c, d, e} : Finset α).card :=
          Finset.card_le_card hsub3
        have h1 : ({c, d, e} : Finset α).card ≤ ({d, e} : Finset α).card + 1 :=
          Finset.card_insert_le _ _
        have h2 : ({d, e} : Finset α).card ≤ ({e} : Finset α).card + 1 :=
          Finset.card_insert_le _ _
        have h3 : ({e} : Finset α).card = 1 := Finset.card_singleton _
        omega
      have hσ4 : 4 ≤ sp.support.card := by
        have hS4 : ({a, b, c, d} : Finset α).card = 4 := by
          rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hab, hac, had⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hbc, hbd⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]; exact hcd),
              Finset.card_singleton]
        have hSsub : ({a, b, c, d} : Finset α) ⊆ sp.support := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hasupp
          · exact hbsupp
          · exact hcsupp
          · exact hdsupp
        calc 4 = ({a, b, c, d} : Finset α).card := hS4.symm
          _ ≤ sp.support.card := Finset.card_le_card hSsub
      omega

/-! ### The classical combinatorial crux (fully proved) -/

/-- **Crux (0 sorry).** A nonidentity element `σ` of a normal subgroup `H ⊴ Aₙ`
(`n ≥ 5`) whose support is *minimal* among the nonidentity elements of `H` is a
3-cycle.

`#support = 3` is immediate (`card_support_eq_three_iff`).  For `#support ≥ 4` we
derive a contradiction by exhibiting a strictly smaller nonidentity element of `H`:

* `σ² = 1` (**Case B**, involution): extract two disjoint transpositions `(a b)`,
  `(c d)` and a fifth point `e`; `exists_smaller_commutator_of_involution` closes it.
* `σ² ≠ 1` (**Case A**) with `#support ≥ 5`: extract `x, sp x, sp² x` (a length-`≥3`
  cycle) plus two more moved points; `exists_smaller_commutator_of_five_points` closes it.
* `σ² ≠ 1` with `#support = 4`: then `σ` is a 4-cycle `(x, sp x, sp² x, d)`, which is
  *odd* (`IsCycle.sign`), contradicting `σ ∈ Aₙ`. -/
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
  · -- `#support ≥ 4`: no support-minimal `σ` can move ≥ 4 points, so this branch is
    -- vacuous.  We produce a strictly smaller nonidentity element of `H`.
    exfalso
    set sp : Perm α := (σ : Perm α) with hsp
    have h4' : 4 ≤ sp.support.card := h4
    by_cases hsq : ∀ x, sp (sp x) = x
    · -- **Case B: `σ² = 1` (involution).** Extract two disjoint transpositions and a
      -- fifth point, then apply `exists_smaller_commutator_of_involution`.
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < sp.support.card)
      have haa : sp a ≠ a := mem_support.mp ha
      have hbmem : sp a ∈ sp.support := by
        rw [mem_support, hsq a]; exact fun h => haa h.symm
      have hab' : a ≠ sp a := fun h => haa h.symm
      -- Third moved point `c ∉ {a, sp a}`.
      have hsub_ab : ({a, sp a} : Finset α) ⊆ sp.support := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hbmem
      have hcard_ab : ({a, sp a} : Finset α).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hab']), Finset.card_singleton]
      have hss_ab : ({a, sp a} : Finset α) ⊂ sp.support := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hsub_ab, ?_⟩
        intro heq; rw [heq] at hcard_ab; omega
      obtain ⟨c, hc_supp, hc_notab⟩ := Finset.exists_of_ssubset hss_ab
      have hcc : sp c ≠ c := mem_support.mp hc_supp
      have hc_ne_a : c ≠ a := fun h => hc_notab (by rw [h]; simp)
      have hc_ne_spa : c ≠ sp a := fun h => hc_notab (by rw [h]; simp)
      -- `d := sp c` is the partner of `c`.
      have hcd' : c ≠ sp c := fun h => hcc h.symm
      have hbd' : sp a ≠ sp c := fun h => (hc_ne_a) (sp.injective h).symm
      have h_a_ne_spc : a ≠ sp c := by
        intro h
        have hca : sp a = c := by rw [h]; exact hsq c
        exact hc_ne_spa hca.symm
      -- Fifth point `e ∉ {a, sp a, c, sp c}`.
      have hcard_abcd : ({a, sp a, c, sp c} : Finset α).card = 4 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hab', hc_ne_a.symm, h_a_ne_spc⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hc_ne_spa.symm, hbd'⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hcd'),
            Finset.card_singleton]
      have hss_abcd : ({a, sp a, c, sp c} : Finset α) ⊂ Finset.univ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_univ _, ?_⟩
        intro heq
        have hcc := congrArg Finset.card heq
        rw [hcard_abcd, Finset.card_univ] at hcc; omega
      obtain ⟨e, -, he_not⟩ := Finset.exists_of_ssubset hss_abcd
      have he_a : a ≠ e := by rintro rfl; exact he_not (by simp)
      have he_b : sp a ≠ e := by rintro rfl; exact he_not (by simp)
      have he_c : c ≠ e := by rintro rfl; exact he_not (by simp)
      have he_d : sp c ≠ e := by rintro rfl; exact he_not (by simp)
      obtain ⟨ρ, hρH, hρ1, hρlt⟩ :=
        exists_smaller_commutator_of_involution (σ := σ) (a := a) (b := sp a)
          (c := c) (d := sp c) (e := e) hHn hσH
          hab' hc_ne_a.symm h_a_ne_spc he_a hc_ne_spa.symm hbd' he_b hcd' he_c he_d
          rfl (hsq a) rfl (hsq c)
      exact absurd (hmin ρ hρH hρ1) (not_le.mpr hρlt)
    · -- **Case A: `σ² ≠ 1`.**  There is `x` with `sp (sp x) ≠ x`; then `a = x`,
      -- `b = sp x`, `c = sp (sp x)` are three distinct moved points on one cycle.
      push_neg at hsq
      obtain ⟨x, hx⟩ := hsq
      have haa : sp x ≠ x := by intro h; exact hx (by rw [h, h])
      have hab' : x ≠ sp x := fun h => haa h.symm
      have hbc' : sp x ≠ sp (sp x) := fun h => hab' (sp.injective h)
      have hac' : x ≠ sp (sp x) := fun h => hx h.symm
      have haS : x ∈ sp.support := mem_support.mpr haa
      have hbS : sp x ∈ sp.support := mem_support.mpr hbc'.symm
      have hcS : sp (sp x) ∈ sp.support := by
        rw [mem_support]; intro h; exact hbc' (sp.injective h).symm
      -- `d`, a fourth moved point.
      have hsub3 : ({x, sp x, sp (sp x)} : Finset α) ⊆ sp.support := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact haS
        · exact hbS
        · exact hcS
      have hcard3 : ({x, sp x, sp (sp x)} : Finset α).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hab', hac'⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hbc'),
            Finset.card_singleton]
      have hss3 : ({x, sp x, sp (sp x)} : Finset α) ⊂ sp.support := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨hsub3, ?_⟩
        intro heq; rw [heq] at hcard3; omega
      obtain ⟨d, hdS, hd_not⟩ := Finset.exists_of_ssubset hss3
      have hxd : x ≠ d := by rintro rfl; exact hd_not (by simp)
      have hbd : sp x ≠ d := by rintro rfl; exact hd_not (by simp)
      have hcd : sp (sp x) ≠ d := by rintro rfl; exact hd_not (by simp)
      by_cases hcard5 : 5 ≤ sp.support.card
      · -- `#support ≥ 5`: a fifth moved point `e`, then engine A closes it.
        have hsub4 : ({x, sp x, sp (sp x), d} : Finset α) ⊆ sp.support := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact haS
          · exact hbS
          · exact hcS
          · exact hdS
        have hcard4 : ({x, sp x, sp (sp x), d} : Finset α).card = 4 := by
          rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hab', hac', hxd⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hbc', hbd⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]; exact hcd),
              Finset.card_singleton]
        have hss4 : ({x, sp x, sp (sp x), d} : Finset α) ⊂ sp.support := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨hsub4, ?_⟩
          intro heq; rw [heq] at hcard4; omega
        obtain ⟨e, heS, he_not⟩ := Finset.exists_of_ssubset hss4
        have hxe : x ≠ e := by rintro rfl; exact he_not (by simp)
        have hbe : sp x ≠ e := by rintro rfl; exact he_not (by simp)
        have hce : sp (sp x) ≠ e := by rintro rfl; exact he_not (by simp)
        have hde : d ≠ e := by rintro rfl; exact he_not (by simp)
        obtain ⟨ρ, hρH, hρ1, hρlt⟩ :=
          exists_smaller_commutator_of_five_points (σ := σ) (a := x) (b := sp x)
            (c := sp (sp x)) (d := d) (e := e) hHn hσH
            hab' hac' hxd hxe hbc' hbd hbe hcd hce hde
            hbS hcS hdS heS rfl rfl
        exact absurd (hmin ρ hρH hρ1) (not_le.mpr hρlt)
      · -- `#support = 4` with `σ² ≠ 1`: then `σ` is the 4-cycle
        -- `(x, sp x, sp² x, d)`, which is *odd* — contradicting `σ ∈ Aₙ`.
        have hsupp4 : sp.support.card = 4 := by omega
        have hsub4 : ({x, sp x, sp (sp x), d} : Finset α) ⊆ sp.support := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact haS
          · exact hbS
          · exact hcS
          · exact hdS
        have hcard4 : ({x, sp x, sp (sp x), d} : Finset α).card = 4 := by
          rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hab', hac', hxd⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨hbc', hbd⟩),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]; exact hcd),
              Finset.card_singleton]
        -- The support is exactly `{x, sp x, sp² x, d}`.
        have hsupp_eq : sp.support = ({x, sp x, sp (sp x), d} : Finset α) :=
          (Finset.eq_of_subset_of_card_le hsub4 (le_of_eq (by rw [hsupp4, hcard4]))).symm
        -- `sp³ x` lies in the support and is forced to equal `d`.
        have h3mem : sp (sp (sp x)) ∈ sp.support := apply_mem_support.mpr hcS
        have h3ne2 : sp (sp (sp x)) ≠ sp (sp x) := mem_support.mp hcS
        have h3ne1 : sp (sp (sp x)) ≠ sp x := fun h => hac' (sp.injective h).symm
        have hdd : sp d ≠ d := mem_support.mp hdS
        have h3nex : sp (sp (sp x)) ≠ x := by
          intro h
          have hdmem : sp d ∈ sp.support := apply_mem_support.mpr hdS
          rw [hsupp_eq] at hdmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
          rcases hdmem with h1 | h2 | h3 | h4
          · exact hd_not (by
              rw [show d = sp (sp x) from sp.injective (h1.trans h.symm)]; simp)
          · exact hd_not (by rw [show d = x from sp.injective h2]; simp)
          · exact hd_not (by rw [show d = sp x from sp.injective h3]; simp)
          · exact hdd h4
        have hsp3d : sp (sp (sp x)) = d := by
          have hmem := h3mem
          rw [hsupp_eq] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h | h
          · exact absurd h h3nex
          · exact absurd h h3ne1
          · exact absurd h h3ne2
          · exact h
        -- `σ` is a single cycle (the 4-cycle `x → sp x → sp² x → d → x`).
        have hcyc : sp.IsCycle := by
          refine ⟨x, haa, ?_⟩
          intro y hy
          have hy' : y ∈ sp.support := mem_support.mpr hy
          rw [hsupp_eq] at hy'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
          have sc1 : sp.SameCycle x (sp x) := sameCycle_apply_right.mpr (SameCycle.refl sp x)
          have sc2 : sp.SameCycle x (sp (sp x)) := sameCycle_apply_right.mpr sc1
          have sc3 : sp.SameCycle x (sp (sp (sp x))) := sameCycle_apply_right.mpr sc2
          rcases hy' with h | h | h | h
          · rw [h]
          · rw [h]; exact sc1
          · rw [h]; exact sc2
          · rw [h, ← hsp3d]; exact sc3
        -- A cycle supported on 4 points is odd, contradicting `sign σ = 1`.
        have hsign : Perm.sign sp = -1 := by rw [hcyc.sign, hsupp4]; decide
        have hsign1 : Perm.sign sp = 1 := mem_alternatingGroup.mp σ.2
        rw [hsign] at hsign1
        exact absurd hsign1 (by decide)

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

/-- **Unconditional simplicity of `Aₙ` for `n ≥ 5` (0 sorry, 0 axiom).** Feeds the
classical 3-cycle lemma into the parent file's formal reduction
(`isSimpleGroup_of_forall_normal_contains_threeCycle`).  This generalizes Mathlib's
`Fin 5`-only `alternatingGroup.isSimpleGroup_five` to every finite `α` with
`5 ≤ card α`. -/
theorem isSimpleGroup_alternating (h5 : 5 ≤ Fintype.card α) :
    IsSimpleGroup (alternatingGroup α) :=
  isSimpleGroup_of_forall_normal_contains_threeCycle
    h5 (fun H hHn hbot => exists_mem_isThreeCycle_of_normal h5 H hHn hbot)

end AbelRuffiniGaloisExtensionsOQ03OQ01
