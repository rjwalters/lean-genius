/-
  Cauchy strengthening of the discriminant-route assembler for
  Gal(X⁵ − X − 1 / ℚ) ≅ S₅  (abel-ruffini OQ-07, discriminant variant).

  ## Background
  The merged file `AbelRuffiniOQ07Discriminant.lean` proves the discriminant-route
  assembler

      gal_eq_top_of_transitive_threeCycle_odd :
        IsPretransitive G (Fin 5) → g.IsThreeCycle → g ∈ G →
        h ∉ alternatingGroup (Fin 5) → h ∈ G → G = ⊤

  i.e. a transitive `G ≤ S₅` containing a **3-cycle** and an **odd permutation** is
  all of `S₅` (prime degree ⟹ primitive; Jordan ⟹ `A₅ ≤ G`; odd ⟹ index 1).
  That statement takes "`G` contains a 3-cycle" as a hypothesis.

  ## This file: discharge the 3-cycle hypothesis via Cauchy
  Classically the 3-cycle is produced not by exhibiting a specific permutation but
  from the **divisibility** `3 ∣ |Gal|` (which is unconditional for `X⁵ − X − 1`):
  Cauchy's theorem yields an element of order 3, and in `S₅` *every* element of
  order 3 is automatically a 3-cycle (there is no room for two disjoint 3-cycles on
  5 points). This file supplies that missing combinatorial bridge and assembles the
  fully-reduced criterion.

  ## What this file verifies (0 sorry, 0 axiom)
    * `isThreeCycle_of_orderOf_eq_three` — on `≤ 5` points, `orderOf g = 3` forces
      `g.IsThreeCycle`. The reusable group-theory content.
    * `gal_eq_top_of_transitive_orderThree_odd` — the assembler with the hypothesis
      `g.IsThreeCycle` weakened to `orderOf g = 3`.
    * `gal_eq_top_of_three_dvd_card_transitive_odd` — the classical criterion in its
      sharpest form: a transitive `G ≤ S₅` with `3 ∣ |G|` and *some* odd permutation
      equals `⊤`. The 3-cycle is now extracted internally by Cauchy.

  The remaining (still-open, Mathlib-absent) inputs are the number-theoretic bridges
  `3 ∣ |Gal|` and "the non-square discriminant 2869 gives an odd permutation"; those
  are exactly the hypotheses left exposed here. Everything below is machine-checked.
-/
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

open MulAction Equiv Equiv.Perm

/-- The symmetric group on the 5 roots. -/
abbrev S5 := Equiv.Perm (Fin 5)

/-- The degree is the prime 5. -/
theorem card_fin5_prime : Nat.Prime (Nat.card (Fin 5)) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num

/-!
## The combinatorial bridge: order 3 ⟹ 3-cycle on ≤ 5 points
-/

/-- On a finite type with **at most 5 points**, every permutation of order `3` is a
3-cycle.  Each cycle length divides `orderOf g = 3` and is `≥ 2`, hence equals `3`,
so the cycle type is `replicate k 3`; the support bound `3k ≤ 5` together with
`g ≠ 1` forces `k = 1`, i.e. cycle type `{3}`.  (For `n < 6` there is simply no room
for two disjoint 3-cycles.) -/
theorem isThreeCycle_of_orderOf_eq_three
    {α : Type*} [Fintype α] [DecidableEq α] (hcard : Fintype.card α ≤ 5)
    {g : Equiv.Perm α} (hg : orderOf g = 3) : g.IsThreeCycle := by
  -- every cycle length divides `orderOf g = 3` and is `≥ 2`, hence equals `3`
  have hparts : ∀ n ∈ g.cycleType, n = 3 := by
    intro n hn
    have hdvd : n ∣ 3 := by
      have h := Multiset.dvd_lcm hn
      rwa [Equiv.Perm.lcm_cycleType, hg] at h
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.prime_three.eq_one_or_self_of_dvd n hdvd) with h1 | h3
    · omega
    · exact h3
  -- so the cycle type is `replicate k 3`
  set k := Multiset.card g.cycleType with hk
  have hrep : g.cycleType = Multiset.replicate k 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, hparts⟩
  -- the support has size `3k`, and `3k ≤ card α ≤ 5`
  have hsum : g.cycleType.sum = k * 3 := by
    rw [hrep, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  have hle : g.cycleType.sum ≤ 5 := le_trans (Equiv.Perm.sum_cycleType_le g) hcard
  -- `g ≠ 1`, so `k ≥ 1`
  have hg1 : g ≠ 1 := by
    intro h; rw [h, orderOf_one] at hg; norm_num at hg
  have hpos : 0 < k := Equiv.Perm.card_cycleType_pos.mpr hg1
  have hk1 : k = 1 := by omega
  -- conclude: cycle type is `{3}`
  show g.cycleType = {3}
  rw [hrep, hk1, Multiset.replicate_one]

/-!
## The strengthened assemblers
-/

/-- Discriminant-route assembler with the 3-cycle hypothesis weakened to
`orderOf g = 3` (equivalent on `S₅` by `isThreeCycle_of_orderOf_eq_three`). -/
theorem gal_eq_top_of_transitive_orderThree_odd
    {G : Subgroup S5} (htrans : IsPretransitive G (Fin 5))
    {g : S5} (h3 : orderOf g = 3) (hg : g ∈ G)
    {h : S5} (hodd : h ∉ alternatingGroup (Fin 5)) (hhG : h ∈ G) :
    G = ⊤ := by
  haveI : IsPretransitive G (Fin 5) := htrans
  have hprim : IsPreprimitive G (Fin 5) := IsPreprimitive.of_prime_card card_fin5_prime
  have h3cyc : g.IsThreeCycle :=
    isThreeCycle_of_orderOf_eq_three (by simp) h3
  have hA : alternatingGroup (Fin 5) ≤ G :=
    alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3cyc hg
  have hdvd : G.index ∣ (alternatingGroup (Fin 5)).index := Subgroup.index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exact absurd ((eq_alternatingGroup_of_index_eq_two h2) ▸ hhG) hodd

/-- **Discriminant criterion, fully reduced.**  A transitive subgroup `G ≤ S₅` with
`3 ∣ |G|` and containing *some* odd permutation equals `⊤`.

The order-3 (hence 3-cycle) element is produced internally by Cauchy's theorem, so
the only remaining inputs are `3 ∣ |Gal|` and the non-square-discriminant datum
("`Gal` contains an odd permutation") — exactly the two number-theoretic facts the
classical Selmer argument supplies for `X⁵ − X − 1`. -/
theorem gal_eq_top_of_three_dvd_card_transitive_odd
    {G : Subgroup S5} [Fintype G] (htrans : IsPretransitive G (Fin 5))
    (h3 : 3 ∣ Fintype.card G)
    {h : S5} (hodd : h ∉ alternatingGroup (Fin 5)) (hhG : h ∈ G) :
    G = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hord : orderOf (x : S5) = 3 := (Subgroup.orderOf_coe x).trans hx
  exact gal_eq_top_of_transitive_orderThree_odd htrans hord x.2 hodd hhG
