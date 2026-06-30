/-
  Abel–Ruffini, concrete-quintic branch — OQ-04-OQ-01-OQ-04-OQ-01:
  from the Key Group Theory Lemma to the NON-SOLVABILITY obstruction.

  ## Question
  The parent entry (`AbelRuffiniOQ04OQ01OQ04`) proves the Key Group Theory Lemma:
  a transitive subgroup `G ≤ S_p` (`p` prime) containing a transposition is all of
  `S_p`. Its open question is the payoff for Abel–Ruffini: such a `G` is the FULL
  symmetric group, hence — for `p ≥ 5` — **not solvable**. Combined with the Galois
  correspondence (a polynomial is solvable by radicals iff its Galois group is
  solvable, `Polynomial.solvableByRad`), this is exactly the group-theoretic
  obstruction that makes the general quintic unsolvable.

  This file supplies that step, axiom-free: it re-proves the Key Lemma
  self-contained (so the file stands alone) and then derives

      a transitive subgroup of `S_p` with a transposition and `p ≥ 5` is not
      solvable,

  by transporting Mathlib's `Equiv.Perm.not_solvable` across `Subgroup.topEquiv`.

  ## What this file delivers (0 axioms, 0 sorries)
  * `eq_top_of_isPretransitive_of_mem_isSwap` — the Key Lemma (re-proved).
  * `not_isSolvable_of_isPretransitive_of_mem_isSwap` — the obstruction: such a `G`
    is not solvable when `5 ≤ card α`.
  * `not_isSolvable_top` — corollary: `S_α` itself is not solvable for `5 ≤ card α`,
    phrased for the top subgroup.

  ## References
  - N. H. Abel (1824); P. Ruffini (1799); É. Galois (1831).
  - Mathlib: `Equiv.Perm.not_solvable`, `closure_prime_cycle_swap`.

  Tags: algebra, galois-theory, abel-ruffini, solvability, symmetric-group
-/

import Mathlib

open Equiv Equiv.Perm Subgroup MulAction

namespace AbelRuffiniOQ04OQ01OQ04OQ01

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Key Group Theory Lemma (transitive + a transposition ⟹ full symmetric group).**
If `α` has a prime number of elements and `G ≤ S_α` acts transitively and contains
a transposition, then `G = ⊤`. (Re-proved self-contained from the parent entry.) -/
theorem eq_top_of_isPretransitive_of_mem_isSwap
    (hp : (Fintype.card α).Prime)
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α]
    {τ : Equiv.Perm α} (hτ : τ ∈ G) (hτswap : τ.IsSwap) :
    G = ⊤ := by
  classical
  haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
  have hcard2 : 2 ≤ Fintype.card α := hp.two_le
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have horbit : Fintype.card (orbit G a) = Fintype.card α :=
    Fintype.card_congr ((Equiv.setCongr (MulAction.orbit_eq_univ G a)).trans (Equiv.Set.univ α))
  have hpdvd : Fintype.card α ∣ Fintype.card G := by
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := G) a
    refine ⟨Fintype.card (stabilizer G a), ?_⟩
    rw [← hos, horbit]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) hpdvd
  have hσord : orderOf (g : Equiv.Perm α) = Fintype.card α := by
    rw [orderOf_coe]; exact hg
  have hσcyc : (g : Equiv.Perm α).IsCycle := by
    refine isCycle_of_prime_order (by rw [hσord]; exact hp) ?_
    rw [hσord]
    calc ((g : Equiv.Perm α).support.card) ≤ Fintype.card α := Finset.card_le_univ _
      _ < 2 * Fintype.card α := by omega
  have hσsupp : (g : Equiv.Perm α).support = Finset.univ := by
    have h1 := hσcyc.orderOf
    rw [hσord] at h1
    exact Finset.eq_univ_of_card _ h1.symm
  have hgen : Subgroup.closure (({(g : Equiv.Perm α), τ}) : Set (Equiv.Perm α)) = ⊤ :=
    closure_prime_cycle_swap hp hσcyc hσsupp hτswap
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact g.2
  · exact hτ

-- ============================================================
-- The Abel–Ruffini obstruction: non-solvability for p ≥ 5
-- ============================================================

omit [DecidableEq α] in
/-- The full symmetric group on `α` is not solvable when `5 ≤ card α`, phrased for
the top subgroup (`Subgroup.topEquiv : ⊤ ≃* S_α`). -/
theorem not_isSolvable_top (h5 : 5 ≤ Fintype.card α) :
    ¬ IsSolvable (⊤ : Subgroup (Equiv.Perm α)) := by
  intro hsolv
  have hperm : IsSolvable (Equiv.Perm α) :=
    solvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm α)) ≃* _).toMonoidHom)
      (Subgroup.topEquiv).surjective
  refine Equiv.Perm.not_solvable α ?_ hperm
  rw [Cardinal.mk_fintype]
  exact_mod_cast h5

/-- **The Abel–Ruffini obstruction.** A transitive subgroup of `S_p` (`p` prime,
`p ≥ 5`) that contains a transposition is the full symmetric group and is therefore
**not solvable**. Via the Galois correspondence this is exactly what blocks
solvability by radicals: any polynomial whose Galois group is such a `G` is not
solvable by radicals. -/
theorem not_isSolvable_of_isPretransitive_of_mem_isSwap
    (hp : (Fintype.card α).Prime) (h5 : 5 ≤ Fintype.card α)
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α]
    {τ : Equiv.Perm α} (hτ : τ ∈ G) (hτswap : τ.IsSwap) :
    ¬ IsSolvable G := by
  have htop : G = ⊤ := eq_top_of_isPretransitive_of_mem_isSwap hp G hτ hτswap
  subst htop
  exact not_isSolvable_top h5

#check @eq_top_of_isPretransitive_of_mem_isSwap
#check @not_isSolvable_top
#check @not_isSolvable_of_isPretransitive_of_mem_isSwap

end AbelRuffiniOQ04OQ01OQ04OQ01
