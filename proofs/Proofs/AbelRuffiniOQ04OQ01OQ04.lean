/-
  Abel–Ruffini, concrete-quintic branch (oq-04-oq-01), open question oq-04.

  The parent entry (`AbelRuffiniOQ04OQ01`, "Gal(x⁵−4x+2) ≅ S₅") documents, in a
  comment block, the classical

      **Key Group Theory Lemma.** A transitive subgroup of `S_p` (`p` prime)
      that contains a transposition is all of `S_p`.

  but — as oq-04 records — "the formal proof of this classical result is not
  included; the current proof avoids it via Sylow." This file supplies that
  missing proof, axiom-free, by assembling standard Mathlib results:

    * transitivity + orbit–stabilizer  ⟹  `p ∣ |G|`;
    * Cauchy's theorem                 ⟹  `G` contains an element `σ` of order `p`;
    * an order-`p` permutation of a `p`-element set is a `p`-cycle with full
      support (`isCycle_of_prime_order`, `IsCycle.orderOf`);
    * a `p`-cycle together with any transposition generates `S_p`
      (`closure_prime_cycle_swap`).

  Hence `⟨σ, τ⟩ = ⊤ ≤ G`, so `G = ⊤`. This is the general lemma behind the
  concrete computation `Gal(x⁵ − 4x + 2) ≅ S₅`.
-/

import Mathlib

open Equiv Equiv.Perm Subgroup MulAction

namespace AbelRuffiniOQ04OQ01OQ04

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Key Group Theory Lemma (transitive + a transposition ⟹ full symmetric group).**

If `α` has a prime number of elements and `G ≤ S_α` acts transitively on `α`
and contains a transposition, then `G = ⊤`. -/
theorem eq_top_of_isPretransitive_of_mem_isSwap
    (hp : (Fintype.card α).Prime)
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α]
    {τ : Equiv.Perm α} (hτ : τ ∈ G) (hτswap : τ.IsSwap) :
    G = ⊤ := by
  classical
  haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
  -- `α` is nonempty (its cardinality is a prime ≥ 2).
  have hcard2 : 2 ≤ Fintype.card α := hp.two_le
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  -- Orbit–stabilizer + transitivity give `card α ∣ |G|`.
  have horbit : Fintype.card (orbit G a) = Fintype.card α :=
    Fintype.card_congr ((Equiv.setCongr (MulAction.orbit_eq_univ G a)).trans (Equiv.Set.univ α))
  have hpdvd : Fintype.card α ∣ Fintype.card G := by
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (α := G) a
    refine ⟨Fintype.card (stabilizer G a), ?_⟩
    rw [← hos, horbit]
  -- Cauchy: `G` contains an element `σ` of order `card α = p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) hpdvd
  have hσord : orderOf (g : Equiv.Perm α) = Fintype.card α := by
    rw [orderOf_coe]; exact hg
  -- An order-`p` permutation of a `p`-element set is a `p`-cycle…
  have hσcyc : (g : Equiv.Perm α).IsCycle := by
    refine isCycle_of_prime_order (by rw [hσord]; exact hp) ?_
    rw [hσord]
    calc ((g : Equiv.Perm α).support.card) ≤ Fintype.card α := Finset.card_le_univ _
      _ < 2 * Fintype.card α := by omega
  -- …with full support.
  have hσsupp : (g : Equiv.Perm α).support = Finset.univ := by
    have h1 := hσcyc.orderOf
    rw [hσord] at h1
    exact Finset.eq_univ_of_card _ h1.symm
  -- A `p`-cycle and a transposition generate `S_p`.
  have hgen : Subgroup.closure (({(g : Equiv.Perm α), τ}) : Set (Equiv.Perm α)) = ⊤ :=
    closure_prime_cycle_swap hp hσcyc hσsupp hτswap
  -- Both generators lie in `G`, so `⊤ = ⟨σ, τ⟩ ≤ G`.
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact g.2
  · exact hτ

end AbelRuffiniOQ04OQ01OQ04
