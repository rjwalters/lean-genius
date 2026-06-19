/-
  Aristotle companion for `abel-ruffini-oq-07` (Gal(X⁵ − X − 1) ≅ S₅).

  ## Why this file exists
  The gallery entry `AbelRuffiniOQ07.lean` is a fully verified (0 sorry / 0 axiom)
  group-theoretic *reduction*: it proves `Gal(X⁵−X−1) ≅ S₅` modulo two number-theoretic
  inputs, of which `5 ∣ |Gal|` is now discharged unconditionally from Selmer's
  irreducibility theorem.  The SOLE remaining input is a **transposition** in the Galois
  group, which comes from the order-6 Frobenius at `p = 2`.

  The abstract Dedekind–Frobenius bridge `orderOf (arithFrobAt R G Q) = inertiaDegIn p S`
  is now PROVED and axiom-free in `DedekindFrobeniusBridge.lean`.  Instantiated at
  `R = ℤ`, `S = 𝓞 K`, `G = Gal`, and a prime `Q` over `2` (where the residue degree in
  the degree-120 splitting field equals the order of the Frobenius, namely `6`), it yields
  an element `σ ∈ f.Gal` with `orderOf σ = 6`.

  The generic group-theoretic step that turns that order-6 element into the swap the
  reduction consumes is the lemma below — the generic form of the concrete
  `frob2_pow_three_isSwap` already in the gallery file.  It is pure `S₅` combinatorics
  (Mathlib-only, no `Proofs.*` dependency), hence a clean Aristotle target.

  ## Math content
  In `S₅` the only cycle type of order `6` is `(2,3)` (partitions of `5` with `lcm = 6`:
  a part divisible by `3` forces a `3`, leaving sum `≤ 2`, so a single `2`; `6 ∉ {2..5}`).
  An element of cycle type `(2,3)` is `c₂ · c₃` (disjoint), whose cube is `c₂ · c₃³ = c₂`,
  a transposition.  Hence `orderOf σ = 6 ⟹ (σ ^ 3).IsSwap`.

  ## Axiom disclosure
  `orderOf_eq_six_pow_three_isSwap` closes the finite `S₅` case-check with `native_decide`,
  which trusts the compiler's kernel reduction and therefore depends on `Lean.ofReduceBool`
  (and `Lean.trustCompiler`) in addition to the usual `propext`/`Classical.choice`/`Quot.sound`.
  This companion is NOT axiom-free; an integration into the verified gallery reduction
  (`AbelRuffiniOQ07.lean`) would need a `decide`-free re-proof to preserve its 0-axiom status.
-/
import Mathlib

open Equiv Equiv.Perm

namespace AbelRuffiniOQ07Order6

/-- **The generic order-6 ⟹ transposition step.**
    In `S₅`, an element of order `6` necessarily has cycle type `(2,3)`, so its cube is a
    transposition.  This is the reusable form of the gallery file's concrete
    `frob2_pow_three_isSwap`; combined with the now-proved Dedekind–Frobenius bridge
    (which supplies an order-6 element of `f.Gal` from the inertia degree at `p = 2`), it
    discharges the last open input of `abel-ruffini-oq-07`. -/
theorem orderOf_eq_six_pow_three_isSwap
    (σ : Equiv.Perm (Fin 5)) (hσ : orderOf σ = 6) : (σ ^ 3).IsSwap := by
  revert σ
  simp +decide [orderOf_eq_iff]
  intro σ hσ hσ'
  simp_all +decide [Equiv.Perm.IsSwap]
  native_decide +revert

/-- **Consumer assembly variant (real Galois-group facing).**
    A subgroup `G ≤ S₅` with `5 ∣ |G|` that contains an order-6 element equals `⊤`.
    This is `gal_eq_top_of_five_dvd_and_swap` with the swap input replaced by the
    order-6 element the bridge produces, so the open gap of `abel-ruffini-oq-07` becomes
    exactly "`∃ σ ∈ Gal, orderOf σ = 6`" — the abstract bridge's output. -/
theorem gal_eq_top_of_five_dvd_and_order6
    {G : Subgroup (Equiv.Perm (Fin 5))} [DecidablePred (· ∈ G)]
    (h5 : 5 ∣ Fintype.card G)
    {σ : Equiv.Perm (Fin 5)} (hσG : σ ∈ G) (hσ : orderOf σ = 6) :
    G = ⊤ := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 5), τ ∈ G ∧ τ.IsSwap := by
    exact ⟨σ ^ 3, pow_mem hσG 3, orderOf_eq_six_pow_three_isSwap σ hσ⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin 5, a ≠ b ∧ τ = swap a b := hτ.2
  apply Equiv.Perm.subgroup_eq_top_of_swap_mem
  all_goals norm_num [hab]
  exacts [h5, hτ.1, hτ.2]

end AbelRuffiniOQ07Order6
