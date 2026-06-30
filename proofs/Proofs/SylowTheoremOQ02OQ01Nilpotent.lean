/-
# Nilpotency of a Finite Group via its Sylow Subgroups

OQ-02-OQ-01 follow-up to sylow-theorem (`sylow-theorem-oq-02`).

The parent entry `sylow-theorem-oq-02` enumerated the Sylow p-subgroups via the
conjugation orbit, obtaining `n_p = [G : N_G(P)]` and the per-prime criterion
`n_p = 1 ↔ P ◁ G`.  This file lifts that *local* (single prime) picture to a
*global* structural characterization of the whole group:

  For a finite group G, the following are equivalent:
    (1) G is nilpotent;
    (4) every Sylow p-subgroup of G is normal;
    (★) every Sylow count is one:  n_p = #(Sylow p G) = 1 for all primes p.

Mathlib already provides the five-way TFAE `isNilpotent_of_finite_tfae`
(nilpotent ⟺ normalizer condition ⟺ all maximal subgroups normal ⟺ all Sylow
normal ⟺ internal direct product of Sylow subgroups).  Our contribution is to

  * extract the clean two-way headline `nilpotent ⟺ all Sylow normal`, and
  * fuse it with Sylow *uniqueness* (`Sylow.unique_of_normal` /
    `Sylow.normal_of_subsingleton`) to obtain the counting form
    `nilpotent ⟺ ∀ p, n_p = 1`,

which is the bridge back to the parent's `n_p = [G : N_G(P)]`: nilpotency forces
`N_G(P) = G`, hence index — and therefore the Sylow count — equals one.

## Main Results

- `nilpotent_iff_forall_sylow_normal` : `IsNilpotent G ↔ ∀ p P, (P : Subgroup G).Normal`
- `sylow_normal_of_nilpotent`         : nilpotent ⇒ every Sylow p-subgroup is normal
- `nilpotent_iff_forall_card_sylow_eq_one` : `IsNilpotent G ↔ ∀ p, #(Sylow p G) = 1`
- `normalizer_eq_top_of_nilpotent`    : nilpotent ⇒ `N_G(P) = ⊤` (so `[G : N_G(P)] = 1`)

## Tags
group-theory, sylow, nilpotent, finite-groups, normalizer
-/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

namespace SylowNilpotent

variable {G : Type*} [Group G] [Finite G]

/-- **Headline equivalence.**  A finite group is nilpotent iff *every* Sylow
p-subgroup (for every prime p) is normal.  This is the `(1) ↔ (4)` slice of
Mathlib's five-way `isNilpotent_of_finite_tfae`. -/
theorem nilpotent_iff_forall_sylow_normal :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), (P : Subgroup G).Normal :=
  (isNilpotent_of_finite_tfae (G := G)).out 0 3

/-- Forward direction, packaged for convenience: in a finite nilpotent group every
Sylow p-subgroup is normal. -/
theorem sylow_normal_of_nilpotent (h : Group.IsNilpotent G)
    (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) : (P : Subgroup G).Normal :=
  (nilpotent_iff_forall_sylow_normal.mp h) p hp P

/-- In a finite nilpotent group the normalizer of every Sylow p-subgroup is the
whole group.  Combined with the parent result `n_p = [G : N_G(P)]`, this is the
reason the Sylow count collapses to one. -/
theorem normalizer_eq_top_of_nilpotent (h : Group.IsNilpotent G)
    (p : ℕ) [hp : Fact p.Prime] (P : Sylow p G) :
    (P : Subgroup G).normalizer = ⊤ :=
  Subgroup.normalizer_eq_top_iff.mpr (sylow_normal_of_nilpotent h p P)

/-- **Counting characterization.**  A finite group is nilpotent iff every Sylow
count is one, i.e. for each prime `p` there is a *unique* Sylow p-subgroup.

This is the global counterpart of the parent's per-prime criterion
`n_p = 1 ↔ P ◁ G`: nilpotency is exactly the statement that *all* of these
local uniqueness conditions hold simultaneously. -/
theorem nilpotent_iff_forall_card_sylow_eq_one :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) (_hp : Fact p.Prime), Nat.card (Sylow p G) = 1 := by
  rw [nilpotent_iff_forall_sylow_normal]
  constructor
  · -- all Sylow normal ⇒ each is unique, so the count is one
    intro h p hp
    haveI := hp
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
    haveI := Sylow.unique_of_normal P (h p hp P)
    exact Nat.card_unique
  · -- count one ⇒ subsingleton ⇒ the (unique) Sylow subgroup is characteristic, hence normal
    intro h p hp P
    haveI := hp
    have hcard : Nat.card (Sylow p G) = 1 := h p hp
    haveI : Subsingleton (Sylow p G) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Sylow.normal_of_subsingleton P

end SylowNilpotent
