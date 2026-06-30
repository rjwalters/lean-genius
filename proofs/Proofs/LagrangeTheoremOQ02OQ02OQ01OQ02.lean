import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-
# Fixed-Point Congruence and the Nontrivial Center of a p-Group
# (lagrange-theorem-oq-02-oq-02-oq-01-oq-02)

Lagrange's theorem (|H| divides |G|) is the gateway to the structure theory of
finite groups.  A `p`-group — a finite group whose order is a power of a prime
`p` — is the most rigid such structure, and the lever that controls it is a
single counting congruence coming from group actions.

**Burnside's fixed-point congruence.** If a `p`-group `G` acts on a finite set
`α`, then

    |α| ≡ |fixed points| (mod p),

because every non-singleton orbit has size a positive power of `p` (orbit–
stabilizer + Lagrange) and so vanishes mod `p`.

Applying this to `G` acting on itself by **conjugation** turns the fixed-point set
into the center `Z(G)`, and the congruence becomes the **class equation mod p**.
Since `p ∣ |G|` for a nontrivial `p`-group, it forces `p ∣ |Z(G)|`, so the center
cannot be trivial.  This is the cornerstone of the theory of `p`-groups (they are
nilpotent; Sylow theory; the classification of small groups).

This file packages the chain over Mathlib's `IsPGroup` development:

  * `card_modEq_card_fixedPoints` — the fixed-point congruence;
  * `nonempty_fixedPoints_of_not_dvd` — a fixed point exists when `p ∤ |α|`;
  * `center_nontrivial` — a nontrivial finite `p`-group has nontrivial center;
  * `bot_lt_center` — equivalently, `⊥ < Z(G)`;
  * `p_dvd_card_center` — and `p` divides `|Z(G)|`.

Each result is a thin wrapper around Mathlib's `IsPGroup` API; the contribution is
the packaged, named exposition of the orbit-counting ⟹ center-nontriviality chain.

Status: 0 axioms, 0 sorries
-/

namespace LagrangeTheoremOQ02OQ02OQ01OQ02

open scoped Pointwise

variable {p : ℕ} {G : Type*} [Group G] [Fact p.Prime] (hG : IsPGroup p G)

include hG

-- ============================================================================
-- Part I: Burnside's fixed-point congruence
-- ============================================================================

/-- **Fixed-point congruence.** If a `p`-group `G` acts on a finite set `α`, the
number of fixed points is congruent to `|α|` modulo `p`. Non-trivial orbits have
size a positive power of `p`, hence vanish mod `p`. -/
theorem card_modEq_card_fixedPoints (α : Type*) [MulAction G α] [Finite α] :
    Nat.card α ≡ Nat.card (MulAction.fixedPoints G α) [MOD p] :=
  IsPGroup.card_modEq_card_fixedPoints hG α

/-- If a `p`-group acts on `α` and `p` does not divide `|α|`, then the action has
a fixed point. The Cauchy/Cayley-style consequence of the congruence. -/
theorem nonempty_fixedPoints_of_not_dvd (α : Type*) [MulAction G α]
    (hpα : ¬ p ∣ Nat.card α) :
    (MulAction.fixedPoints G α).Nonempty :=
  IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hG α hpα

-- ============================================================================
-- Part II: The class equation and the center
-- ============================================================================

/-- **The center of a nontrivial finite `p`-group is nontrivial.** Applying the
fixed-point congruence to conjugation (whose fixed points are the center) gives
the class equation mod `p`; since `p ∣ |G|`, it forces `Z(G)` to be nontrivial. -/
theorem center_nontrivial [Nontrivial G] [Finite G] :
    Nontrivial (Subgroup.center G) :=
  IsPGroup.center_nontrivial hG

/-- Equivalently, the center strictly contains the trivial subgroup. -/
theorem bot_lt_center [Nontrivial G] [Finite G] :
    ⊥ < Subgroup.center G :=
  IsPGroup.bot_lt_center hG

/-- The prime `p` divides the order of the center of a nontrivial finite
`p`-group: the center is itself a nontrivial `p`-group, so its order is a positive
power of `p`. -/
theorem p_dvd_card_center [Nontrivial G] [Finite G] :
    p ∣ Nat.card (Subgroup.center G) := by
  haveI := IsPGroup.center_nontrivial hG
  obtain ⟨n, hn0, hn⟩ :=
    (IsPGroup.nontrivial_iff_card (IsPGroup.to_subgroup hG (Subgroup.center G))).mp inferInstance
  exact hn.symm ▸ dvd_pow_self p hn0.ne'

-- ============================================================================
-- Part III: Summary
-- ============================================================================

/-
## Summary

| Result | Statement | Backing |
|--------|-----------|---------|
| `card_modEq_card_fixedPoints` | \|α\| ≡ \|fix\| (mod p) | `IsPGroup.card_modEq_card_fixedPoints` |
| `nonempty_fixedPoints_of_not_dvd` | p ∤ \|α\| ⟹ a fixed point exists | `IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card` |
| `center_nontrivial` | nontrivial p-group has nontrivial center | `IsPGroup.center_nontrivial` |
| `bot_lt_center` | ⊥ < Z(G) | `IsPGroup.bot_lt_center` |
| `p_dvd_card_center` | p ∣ \|Z(G)\| | `IsPGroup.nontrivial_iff_card` |

The single congruence `|α| ≡ |fixed points| (mod p)` — itself a consequence of the
orbit–stabilizer theorem and Lagrange — drives the entire structure theory of
`p`-groups: nontriviality of the center (here), nilpotency, the existence of
normal subgroups of every order dividing `|G|`, and, via Sylow's theorems, the
local structure of every finite group.
-/

end LagrangeTheoremOQ02OQ02OQ01OQ02

#check @LagrangeTheoremOQ02OQ02OQ01OQ02.card_modEq_card_fixedPoints
#check @LagrangeTheoremOQ02OQ02OQ01OQ02.center_nontrivial
#check @LagrangeTheoremOQ02OQ02OQ01OQ02.bot_lt_center
#check @LagrangeTheoremOQ02OQ02OQ01OQ02.p_dvd_card_center
