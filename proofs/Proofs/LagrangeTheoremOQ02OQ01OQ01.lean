import Mathlib
import Proofs.LagrangeTheoremOQ02OQ01

/-
# Burnside's Lemma with No Burnside Intermediate (lagrange-theorem-oq-02-oq-01-oq-01)

## Open Question

The parent entry `lagrange-theorem-oq-02-oq-01` derives Burnside's counting lemma from
orbit-stabilizer, but its final step quietly *borrows* Mathlib's own Burnside lemma
(`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) to discharge the global
orbit-partition identity

  Σ_x |Stab(x)| = |X/G| × |G|.

So the parent's `burnside_from_orbit_stabilizer` is not, in fact, self-contained: it routes
through Mathlib's Burnside to close the gap between its *per-orbit* contribution lemma
(`sum_card_stabilizer_orbit`, "each orbit contributes |G|") and the *global* sum over all of `X`.

This entry removes that intermediate. We assemble the per-orbit contributions into the global
stabilizer sum directly, using only the orbit-partition decomposition of `X`
(`MulAction.selfEquivSigmaOrbits`) and the parent's per-orbit lemma — never Mathlib's Burnside.
Burnside's counting lemma then follows from the double-counting bijection of the parent
(`sum_card_fixedBy_eq_sum_card_stabilizer`) with a genuinely independent derivation.

## Proof Chain (self-contained — no Mathlib Burnside)

```
  X ≃ Σ_{ω ∈ X/G} Orb(ω.out)              (selfEquivSigmaOrbits: orbit partition of X)
      ↓  reindex the sum over this partition
  Σ_x |Stab(x)| = Σ_ω Σ_{y ∈ Orb(ω.out)} |Stab(y)|
      ↓  per-orbit contribution (parent's sum_card_stabilizer_orbit, via orbit-stabilizer)
                = Σ_ω |G|
      ↓  constant sum
                = |X/G| × |G|             (global orbit-partition stabilizer sum)
      ↓  double-counting bijection (parent's sum_card_fixedBy_eq_sum_card_stabilizer)
  Σ_g |Fix(g)| = |X/G| × |G|              (Burnside's counting lemma)
```

## Main Results

1. `sum_card_stabilizer_eq_card_orbits_mul_card_group`:
     Σ_x |Stab(x)| = |X/G| × |G|, assembled from the orbit partition and the per-orbit lemma,
     with NO appeal to Mathlib's Burnside. This is the new content.
2. `burnside_no_intermediate`:
     Σ_g |Fix(g)| = |X/G| × |G|, Burnside's counting lemma, derived from (1) and the parent's
     double-counting bijection — a fully self-contained route from orbit-stabilizer.

## Status

Verified: 0 sorries, 0 axioms (target). All theorems machine-checked.
-/

open MulAction Finset BigOperators

namespace LagrangeTheoremOQ02OQ01OQ01

variable {G X : Type*} [Group G] [MulAction G X]

-- ============================================================================
-- The global orbit-partition stabilizer sum (no Burnside intermediate)
-- ============================================================================

/-- **Global orbit-partition stabilizer sum.**

    `Σ_{x ∈ X} |Stab(x)| = |X/G| × |G|`.

    Unlike the parent's `burnside_from_orbit_stabilizer`, which borrows Mathlib's Burnside lemma
    to close this step, here we assemble the identity directly:

    * `MulAction.selfEquivSigmaOrbits G X : X ≃ Σ ω : X/G, Orb(ω.out)` decomposes `X` as the
      disjoint union of its orbits, indexed by the orbit quotient `Ω = X/G`. The underlying point
      is preserved, so reindexing the sum across this equivalence and splitting the resulting
      `Σ`-sum gives `Σ_x |Stab(x)| = Σ_ω Σ_{y ∈ Orb(ω.out)} |Stab(y)|`.
    * Each inner sum equals `|G|` by the parent's `sum_card_stabilizer_orbit` (which is the
      genuine orbit-stabilizer content: every point of an orbit has the same stabilizer size, and
      `|Orb| × |Stab| = |G|`).
    * Summing the constant `|G|` over the `|X/G|` orbits yields `|X/G| × |G|`.

    No step uses `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`. -/
theorem sum_card_stabilizer_eq_card_orbits_mul_card_group
    [Fintype G] [Fintype X] [Fintype (MulAction.orbitRel.Quotient G X)] :
    ∑ x : X, Fintype.card ↥(MulAction.stabilizer G x) =
      Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G := by
  classical
  -- Reindex the sum over the orbit-partition equivalence `X ≃ Σ ω, Orb(ω.out)`.
  -- The underlying point is preserved by the equivalence, so the summand transports by `rfl`.
  rw [Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits G X)
        (fun x => Fintype.card ↥(MulAction.stabilizer G x))
        (fun p => Fintype.card ↥(MulAction.stabilizer G ((p.2 : X))))
        (fun x => rfl)]
  -- Split the Σ-sum into an outer sum over orbits `ω` and an inner sum over `Orb(ω.out)`.
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  -- Each inner orbit sum equals `|G|` by the parent's per-orbit lemma.
  simp_rw [LagrangeTheoremOQ02OQ01.sum_card_stabilizer_orbit]
  -- Sum the constant `|G|` over the `|X/G|` orbits.
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

-- ============================================================================
-- Burnside's counting lemma, self-contained from orbit-stabilizer
-- ============================================================================

/-- **Burnside's counting lemma, with no Burnside intermediate.**

    `Σ_{g ∈ G} |Fix(g)| = |X/G| × |G|`.

    Two genuinely independent steps:

    * Step 1 (double-counting): `Σ_g |Fix(g)| = Σ_x |Stab(x)|`, witnessed by the explicit
      bijection `sigma_fixedBy_equiv_sigma_stabilizer` of the parent
      (`sum_card_fixedBy_eq_sum_card_stabilizer`).
    * Step 2 (orbit partition + orbit-stabilizer): `Σ_x |Stab(x)| = |X/G| × |G|`, proved here in
      `sum_card_stabilizer_eq_card_orbits_mul_card_group` WITHOUT Mathlib's Burnside.

    The result is therefore a fully self-contained derivation of Burnside from orbit-stabilizer,
    closing the gap left open by the parent entry. -/
theorem burnside_no_intermediate
    [Fintype G] [Fintype X]
    [(g : G) → Fintype (MulAction.fixedBy X g)]
    [Fintype (MulAction.orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (MulAction.fixedBy X g) =
      Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G := by
  -- Step 1: double-counting identity Σ_g |Fix(g)| = Σ_x |Stab(x)|.
  rw [LagrangeTheoremOQ02OQ01.sum_card_fixedBy_eq_sum_card_stabilizer]
  -- Step 2: the self-contained global orbit-partition stabilizer sum.
  exact sum_card_stabilizer_eq_card_orbits_mul_card_group

/-- **Burnside's divisibility**, via the self-contained route: `|G| ∣ Σ_g |Fix(g)|`. -/
theorem burnside_divides_no_intermediate
    [Fintype G] [Fintype X]
    [(g : G) → Fintype (MulAction.fixedBy X g)]
    [Fintype (MulAction.orbitRel.Quotient G X)] :
    Fintype.card G ∣ ∑ g : G, Fintype.card (MulAction.fixedBy X g) := by
  rw [burnside_no_intermediate]
  exact dvd_mul_left _ _

end LagrangeTheoremOQ02OQ01OQ01
