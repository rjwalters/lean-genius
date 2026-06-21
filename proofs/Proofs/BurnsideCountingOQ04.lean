import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-
# Burnside Counting, OQ-04: Extending to the Dihedral Group via Index-2 Folding

## What This Proves

The parent entry `burnside-counting` counts binary necklaces of length `n`: orbits of
colorings under the **cyclic** rotation group `ℤ/nℤ`.  This file answers the open question
"extend to the dihedral group `D_n`" by isolating the exact mechanism that relates
**bracelet** counting (dihedral orbits, rotations *and* reflections) to **necklace**
counting (cyclic orbits, rotations only).

The dihedral group `D_n` contains the cyclic rotation group as a subgroup of **index 2**:
`|D_n| = 2n = 2·|ℤ/nℤ|`.  Everything about "adding reflections to Burnside" is captured by
the following abstract statement, proved here with no extra axioms:

  **Index-2 orbit folding.**  If a finite group `G` acts on a finite set `X` and `H ≤ G`,
  then
    `|X/G|·|G| = |X/H|·|H| + Σ_{g ∉ H} |Fix(g)|`.

  Applied with `G = D_n`, `H = ℤ/nℤ`, this reads
    `(bracelets)·2n = (necklaces)·n + Σ_{reflections} |Fix|`,
  i.e. the classical "bracelets = (necklaces + reflection fixed points)/2".

We then specialise: when `|G| = 2|H|` (the dihedral case) we obtain the doubling form
  `2·|X/G|·|H| = |X/H|·|H| + Σ_{g ∉ H} |Fix(g)|`,
and we plug in the classical data for binary length-4 colourings
(`|necklaces| = 6`, `|H| = 4`, reflection fixed points `= 24`) to recover
`|bracelets| = 6`.

## Honesty / Scope

The headline theorem `index_two_orbit_folding` is the genuine contribution: it is a clean,
fully general, axiom-free derivation that holds for *any* subgroup, with the dihedral
extension as its motivating instance.  The numeric corollary
`binary_four_bracelet_count` takes the classical reflection-fixed-point total (24) and
necklace count (6) for length-4 binary colourings as hypotheses and *derives* the bracelet
count from the folding theorem; it does not recompute those two finite counts inside Lean
(that would require rebuilding the parent's concrete orbit-quotient `Fintype`, which the
parent itself only closes with `native_decide`).  So this is an exact algebraic reduction,
not a from-scratch enumeration.

## Mathlib Dependencies
- `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` : Burnside's lemma
- `Mathlib.GroupTheory.SpecificGroups.Dihedral` : `DihedralGroup n`, `DihedralGroup.card`
-/

namespace BurnsideCountingOQ04

open Finset MulAction

/-! ## Part I: The index-2 orbit-folding theorem -/

/-- **Index-2 orbit folding (Burnside, split by a subgroup).**

For a finite group `G` acting on a finite set `X` and any subgroup `H ≤ G`,
the Burnside count over `G` decomposes as the Burnside count over `H` plus the
contribution of the elements outside `H`:

  `|X/G|·|G| = |X/H|·|H| + Σ_{g ∉ H} |Fix(g)|`.

With `G = D_n` and `H` the rotation subgroup `ℤ/nℤ`, the second summand ranges over the
reflections, so this is precisely the bracelets-from-necklaces formula. -/
theorem index_two_orbit_folding
    {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    [∀ g : G, Fintype (fixedBy X g)] [∀ h : H, Fintype (fixedBy X h)]
    [Fintype (orbitRel.Quotient G X)] [Fintype (orbitRel.Quotient H X)] :
    Fintype.card (orbitRel.Quotient G X) * Fintype.card G
      = Fintype.card (orbitRel.Quotient H X) * Fintype.card H
        + ∑ g ∈ Finset.univ.filter (fun g => ¬ (g ∈ H)),
            Fintype.card (fixedBy X g) := by
  -- Burnside's lemma applied to the full group `G`.
  have hG : ∑ g : G, Fintype.card (fixedBy X g)
      = Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  -- The restricted action of `H` fixes a coloring iff the underlying element of `G` does:
  -- `fixedBy X (h : G)` and `fixedBy X h` are definitionally the same set, so their
  -- cardinalities agree (only the `Fintype` instances differ).
  have hcard : ∀ h : H, Fintype.card (fixedBy X (h : G)) = Fintype.card (fixedBy X h) :=
    fun h => Fintype.card_congr (Equiv.refl _)
  -- Burnside's lemma applied to the subgroup `H`.
  have hH : ∑ h : H, Fintype.card (fixedBy X (h : G))
      = Fintype.card (orbitRel.Quotient H X) * Fintype.card H := by
    rw [Finset.sum_congr rfl (fun h _ => hcard h)]
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H X
  -- Split the Burnside sum over `G` into the `H`-part and the complement.
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset G)
    (fun g => g ∈ H) (fun g => Fintype.card (fixedBy X g))
  -- The `H`-part of the sum equals the Burnside sum over the subgroup `H`.
  have hrot : ∑ g ∈ Finset.univ.filter (fun g => g ∈ H), Fintype.card (fixedBy X g)
      = ∑ h : H, Fintype.card (fixedBy X (h : G)) :=
    Finset.sum_subtype (Finset.univ.filter (fun g => g ∈ H)) (fun x => by simp)
      (fun g => Fintype.card (fixedBy X g))
  rw [← hG, ← hsplit, hrot, hH]

/-! ## Part II: The dihedral (index-2) specialisation -/

/-- **Dihedral doubling form.**  When `|G| = 2·|H|` — the defining size relation of the
dihedral group over its rotation subgroup — folding rearranges to

  `2·|X/G|·|H| = |X/H|·|H| + Σ_{g ∉ H} |Fix(g)|`,

i.e. `bracelets·2|H| = necklaces·|H| + (reflection fixed points)`. -/
theorem dihedral_doubling
    {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    [∀ g : G, Fintype (fixedBy X g)] [∀ h : H, Fintype (fixedBy X h)]
    [Fintype (orbitRel.Quotient G X)] [Fintype (orbitRel.Quotient H X)]
    (hindex : Fintype.card G = 2 * Fintype.card H) :
    2 * Fintype.card (orbitRel.Quotient G X) * Fintype.card H
      = Fintype.card (orbitRel.Quotient H X) * Fintype.card H
        + ∑ g ∈ Finset.univ.filter (fun g => ¬ (g ∈ H)),
            Fintype.card (fixedBy X g) := by
  have h := index_two_orbit_folding (G := G) (X := X) H
  rw [hindex] at h
  rw [← h]; ring

/-- `DihedralGroup n` has order `2n`: the size relation that makes the rotation subgroup
have index 2.  (Re-export of `DihedralGroup.card` for context.) -/
theorem dihedralGroup_card (n : ℕ) [NeZero n] :
    Fintype.card (DihedralGroup n) = 2 * n :=
  DihedralGroup.card

/-! ## Part III: Numeric instance — binary length-4 bracelets

We plug the classical length-4 binary data into the folding theorem.

The parent entry establishes the necklace (cyclic-orbit) count `|X/H| = 6` with `|H| = 4`.
For the dihedral group `D_4` (order 8) the four reflections of the square fix, respectively,
`8, 8, 4, 4` colourings (two axes through opposite vertices, two through opposite edge
midpoints), for a reflection total of `24`.  Folding then forces the bracelet count to be 6:

  `bracelets·8 = necklaces·4 + 24 = 24 + 24 = 48`,  so  `bracelets = 6`.

These two inputs (`necklaces = 6`, reflection total `= 24`) are taken as hypotheses; the
theorem derives the bracelet count purely from `index_two_orbit_folding`. -/
theorem binary_four_bracelet_count
    {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]
    (H : Subgroup G) [DecidablePred (· ∈ H)]
    [∀ g : G, Fintype (fixedBy X g)] [∀ h : H, Fintype (fixedBy X h)]
    [Fintype (orbitRel.Quotient G X)] [Fintype (orbitRel.Quotient H X)]
    (hG : Fintype.card G = 8) (hH : Fintype.card H = 4)
    (hnecklaces : Fintype.card (orbitRel.Quotient H X) = 6)
    (hreflections :
      (∑ g ∈ Finset.univ.filter (fun g => ¬ (g ∈ H)), Fintype.card (fixedBy X g)) = 24) :
    Fintype.card (orbitRel.Quotient G X) = 6 := by
  have h := index_two_orbit_folding (G := G) (X := X) H
  rw [hG, hH, hnecklaces, hreflections] at h
  -- `|X/G| * 8 = 6 * 4 + 24 = 48`
  omega

end BurnsideCountingOQ04
