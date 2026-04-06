/-
# Interfacing Burnside's Lemma with Mathlib MulAction Framework
## (burnside-counting-oq-03-oq-03)

**Open Question** (from burnside-counting-oq-03): Can the cyclic rotation AddAction
be formally connected to Mathlib's `MulAction` framework to derive the Burnside
orbit-counting theorem for necklaces?

**Answer**: YES. The key is the canonical `Multiplicative` type alias:
  `AddAction (ZMod n) X` ⟺ `MulAction (Multiplicative (ZMod n)) X`
via `(Multiplicative.ofAdd r) • c = r +ᵥ c` (definitional equality).

**Connection chain**:
1. `cyclicAddActionOnColorings : AddAction (ZMod n) (Coloring n k)` [in BurnsideCounting.lean]
2. Mathlib auto-derives `MulAction (Multiplicative (ZMod n)) (Coloring n k)`
3. `fixedBy (Coloring n k) (Multiplicative.ofAdd r) = {c | IsFixedByRotation r c}`
4. `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` gives Burnside identity
5. `Fintype.card (Multiplicative (ZMod n)) = n` closes the sum

**Axiom note**: Inherits `rotatedIndex_add` axiom from BurnsideCounting.lean.

**Sorry count**: 0.
-/

import Mathlib
import Proofs.BurnsideCounting

open BurnsideCounting MulAction Finset

namespace BurnsideCountingOQ03OQ03

variable {n k : ℕ} [NeZero n]

/-! ## Section I: MulAction from AddAction (automatic via Multiplicative) -/

/-- Mathlib derives `MulAction (Multiplicative (ZMod n)) (Coloring n k)` from the
    `AddAction` instance via the `Multiplicative` functor. -/
example : MulAction (Multiplicative (ZMod n)) (Coloring n k) := inferInstance

/-! ## Section II: Fixed-Point Identification -/

/-- The fixed points of `Multiplicative.ofAdd r` are exactly the colorings fixed by `r +ᵥ ·`.
    Key: `(Multiplicative.ofAdd r) • c = r +ᵥ c` by the SMul instance definition,
    and `IsFixedByRotation r c` is `r +ᵥ c = c`. -/
lemma mem_fixedBy_iff (r : ZMod n) (c : Coloring n k) :
    c ∈ MulAction.fixedBy (Coloring n k) (Multiplicative.ofAdd r) ↔
    IsFixedByRotation r c := by
  simp only [MulAction.mem_fixedBy, IsFixedByRotation]

/-- Cardinality of `fixedBy (Multiplicative.ofAdd r)` equals cardinality of
    `{c | IsFixedByRotation r c}`. -/
lemma card_fixedBy_eq (r : ZMod n) :
    Fintype.card (MulAction.fixedBy (Coloring n k) (Multiplicative.ofAdd r)) =
    Fintype.card { c : Coloring n k // IsFixedByRotation r c } := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (fun c => mem_fixedBy_iff r c)

/-! ## Section III: Orbit Decidability -/

/-- The orbit equivalence relation is decidable for cyclic necklaces.
    `c₁ ~orbit c₂` iff `∃ g : Multiplicative (ZMod n), g • c₁ = c₂`,
    decidable since the group is finite and equality of colorings is decidable. -/
private instance orbitDecidable :
    DecidableRel (MulAction.orbitRel (Multiplicative (ZMod n)) (Coloring n k)).r := by
  intro c₁ c₂
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact Fintype.decidableExistsFintype

/-- The orbit quotient is Fintype (finite colorings + decidable orbit relation). -/
private instance orbitFintype :
    Fintype (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (Coloring n k)) :=
  Quotient.fintype (MulAction.orbitRel (Multiplicative (ZMod n)) (Coloring n k))

/-! ## Section IV: Burnside's Theorem -/

/-- **Main Theorem**: Burnside's orbit-counting for cyclic necklaces via Mathlib.

The sum of fixed-point counts (over all rotations) equals the number of
distinct necklaces (orbits) times n.

Direct application of `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
with `Fintype.card (Multiplicative (ZMod n)) = n`. -/
theorem burnside_necklace_count :
    ∑ g : Multiplicative (ZMod n),
      Fintype.card (MulAction.fixedBy (Coloring n k) g) =
    Fintype.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (Coloring n k)) * n := by
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (ZMod n)) (Coloring n k)
  have hcard : Fintype.card (Multiplicative (ZMod n)) = n := by
    simp [ZMod.card]
  rw [hcard] at h
  exact h

/-- Restate Burnside with sum over `ZMod n` (rather than `Multiplicative (ZMod n)`)
    and in terms of `IsFixedByRotation` subtypes. -/
theorem burnside_necklace_count_zmod :
    ∑ r : ZMod n,
      Fintype.card { c : Coloring n k // IsFixedByRotation r c } =
    Fintype.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (Coloring n k)) * n := by
  -- Rewrite each term via card_fixedBy_eq, then close with burnside_necklace_count.
  -- Note: Multiplicative (ZMod n) = ZMod n by def, so 'exact' unifies the sum domains.
  refine (Finset.sum_congr rfl fun r _ => (card_fixedBy_eq r).symm).trans ?_
  exact burnside_necklace_count

/-! ## Section V: Consequences -/

/-- **Necklace Count**: The Burnside identity implies
    n × necklace_count = Σ_{r} |{colorings fixed by rotation r}| -/
theorem necklace_count_burnside (necklace_count : ℕ)
    (h_orbits : Fintype.card
      (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (Coloring n k)) = necklace_count) :
    n * necklace_count =
    ∑ r : ZMod n, Fintype.card { c : Coloring n k // IsFixedByRotation r c } := by
  rw [mul_comm, ← h_orbits]
  exact burnside_necklace_count_zmod.symm

/-- The Mathlib orbit relation coincides with `ColoringEquiv`.
    Two colorings are in the same orbit iff one is a cyclic rotation of the other. -/
theorem orbitRel_iff_coloringEquiv (c₁ c₂ : Coloring n k) :
    MulAction.orbitRel (Multiplicative (ZMod n)) (Coloring n k) c₁ c₂ ↔
    ColoringEquiv c₁ c₂ := by
  -- Key: orbitRel G X c₁ c₂ means c₁ ∈ orbit G c₂ (i.e., ∃ g, g • c₂ = c₁),
  -- while ColoringEquiv c₁ c₂ means ∃ r, r +ᵥ c₁ = c₂.
  -- Both directions require group inverse: from g • c₂ = c₁, use (-toAdd g) +ᵥ c₁ = c₂.
  constructor
  · intro h
    -- h : orbitRel c₁ c₂, i.e., c₁ ∈ orbit G c₂ = ∃ g, g • c₂ = c₁
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨g, hg⟩ := h
    -- hg : g • c₂ = c₁, i.e., toAdd g +ᵥ c₂ = c₁
    -- Use r = -(toAdd g): then -(toAdd g) +ᵥ c₁ = c₂
    refine ⟨-(Multiplicative.toAdd g), ?_⟩
    have h₁ : Multiplicative.toAdd g +ᵥ c₂ = c₁ := hg
    rw [← h₁, ← add_vadd, neg_add_cancel, zero_vadd (M := ZMod n)]
  · intro ⟨r, hr⟩
    -- hr : r +ᵥ c₁ = c₂; need orbitRel c₁ c₂ = c₁ ∈ orbit G c₂ = ∃ g, g • c₂ = c₁
    -- Use g = ofAdd (-r): (-r) +ᵥ c₂ = c₁
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨Multiplicative.ofAdd (-r), ?_⟩
    show (-r) +ᵥ c₂ = c₁
    rw [← hr, ← add_vadd, neg_add_cancel, zero_vadd (M := ZMod n)]

#check @MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
#check burnside_necklace_count
#check burnside_necklace_count_zmod
#check necklace_count_burnside
#check orbitRel_iff_coloringEquiv

end BurnsideCountingOQ03OQ03
