import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib.Tactic
import Proofs.SylowTheoremOQ02

/-
# OQ-03: Continuity-enhanced discharge of `sylowProP_projects_pgroup`

This file is `sylow-theorems-oq-03` Candidate A* (S2 ACT): a
continuity-enhanced replacement for the OQ-02 axiom
`ProfiniteSylow.sylowProP_projects_pgroup` (declared at
`SylowTheoremOQ02.lean:134`).

## Mathematical content

The OQ-02 axiom states: under a *continuous surjective* homomorphism
`φ : G →* H` to a finite group `H`, the image of a Sylow pro-p
subgroup `P` of a profinite group `G` is a p-group of `H`. The
axiom's signature lacks the formal `Continuous φ` and
`[DiscreteTopology H]` hypotheses (its docstring mentions "continuous"
but the Lean signature did not record them).

This file proves a strict refinement: under a continuous homomorphism
to a finite discrete group, the image of any Sylow pro-p subgroup is
a p-group. We do not require `IsProfiniteGroup G`, `Fact p.Prime`,
or `Function.Surjective φ` — the cardinality argument only needs the
pro-p structure on `P` and continuity of `φ` to detect an open
kernel.

## Proof outline (Candidate A* per S2 PREP-6, ~50 LOC)

1. Restrict `φ` to `P.toSubgroup` to obtain `φ|P : ↥P.toSubgroup →* H`.
2. Continuity of `φ|P` is inherited from continuity of `φ`.
3. The kernel `(φ|P).ker` is open in `P` because preimages of singletons
   (in discrete `H`) are open.
4. `MonoidHom.normal_ker` provides normality of the kernel as an
   instance.
5. By `IsProP.index_of_open_normal` (OQ-02's `IsProP` typeclass
   field), `(φ|P).ker.index = p ^ k` for some `k`.
6. `Subgroup.index_ker` collapses `Nat.card range` and `ker.index`
   in one line: `f.ker.index = Nat.card f.range`.
7. `P.toSubgroup.map φ = (φ|P).range` (image-as-subgroup vs restricted
   range), so `Nat.card (P.toSubgroup.map φ) = p ^ k`.
8. `IsPGroup.of_card` closes from a cardinality-is-power-of-p witness.

The 1-LOC `Subgroup.index_ker` bridge (PREP-6 Finding I) replaces an
earlier 3-lemma chain.

## Effect on `SylowTheoremOQ02.lean`

In S4 ACT (this file's companion edit), the original axiom
`sylowProP_projects_pgroup` was deleted from `SylowTheoremOQ02.lean`
along with its `#check` line in the sanity-check block. Net OQ-02
axiom count: 5 → 4. No callers anywhere in `proofs/Proofs/` referenced
the axiom by name beyond the `#check`, so removal is purely additive
to the gallery's axiom-integrity ledger; the continuity-enhanced
theorem `ProfiniteSylow.sylowProP_projects_pgroup_continuous` below
is the new bearer of the projection result.

## References

- `Mathlib/GroupTheory/Index.lean:322` — `Subgroup.index_ker`
  (`f.ker.index = Nat.card f.range`).
- `Mathlib/GroupTheory/PGroup.lean:40` — `IsPGroup.of_card`
  (`Nat.card G = p ^ n → IsPGroup p G`).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:314` — `MonoidHom.normal_ker`
  (instance: `(f : G →* M) : f.ker.Normal`).
- `Mathlib/Topology/Order.lean:255` — `isOpen_discrete`
  (`@[simp]` lemma: in a discrete topology, every set is open).
-/

namespace ProfiniteSylow

set_option linter.unusedVariables false

section SylowProjectionsToFinite

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {p : ℕ} (P : SylowProP G p)
variable {H : Type*} [Group H] [Fintype H]
variable [TopologicalSpace H] [DiscreteTopology H]
variable (φ : G →* H)

/-- The restriction of a homomorphism `φ : G →* H` to a Sylow pro-p
subgroup `P` of `G`. -/
def restrictToSylowProP : P.toSubgroup →* H :=
  φ.comp P.toSubgroup.subtype

/-- The restriction of a continuous homomorphism is continuous. -/
theorem continuous_restrictToSylowProP (hφ_cont : Continuous φ) :
    Continuous (restrictToSylowProP P φ) :=
  hφ_cont.comp continuous_subtype_val

/-- The kernel of the restriction is open in `P` (because the codomain
is finite discrete and the restriction is continuous). -/
theorem isOpen_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    IsOpen (((restrictToSylowProP P φ).ker : Subgroup P.toSubgroup) :
      Set P.toSubgroup) := by
  have hker_eq :
      (((restrictToSylowProP P φ).ker : Subgroup P.toSubgroup) :
        Set P.toSubgroup)
        = (restrictToSylowProP P φ) ⁻¹' ({(1 : H)} : Set H) := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hker_eq]
  exact (isOpen_discrete _).preimage
    (continuous_restrictToSylowProP P φ hφ_cont)

/-- The kernel of the restriction has p-power index in `P`
(because `P` is pro-p and the kernel is open and normal). -/
theorem exists_pow_index_ker_restrictToSylowProP (hφ_cont : Continuous φ) :
    ∃ k : ℕ, (restrictToSylowProP P φ).ker.index = p ^ k :=
  P.isProP.index_of_open_normal
    (restrictToSylowProP P φ).ker
    (MonoidHom.normal_ker _)
    (isOpen_ker_restrictToSylowProP P φ hφ_cont)

/-- **Continuity-enhanced replacement for axiom
`ProfiniteSylow.sylowProP_projects_pgroup`**: the image of a Sylow
pro-p subgroup under a *continuous* homomorphism to a finite discrete
group is a p-group.

Compared to the OQ-02 axiom (declared at `SylowTheoremOQ02.lean:134`),
this theorem:

* Adds the (mathematically required) hypotheses `Continuous φ` and
  `[DiscreteTopology H]`.
* Drops the unused `IsProfiniteGroup G`, `Fact p.Prime`, and
  `Function.Surjective φ` hypotheses.
-/
theorem sylowProP_projects_pgroup_continuous (hφ_cont : Continuous φ) :
    IsPGroup p (P.toSubgroup.map φ) := by
  -- The image-as-subgroup equals the range of the restriction.
  have himg_eq_range :
      P.toSubgroup.map φ = (restrictToSylowProP P φ).range := by
    ext x
    simp [Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP,
          MonoidHom.comp_apply, Subgroup.coe_subtype]
  -- `Subgroup.index_ker`: |range f| = (ker f).index.
  have hcard_range :
      Nat.card (restrictToSylowProP P φ).range
        = (restrictToSylowProP P φ).ker.index :=
    (Subgroup.index_ker (restrictToSylowProP P φ)).symm
  obtain ⟨k, hk⟩ :=
    exists_pow_index_ker_restrictToSylowProP P φ hφ_cont
  have hcard_img : Nat.card (P.toSubgroup.map φ) = p ^ k := by
    rw [himg_eq_range, hcard_range, hk]
  exact IsPGroup.of_card hcard_img

end SylowProjectionsToFinite

end ProfiniteSylow

#check @ProfiniteSylow.restrictToSylowProP
#check @ProfiniteSylow.continuous_restrictToSylowProP
#check @ProfiniteSylow.isOpen_ker_restrictToSylowProP
#check @ProfiniteSylow.exists_pow_index_ker_restrictToSylowProP
#check @ProfiniteSylow.sylowProP_projects_pgroup_continuous
