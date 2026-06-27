/-
  The Fundamental Theorem of Galois Theory — the subfield ↔ subgroup dictionary
  (Open Question OQ-02 of abel-ruffini-galois-extensions:
   "Prove the Galois Correspondence Theorem (Subfields ↔ Subgroups)").

  ## What this file establishes (0 sorry, 0 axiom)

  For a finite Galois extension `E / F`, the **Galois correspondence** is an
  order-reversing bijection between the lattice of intermediate fields `F ⊆ K ⊆ E`
  and the lattice of subgroups of the Galois group `Gal(E/F) = E ≃ₐ[F] E`, sending an
  intermediate field `K` to its fixing subgroup `{σ | σ|_K = id}` and a subgroup `H` to
  its fixed field `{x | ∀ σ ∈ H, σ x = x}`.

  Mathlib already contains the core theorem (`IsGalois.intermediateFieldEquivSubgroup`,
  the two round-trip identities, and the normal-subgroup ↔ Galois-subextension
  refinement). This file does **not** re-prove that machinery; it **packages** it into a
  single, self-contained "dictionary" entry for the gallery and derives the consequences
  that make the correspondence usable, several of which are not single Mathlib lemmas:

    * `galoisCorrespondence` — the headline order anti-isomorphism
      `IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ`.
    * `fixedField_fixingSubgroup`, `fixingSubgroup_fixedField` — the two round trips
      (`H ↦ fixedField H ↦ fixingSubgroup` and the reverse are the identity).
    * `le_iff_fixingSubgroup_le` — the correspondence is **order-reversing**:
      `K ≤ L ↔ L.fixingSubgroup ≤ K.fixingSubgroup`.
    * `fixingSubgroup_bot/top`, `fixedField_bot/top` — the endpoints: the base field `⊥`
      corresponds to the whole group `⊤` and the top field `⊤` to the trivial group `⊥`.
    * `intermediateFieldEquivSubgroup'` / `card_intermediateField_eq_card_subgroup` —
      forgetting the order, intermediate fields are in plain bijection with subgroups, so
      a finite Galois extension has exactly as many intermediate fields as the Galois
      group has subgroups.
    * `card_fixingSubgroup_eq_finrank` — the **degree dictionary**, upper half:
      `[E : K] = |Gal(E/K)| = |K.fixingSubgroup|`.
    * `finrank_eq_index_fixingSubgroup` — the degree dictionary, lower half:
      `[K : F] = [Gal(E/F) : K.fixingSubgroup]` (the index of the corresponding subgroup).
      This one is assembled from `Module.finrank_mul_finrank`, `card_aut_eq_finrank`,
      and `Subgroup.index_mul_card`, not read off a single Mathlib declaration.
    * `isGalois_fixedField_of_normal`, `normalQuotientEquiv` — the **normal refinement**:
      a normal subgroup `H` corresponds to a Galois subextension, and then
      `Gal(fixedField H / F) ≃* Gal(E/F) ⧸ H`.

  ## Concrete instantiation (links to OQ-01)

  The final section applies the dictionary to the Abel–Ruffini witness
  `q = X⁵ − 4X + 2` from `AbelRuffiniGaloisExtensionsOQ01.lean`. Its splitting field is a
  finite Galois extension of `ℚ` whose Galois group is `S₅` (OQ-01's `galEquivS5`), so the
  intermediate fields of that splitting field are in bijection with the subgroups of `S₅`
  (`quintic_card_intermediateField_eq_card_subgroup`). This connects the abstract
  correspondence to the concrete quintic whose unsolvability OQ-01 established.

  ## Provenance

  The Galois correspondence and its normal refinement are Mathlib's
  `Mathlib/FieldTheory/Galois/Basic.lean`. The new content here is the consolidated
  packaging, the order-reversal and degree/index corollaries, and the concrete link to
  the OQ-01 quintic witness.

  ## References
  - Mathlib, `Mathlib/FieldTheory/Galois/Basic.lean`
    (`IsGalois.intermediateFieldEquivSubgroup`, `fixedField_fixingSubgroup`,
    `fixingSubgroup_fixedField`, `normalAutEquivQuotient`).
  - Stacks project, tag 09DW (Fundamental theorem of Galois theory).
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Proofs.AbelRuffiniGaloisExtensionsOQ01

namespace AbelRuffiniGaloisExtensionsOQ02

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-! ## Part I — the correspondence and its round trips -/

/-- **The Fundamental Theorem of Galois Theory.** For a finite Galois extension `E / F`,
the map `K ↦ K.fixingSubgroup` is an order-*reversing* bijection from intermediate fields
to subgroups of the Galois group, with inverse `H ↦ fixedField H`. Packaged as an order
isomorphism onto the order dual of the subgroup lattice. -/
noncomputable def galoisCorrespondence :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ :=
  IsGalois.intermediateFieldEquivSubgroup

/-- Round trip starting from an intermediate field: fixing then fixing-back recovers `K`. -/
theorem fixedField_fixingSubgroup (K : IntermediateField F E) :
    fixedField K.fixingSubgroup = K :=
  IsGalois.fixedField_fixingSubgroup K

/-- Round trip starting from a subgroup: taking the fixed field then the fixing subgroup
recovers `H`. -/
theorem fixingSubgroup_fixedField (H : Subgroup (E ≃ₐ[F] E)) :
    (fixedField H).fixingSubgroup = H :=
  IntermediateField.fixingSubgroup_fixedField H

/-! ## Part II — the correspondence is order-reversing -/

/-- The Galois correspondence is **inclusion-reversing**: a larger intermediate field
fixes fewer automorphisms, i.e. `K ≤ L ↔ L.fixingSubgroup ≤ K.fixingSubgroup`. -/
theorem le_iff_fixingSubgroup_le {K L : IntermediateField F E} :
    K ≤ L ↔ L.fixingSubgroup ≤ K.fixingSubgroup := by
  refine ⟨fixingSubgroup_le, fun h => ?_⟩
  have h2 := fixedField_le h
  rwa [IsGalois.fixedField_fixingSubgroup, IsGalois.fixedField_fixingSubgroup] at h2

/-! ## Part III — the endpoints of the correspondence -/

/-- The base field `F` (the bottom intermediate field) is fixed by **every** automorphism:
`⊥.fixingSubgroup = ⊤`. -/
@[simp] theorem fixingSubgroup_bot : (⊥ : IntermediateField F E).fixingSubgroup = ⊤ :=
  IntermediateField.fixingSubgroup_bot

/-- The whole field `E` (the top intermediate field) is fixed **only** by the identity:
`⊤.fixingSubgroup = ⊥`. -/
@[simp] theorem fixingSubgroup_top : (⊤ : IntermediateField F E).fixingSubgroup = ⊥ :=
  IntermediateField.fixingSubgroup_top

/-- The trivial subgroup fixes everything: `fixedField ⊥ = ⊤` (the whole field). -/
theorem fixedField_bot : fixedField (⊥ : Subgroup (E ≃ₐ[F] E)) = ⊤ := by
  rw [← IntermediateField.fixingSubgroup_top, IsGalois.fixedField_fixingSubgroup]

/-- The whole group fixes only the base field: `fixedField ⊤ = ⊥`. -/
theorem fixedField_top : fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥ :=
  IsGalois.fixedField_top

/-! ## Part IV — counting: intermediate fields ↔ subgroups -/

/-- The Galois correspondence as a plain bijection (forgetting the order), obtained from
`galoisCorrespondence` by discarding the order-dual wrapper. -/
noncomputable def intermediateFieldEquivSubgroup' :
    IntermediateField F E ≃ Subgroup (E ≃ₐ[F] E) :=
  IsGalois.intermediateFieldEquivSubgroup.toEquiv.trans OrderDual.ofDual

/-- A finite Galois extension has exactly as many intermediate fields as its Galois group
has subgroups. -/
theorem card_intermediateField_eq_card_subgroup :
    Nat.card (IntermediateField F E) = Nat.card (Subgroup (E ≃ₐ[F] E)) :=
  Nat.card_congr intermediateFieldEquivSubgroup'

/-! ## Part V — the degree/index dictionary -/

/-- **Degree dictionary, upper half.** The degree `[E : K]` of the top of the tower over
an intermediate field equals the order of the corresponding subgroup `K.fixingSubgroup`
(which is `Gal(E/K)`). -/
theorem card_fixingSubgroup_eq_finrank (K : IntermediateField F E) :
    Nat.card K.fixingSubgroup = Module.finrank K E :=
  IsGalois.card_fixingSubgroup_eq_finrank K

/-- **Degree dictionary, lower half.** The degree `[K : F]` of the bottom of the tower
equals the *index* of the corresponding subgroup in the Galois group. Assembled from the
tower law `[E:F] = [K:F]·[E:K]`, the Galois count `|Gal(E/F)| = [E:F]`, the upper-half
dictionary `|K.fixingSubgroup| = [E:K]`, and `index · order = group order`. -/
theorem finrank_eq_index_fixingSubgroup (K : IntermediateField F E) :
    Module.finrank F K = K.fixingSubgroup.index := by
  have hpos : 0 < Module.finrank K E := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [Module.finrank_mul_finrank F K E, ← IsGalois.card_aut_eq_finrank F E,
    ← Subgroup.index_mul_card K.fixingSubgroup, IsGalois.card_fixingSubgroup_eq_finrank]

/-! ## Part VI — the normal refinement -/

/-- A **normal** subgroup corresponds to a **Galois** subextension: `fixedField H` is
Galois over the base field `F`. -/
theorem isGalois_fixedField_of_normal (H : Subgroup (E ≃ₐ[F] E)) [H.Normal] :
    IsGalois F (fixedField H) :=
  inferInstance

/-- For a normal subgroup `H`, the Galois group of the corresponding subextension is the
quotient of the full Galois group by `H`: `Gal(fixedField H / F) ≃* Gal(E/F) ⧸ H`. -/
noncomputable def normalQuotientEquiv (H : Subgroup (E ≃ₐ[F] E)) [H.Normal] :
    ((E ≃ₐ[F] E) ⧸ H) ≃* (fixedField H ≃ₐ[F] fixedField H) :=
  IsGalois.normalAutEquivQuotient H

/-! ## Part VII — concrete instantiation: the Abel–Ruffini quintic `X⁵ − 4X + 2`

We apply the dictionary to the witness `q = X⁵ − 4X + 2` from OQ-01. Its splitting field
is a finite Galois extension of `ℚ` (separable since irreducible in characteristic zero),
and OQ-01 identifies its Galois group with `S₅`. -/

section Quintic

open AbelRuffiniGaloisExtensionsOQ01

/-- The splitting field of `X⁵ − 4X + 2` is Galois over `ℚ` (the polynomial is separable,
being irreducible over a field of characteristic zero). -/
noncomputable instance : IsGalois ℚ q.SplittingField :=
  IsGalois.of_separable_splitting_field q_separable

/-- **The Galois correspondence for the Abel–Ruffini witness.** The intermediate fields of
the splitting field of `X⁵ − 4X + 2` are in bijection with the subgroups of its Galois
group — which, by `AbelRuffiniGaloisExtensionsOQ01.galEquivS5`, is the symmetric group
`S₅`. So the lattice of subfields of this concrete quintic's splitting field mirrors the
subgroup lattice of `S₅`. -/
theorem quintic_card_intermediateField_eq_card_subgroup :
    Nat.card (IntermediateField ℚ q.SplittingField)
      = Nat.card (Subgroup (q.SplittingField ≃ₐ[ℚ] q.SplittingField)) :=
  card_intermediateField_eq_card_subgroup

end Quintic

end AbelRuffiniGaloisExtensionsOQ02
