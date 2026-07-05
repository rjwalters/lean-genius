/-
  Zassenhaus Butterfly Lemma for Subgroups (OQ-04-OQ-03)

  Formalizes the **Zassenhaus butterfly lemma** (Schmetterlingslemma, 1934),
  the combinatorial engine behind Schreier's refinement theorem and hence behind
  the Jordan-Hölder theorem. This is the open follow-up to OQ-04, which noted:

    "The Zassenhaus butterfly lemma is not yet in Mathlib and would be needed for
     a self-contained proof [of Schreier refinement] independent of Jordan-Hölder."

  ## The Lemma

  Let `A ⊴ A'` and `B ⊴ B'` be subgroups of a group `G` (each normal in the next).
  Writing `H·K` for the pointwise product of subgroups, the butterfly lemma states
  that the two "tower" quotients are isomorphic through a common middle quotient:

      A·(A'∩B')            B·(B'∩A')                    A'∩B'
      ─────────    ≅≅≅     ─────────      ≅≅≅      ─────────────────
      A·(A'∩B)             B·(B'∩A)                 (A∩B')·(A'∩B)

  In lattice/Mathlib notation with `⊔` (= pointwise product here, since one factor
  is normal) and `⊓`:

      U_A := A ⊔ (A' ⊓ B'),   L_A := A ⊔ (A' ⊓ B)      (left tower)
      U_B := B ⊔ (B' ⊓ A'),   L_B := B ⊔ (B' ⊓ A)      (right tower)
      I   := A' ⊓ B',         M   := (A ⊓ B') ⊔ (A' ⊓ B)  (common middle)

  and the claim is `U_A ⧸ L_A ≃* U_B ⧸ L_B`, both being `≃* I ⧸ M`.

  ## Proof Strategy (roadmap for the remaining `sorry`)

  The whole content is the single "half" isomorphism `U_A ⧸ L_A ≃* I ⧸ M`; the
  full butterfly then follows by applying it a second time with `A,A'` and `B,B'`
  swapped and composing (this assembly is fully proved below, `zassenhaus_butterfly`).

  The half isomorphism is the second isomorphism theorem chained with the third:

  * The Dedekind modular law is now in Mathlib as `Subgroup.mul_inf_assoc` /
    `Subgroup.inf_mul_assoc`:  `A ≤ C → ↑A * ↑(B ⊓ C) = ↑A * ↑B ∩ ↑C`.
    Applying `inf_mul_assoc` (with `A' ⊓ B ≤ A' ⊓ B'`) computes the kernel:
        (A' ⊓ B') ⊓ (A ⊔ (A' ⊓ B)) = (A ⊓ B') ⊔ (A' ⊓ B) = M.
  * Build `φ : (A' ⊓ B') →* U_A ⧸ (L_A.subgroupOf U_A)` as `mk' ∘ inclusion`,
    exactly as in OQ-04's `second_iso`. Surjectivity uses that `A ⊴ A'` makes
    `A ⊔ (A' ⊓ B') = A · (A' ⊓ B')` (mem_sup) and `A ⊆ L_A`; the kernel is `M`
    by the Dedekind computation above. Then
    `QuotientGroup.quotientKerEquivOfSurjective` gives `I ⧸ M ≃* U_A ⧸ L_A`.

  The two normality facts `L_A ⊴ U_A` and `M ⊴ I` are recorded as lemmas; `M ⊴ I`
  is fully proved (join of two relatively-normal subgroups), while `L_A ⊴ U_A`
  is deferred with the same second-iso route.

  ## Proof Status

  - `zassenhaus_butterfly`   — PROVED from `zassenhaus_half` (symmetry assembly).
  - `middle_le_inter`, tower containments, `middle_symm`, `inter_symm`,
    `middle_normal` — PROVED.
  - `zassenhaus_half`        — sorry (core second/third-iso; Aristotle target).

  Reuses `GroupQuotIso` from OQ-04 as the normality-carrying "iso" predicate.
-/

import Mathlib.Tactic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Proofs.AbelRuffiniGaloisExtensionsOQ04

namespace AbelRuffiniGaloisExtensionsOQ04OQ03

open Subgroup QuotientGroup
open AbelRuffiniGaloisExtensionsOQ04 (GroupQuotIso)

variable {G : Type*} [Group G]

-- ============================================================
-- PART I: GroupQuotIso is a symmetric, transitive relation
-- (re-proved locally so the butterfly assembly is self-contained)
-- ============================================================

/-- `GroupQuotIso` is symmetric: `U/L ≃* I/M` gives `I/M ≃* U/L`. -/
lemma giso_symm {X Y : Subgroup G × Subgroup G} :
    GroupQuotIso X Y → GroupQuotIso Y X := by
  rintro ⟨hn1, hn2, f⟩
  refine ⟨hn2, hn1, ?_⟩
  haveI := hn1; haveI := hn2
  exact f.map (·.symm)

/-- `GroupQuotIso` is transitive. -/
lemma giso_trans {X Y Z : Subgroup G × Subgroup G} :
    GroupQuotIso X Y → GroupQuotIso Y Z → GroupQuotIso X Z := by
  rintro ⟨hn1, hn2, f⟩ ⟨hn2', hn3, g⟩
  refine ⟨hn1, hn3, ?_⟩
  haveI := hn1; haveI := hn2; haveI := hn2'; haveI := hn3
  rcases f with ⟨e1⟩; rcases g with ⟨e2⟩; exact ⟨e1.trans e2⟩

-- ============================================================
-- PART II: Structural facts (fully proved)
-- ============================================================

variable {A A' B B' : Subgroup G}

/-- The left tower bottom is below its top: `A ⊔ (A' ⊓ B) ≤ A ⊔ (A' ⊓ B')`. -/
lemma tower_le (hB : B ≤ B') : A ⊔ (A' ⊓ B) ≤ A ⊔ (A' ⊓ B') :=
  sup_le_sup_left (inf_le_inf_left A' hB) A

/-- The common middle sits inside the common intersection: `M ≤ I`. -/
lemma middle_le_inter (hA : A ≤ A') (hB : B ≤ B') :
    (A ⊓ B') ⊔ (A' ⊓ B) ≤ A' ⊓ B' :=
  sup_le (le_inf (inf_le_left.trans hA) inf_le_right)
         (le_inf inf_le_left (inf_le_right.trans hB))

/-- The intersection `I = A' ⊓ B'` is symmetric under swapping the two towers. -/
lemma inter_symm : A' ⊓ B' = B' ⊓ A' := inf_comm _ _

/-- The common middle `M` is symmetric under swapping the two towers:
    `(A ⊓ B') ⊔ (A' ⊓ B) = (B ⊓ A') ⊔ (B' ⊓ A)`. -/
lemma middle_symm : (A ⊓ B') ⊔ (A' ⊓ B) = (B ⊓ A') ⊔ (B' ⊓ A) := by
  rw [sup_comm, inf_comm A B', inf_comm A' B]

/-- **`M ⊴ I`** — the common middle is normal in the common intersection.
    Both `A ⊓ B'` and `A' ⊓ B` are normal in `A' ⊓ B'` (restrictions of the
    normalities `A ⊴ A'` and `B ⊴ B'`), and a join of normal subgroups is normal. -/
lemma middle_normal (hA : A ≤ A') (hB : B ≤ B')
    (hAn : (A.subgroupOf A').Normal) (hBn : (B.subgroupOf B').Normal) :
    (((A ⊓ B') ⊔ (A' ⊓ B)).subgroupOf (A' ⊓ B')).Normal := by
  -- `A ⊓ B'` is normal in `A' ⊓ B'`: conjugating by `A' ⊓ B' ≤ A.normalizer`.
  have hAn' : ((A ⊓ B').subgroupOf (A' ⊓ B')).Normal := by
    have hle : (A' ⊓ B' : Subgroup G) ≤ A.normalizer := by
      have hAA' : (A' : Subgroup G) ≤ A.normalizer :=
        (normal_subgroupOf_iff_le_normalizer hA).mp hAn
      exact inf_le_left.trans hAA'
    have hnorm : ((A.subgroupOf (A' ⊓ B')).Normal) :=
      normal_subgroupOf_of_le_normalizer hle
    have hrw : (A ⊓ B' : Subgroup G) = A ⊓ (A' ⊓ B') := by
      rw [← inf_assoc, inf_eq_left.mpr hA]
    rw [hrw, inf_subgroupOf_right]
    exact hnorm
  -- `A' ⊓ B` is normal in `A' ⊓ B'`: conjugating by `A' ⊓ B' ≤ B.normalizer`.
  have hBn' : ((A' ⊓ B).subgroupOf (A' ⊓ B')).Normal := by
    have hle : (A' ⊓ B' : Subgroup G) ≤ B.normalizer := by
      have hBB' : (B' : Subgroup G) ≤ B.normalizer :=
        (normal_subgroupOf_iff_le_normalizer hB).mp hBn
      exact inf_le_right.trans hBB'
    have hnorm : ((B.subgroupOf (A' ⊓ B')).Normal) :=
      normal_subgroupOf_of_le_normalizer hle
    have hrw : (A' ⊓ B : Subgroup G) = B ⊓ (A' ⊓ B') := by
      rw [← inf_assoc, inf_comm B A', inf_assoc, inf_eq_left.mpr hB]
    rw [hrw, inf_subgroupOf_right]
    exact hnorm
  -- join of two normal subgroups is normal (same idiom as OQ-04 `sup_eq_of_isMaximal`)
  have h1 : (A ⊓ B' : Subgroup G) ≤ A' ⊓ B' := le_inf (inf_le_left.trans hA) inf_le_right
  have h2 : (A' ⊓ B : Subgroup G) ≤ A' ⊓ B' := le_inf inf_le_left (inf_le_right.trans hB)
  rw [subgroupOf_sup h1 h2]
  haveI := hAn'; haveI := hBn'
  infer_instance

-- ============================================================
-- PART III: The core half-isomorphism (Aristotle target)
-- ============================================================

/-- **Zassenhaus half-isomorphism** (core content).

    `U_A ⧸ L_A ≃* I ⧸ M`, i.e.
    `(A ⊔ (A'⊓B')) ⧸ (A ⊔ (A'⊓B)) ≃* (A'⊓B') ⧸ ((A⊓B') ⊔ (A'⊓B))`.

    Proof route (see file header): second isomorphism theorem via an explicit
    surjection `mk' ∘ inclusion : (A'⊓B') →* U_A ⧸ L_A.subgroupOf U_A`, whose
    kernel is `M` by the Dedekind law `Subgroup.inf_mul_assoc`. Mirrors OQ-04's
    `second_iso`. -/
theorem zassenhaus_half (hA : A ≤ A') (hB : B ≤ B')
    (hAn : (A.subgroupOf A').Normal) (hBn : (B.subgroupOf B').Normal) :
    GroupQuotIso (A ⊔ (A' ⊓ B), A ⊔ (A' ⊓ B')) ((A ⊓ B') ⊔ (A' ⊓ B), A' ⊓ B') := by
  sorry

-- ============================================================
-- PART IV: The full butterfly (PROVED from the half + symmetry)
-- ============================================================

/-- **Zassenhaus butterfly lemma.**

    `(A ⊔ (A'⊓B')) ⧸ (A ⊔ (A'⊓B)) ≃* (B ⊔ (B'⊓A')) ⧸ (B ⊔ (B'⊓A))`.

    The two Jordan-Hölder "tower" quotients are isomorphic. Proved by applying
    `zassenhaus_half` to each tower (the second with `A,A'` and `B,B'` swapped)
    and composing through the common middle quotient `I ⧸ M`. -/
theorem zassenhaus_butterfly (hA : A ≤ A') (hB : B ≤ B')
    (hAn : (A.subgroupOf A').Normal) (hBn : (B.subgroupOf B').Normal) :
    GroupQuotIso (A ⊔ (A' ⊓ B), A ⊔ (A' ⊓ B')) (B ⊔ (B' ⊓ A), B ⊔ (B' ⊓ A')) := by
  -- Left tower ≃ common middle.
  have hleft : GroupQuotIso (A ⊔ (A' ⊓ B), A ⊔ (A' ⊓ B'))
      ((A ⊓ B') ⊔ (A' ⊓ B), A' ⊓ B') := zassenhaus_half hA hB hAn hBn
  -- Right tower ≃ common middle (swap the roles of A and B).
  have hright : GroupQuotIso (B ⊔ (B' ⊓ A), B ⊔ (B' ⊓ A'))
      ((B ⊓ A') ⊔ (B' ⊓ A), B' ⊓ A') := zassenhaus_half hB hA hBn hAn
  -- The two common middles coincide: `(M', I') = (M, I)`.
  have hM : (B ⊓ A') ⊔ (B' ⊓ A) = (A ⊓ B') ⊔ (A' ⊓ B) := (middle_symm).symm
  have hI : (B' ⊓ A' : Subgroup G) = A' ⊓ B' := inf_comm _ _
  rw [hM, hI] at hright
  -- Compose: left ≃ middle ≃ right.
  exact giso_trans hleft (giso_symm hright)

-- ============================================================
-- PART V: Verification
-- ============================================================

#check @zassenhaus_butterfly
#check @zassenhaus_half
#check @middle_normal

end AbelRuffiniGaloisExtensionsOQ04OQ03
