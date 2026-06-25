/-
  Abel–Ruffini / Galois extensions, Jordan–Hölder branch (oq-04), open
  question oq-01:

      "Mathlib contribution: can `JordanHolderLattice (Subgroup G)` be
       contributed upstream? The main challenge is generalizing the `IsMaxNorm`
       predicate to work with `IsSimpleGroup (K ⧸ H)` directly."

  The parent entry (`AbelRuffiniGaloisExtensionsOQ04`) defines a combinatorial
  predicate `IsMaxNorm H K` ("H is a maximal normal subgroup of K") and remarks
  that it is *equivalent* to `IsSimpleGroup (K ⧸ H.subgroupOf K)` "by the
  correspondence theorem, but avoids quotient typeclass issues" — without
  proving that equivalence.

  This file proves exactly that bridge in the essential case `K = ⊤`,
  axiom-free: a normal subgroup `N ◁ G` has a *simple quotient* `G ⧸ N` iff it
  is a *maximal normal subgroup* of `G`. The proof is short because it routes
  everything through Mathlib's fourth isomorphism / correspondence theorem
  (`QuotientGroup.comapMk'OrderIso`) rather than re-deriving the lattice
  correspondence.

  Main results:
    * `isSimpleGroup_quotient_iff` — `IsSimpleGroup (G ⧸ N) ↔ N` is maximal
      among proper normal subgroups;
    * `isSimpleGroup_quotient_iff_isMaximalNormal` — the packaged form using the
      `IsMaximalNormal` predicate;
    * `IsMaximalNormal.isSimpleGroup_quotient` / `.of_isSimpleGroup_quotient`
      — the two directions as standalone lemmas.

  This settles the `IsMaxNorm`↔`IsSimpleGroup` correspondence that the open
  question identifies as the crux; the fully general `K`/`subgroupOf` version
  (working inside the subtype group `↥K`) is left for the upstream Mathlib
  development.
-/

import Mathlib

open Subgroup QuotientGroup

namespace AbelRuffiniGaloisExtensionsOQ04OQ01

variable {G : Type*} [Group G]

/-- `N` is a **maximal normal subgroup** of `G`: normal, proper, and not strictly
contained in any proper normal subgroup. (The `K = ⊤` instance of the parent
entry's `IsMaxNorm`.) -/
def IsMaximalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊤ ∧ ∀ M : Subgroup G, N ≤ M → M.Normal → M = N ∨ M = ⊤

/-- **Simple quotient ⇔ maximal normal subgroup.**

For a normal subgroup `N ◁ G`, the quotient `G ⧸ N` is simple if and only if
`N` is proper and maximal among proper normal subgroups. This is the
`IsMaxNorm`/`IsSimpleGroup` correspondence (for `K = ⊤`) flagged by oq-01. -/
theorem isSimpleGroup_quotient_iff (N : Subgroup G) [N.Normal] :
    IsSimpleGroup (G ⧸ N) ↔
      N ≠ ⊤ ∧ ∀ M : Subgroup G, N ≤ M → M.Normal → M = N ∨ M = ⊤ := by
  rw [isSimpleGroup_iff]
  constructor
  · rintro ⟨hnt, hbt⟩
    refine ⟨?_, ?_⟩
    · -- `N ≠ ⊤`, else the quotient is trivial.
      intro hN
      subst hN
      exact (not_subsingleton (G ⧸ (⊤ : Subgroup G))) subsingleton_quotient_top
    · intro M hNM hM
      -- Push `M` into the quotient; normal, so `⊥` or `⊤`.
      rcases hbt (M.map (mk' N)) inferInstance with h | h
      · left
        have hc : Subgroup.comap (mk' N) (M.map (mk' N))
            = Subgroup.comap (mk' N) (⊥ : Subgroup (G ⧸ N)) := by rw [h]
        rw [comap_map_mk' N M, MonoidHom.comap_bot, ker_mk', sup_eq_right.mpr hNM] at hc
        exact hc
      · right
        have hc : Subgroup.comap (mk' N) (M.map (mk' N))
            = Subgroup.comap (mk' N) (⊤ : Subgroup (G ⧸ N)) := by rw [h]
        rw [comap_map_mk' N M, comap_top, sup_eq_right.mpr hNM] at hc
        exact hc
  · rintro ⟨hNtop, hmax⟩
    refine ⟨?_, ?_⟩
    · -- `G ⧸ N` is nontrivial because `N ≠ ⊤`.
      have hns : ¬ Subsingleton (G ⧸ N) :=
        fun h => hNtop (subgroup_eq_top_of_subsingleton N h)
      exact not_subsingleton_iff_nontrivial.mp hns
    · intro H' hH'
      -- Pull `H'` back; it is normal and contains `N`, so equals `N` or `⊤`.
      have hcN : N ≤ Subgroup.comap (mk' N) H' := le_comap_mk' N H'
      rcases hmax (Subgroup.comap (mk' N) H') hcN inferInstance with h | h
      · left
        -- `comap H' = N = comap ⊥`, and `comap` (the correspondence map) is injective.
        have hb : Subgroup.comap (mk' N) (⊥ : Subgroup (G ⧸ N)) = N := by
          rw [MonoidHom.comap_bot, ker_mk']
        apply (comapMk'OrderIso N).injective
        apply Subtype.ext
        simp only [comapMk'OrderIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk]
        rw [h, hb]
      · right
        have ht : Subgroup.comap (mk' N) (⊤ : Subgroup (G ⧸ N)) = ⊤ := comap_top _
        apply (comapMk'OrderIso N).injective
        apply Subtype.ext
        simp only [comapMk'OrderIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk]
        rw [h, ht]

/-- The packaged equivalence with the `IsMaximalNormal` predicate. -/
theorem isSimpleGroup_quotient_iff_isMaximalNormal (N : Subgroup G) [hN : N.Normal] :
    IsSimpleGroup (G ⧸ N) ↔ IsMaximalNormal N := by
  rw [isSimpleGroup_quotient_iff N, IsMaximalNormal]
  exact ⟨fun h => ⟨hN, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

/-- A maximal normal subgroup has a simple quotient. -/
theorem IsMaximalNormal.isSimpleGroup_quotient {N : Subgroup G} (h : IsMaximalNormal N) :
    haveI := h.1; IsSimpleGroup (G ⧸ N) := by
  haveI := h.1
  exact (isSimpleGroup_quotient_iff_isMaximalNormal N).mpr h

/-- If `G ⧸ N` is simple (with `N` normal) then `N` is a maximal normal subgroup. -/
theorem IsMaximalNormal.of_isSimpleGroup_quotient {N : Subgroup G} [N.Normal]
    (h : IsSimpleGroup (G ⧸ N)) : IsMaximalNormal N :=
  (isSimpleGroup_quotient_iff_isMaximalNormal N).mp h

end AbelRuffiniGaloisExtensionsOQ04OQ01
