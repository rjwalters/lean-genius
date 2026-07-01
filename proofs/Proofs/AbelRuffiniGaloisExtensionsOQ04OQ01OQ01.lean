/-
  Abel–Ruffini / Galois extensions, Jordan–Hölder branch (oq-04), open
  question oq-01, follow-up oq-01:

      "The fully general `K`/`subgroupOf` version (working inside the subtype
       group `↥K`) is left for the upstream Mathlib development."
                       — AbelRuffiniGaloisExtensionsOQ04OQ01.lean

  The parent entry (`…OQ04`) defines the *relative* predicate `IsMaxNorm H K`
  ("H is a maximal normal subgroup of K") and states — without proof — that it
  is equivalent to `IsSimpleGroup (↥K ⧸ H.subgroupOf K)` "by the correspondence
  theorem, but avoids quotient typeclass issues".  Its child (`…OQ04OQ01`) then
  proved the `K = ⊤` instance of that bridge, explicitly deferring the general
  relative case.

  This file settles the deferred general case, axiom-free:

      given `H ≤ K` and `(H.subgroupOf K).Normal`,
        `IsSimpleGroup (↥K ⧸ H.subgroupOf K)  ↔  IsMaxNorm H K`.

  The mathematical content beyond the `K = ⊤` case is the lattice transfer
  between `Subgroup ↥K` and the interval `[H, K]` of `Subgroup G`, carried out
  through `Subgroup.map K.subtype` / `Subgroup.subgroupOf K` and their round
  trips.  This lets the abstract simplicity of the subtype quotient `↥K ⧸ …`
  be tested entirely inside the ambient group `G`, which is what a
  composition-series / Jordan–Hölder development actually needs.

  Main results:
    * `isMaximalNormal_subgroupOf_iff_isMaxNorm` — the lattice-transfer bridge
      `IsMaximalNormal (H.subgroupOf K) ↔ IsMaxNorm H K` (for `H ≤ K`);
    * `isSimpleGroup_quotient_subgroupOf_iff_isMaxNorm` — the packaged
      correspondence `IsSimpleGroup (↥K ⧸ H.subgroupOf K) ↔ IsMaxNorm H K`;
    * `IsMaxNorm.isSimpleGroup_quotient` / `.of_isSimpleGroup_quotient`
      — the two directions as standalone lemmas.

  The absolute (`K = ⊤`) correspondence is reproved inline (self-contained,
  Mathlib-only) so the file has no dependency beyond `import Mathlib`.
-/

import Mathlib

open Subgroup QuotientGroup

namespace AbelRuffiniGaloisExtensionsOQ04OQ01OQ01

variable {G : Type*} [Group G]

/-! ## The absolute correspondence (reproved inline, `K = ⊤` case) -/

/-- `N` is a **maximal normal subgroup** of `G`: normal, proper, and not
strictly contained in any proper normal subgroup. -/
def IsMaximalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊤ ∧ ∀ M : Subgroup G, N ≤ M → M.Normal → M = N ∨ M = ⊤

/-- **Simple quotient ⇔ maximal normal subgroup** (absolute form).

For a normal subgroup `N ◁ G`, the quotient `G ⧸ N` is simple iff `N` is
proper and maximal among proper normal subgroups. -/
theorem isSimpleGroup_quotient_iff (N : Subgroup G) [N.Normal] :
    IsSimpleGroup (G ⧸ N) ↔
      N ≠ ⊤ ∧ ∀ M : Subgroup G, N ≤ M → M.Normal → M = N ∨ M = ⊤ := by
  rw [isSimpleGroup_iff]
  constructor
  · rintro ⟨hnt, hbt⟩
    refine ⟨?_, ?_⟩
    · intro hN
      subst hN
      exact (not_subsingleton (G ⧸ (⊤ : Subgroup G))) subsingleton_quotient_top
    · intro M hNM hM
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
    · have hns : ¬ Subsingleton (G ⧸ N) :=
        fun h => hNtop (subgroup_eq_top_of_subsingleton N h)
      exact not_subsingleton_iff_nontrivial.mp hns
    · intro H' hH'
      have hcN : N ≤ Subgroup.comap (mk' N) H' := le_comap_mk' N H'
      rcases hmax (Subgroup.comap (mk' N) H') hcN inferInstance with h | h
      · left
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

/-- Packaged absolute form via `IsMaximalNormal`. -/
theorem isSimpleGroup_quotient_iff_isMaximalNormal (N : Subgroup G) [hN : N.Normal] :
    IsSimpleGroup (G ⧸ N) ↔ IsMaximalNormal N := by
  rw [isSimpleGroup_quotient_iff N, IsMaximalNormal]
  exact ⟨fun h => ⟨hN, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

/-! ## The relative predicate and the lattice-transfer bridge -/

/-- `H` is a **maximal normal subgroup of `K`** (parent entry `…OQ04`):
`H < K`, `H` is relatively normal in `K`, and every normal-in-`K` subgroup
between `H` and `K` equals `H` or `K`. -/
def IsMaxNorm (H K : Subgroup G) : Prop :=
  H < K ∧
  (H.subgroupOf K).Normal ∧
  ∀ N : Subgroup G, H ≤ N → N ≤ K → (N.subgroupOf K).Normal → N = H ∨ N = K

/-- **Lattice-transfer bridge.**  For `H ≤ K`, being a maximal normal subgroup
of the subtype group `↥K` (i.e. `IsMaximalNormal (H.subgroupOf K)`) is exactly
the relative predicate `IsMaxNorm H K` stated in the ambient group `G`.

This is the crux the open question flags: it moves the maximality test from the
inaccessible subtype lattice `Subgroup ↥K` into the concrete interval `[H, K]`
of `Subgroup G`, using the `map K.subtype` / `subgroupOf K` correspondence. -/
theorem isMaximalNormal_subgroupOf_iff_isMaxNorm
    {H K : Subgroup G} (hHK : H ≤ K) :
    IsMaximalNormal (H.subgroupOf K) ↔ IsMaxNorm H K := by
  constructor
  · rintro ⟨hnorm, hne, hmax⟩
    refine ⟨?_, hnorm, ?_⟩
    · -- `H < K`: `H ≤ K` and `H ≠ K` (else `H.subgroupOf K = ⊤`).
      refine lt_of_le_of_ne hHK ?_
      intro hHKeq
      exact hne (by rw [hHKeq, subgroupOf_self])
    · -- relative maximality from subtype maximality via `N ↦ N.subgroupOf K`.
      intro N hHN hNK hNnorm
      have hle : H.subgroupOf K ≤ N.subgroupOf K := by
        simpa only [subgroupOf] using comap_mono hHN
      rcases hmax (N.subgroupOf K) hle hNnorm with h | h
      · left
        -- `N.subgroupOf K = H.subgroupOf K`, push through `map K.subtype`.
        have := congrArg (Subgroup.map K.subtype) h
        rwa [map_subgroupOf_eq_of_le hNK, map_subgroupOf_eq_of_le hHK] at this
      · right
        -- `N.subgroupOf K = ⊤` means `K ≤ N`, with `N ≤ K` gives `N = K`.
        exact le_antisymm hNK (subgroupOf_eq_top.mp h)
  · rintro ⟨hlt, hnorm, hmax⟩
    refine ⟨hnorm, ?_, ?_⟩
    · -- `H.subgroupOf K ≠ ⊤` since `H ≠ K` and `H ≤ K`.
      rw [Ne, subgroupOf_eq_top]
      exact fun hKH => absurd (le_antisymm hHK hKH) hlt.ne
    · -- subtype maximality from relative maximality via `M ↦ M.map K.subtype`.
      intro M hHM hMnorm
      set N : Subgroup G := M.map K.subtype with hN
      have hNK : N ≤ K := map_subtype_le M
      have hMback : N.subgroupOf K = M := by
        rw [hN, subgroupOf, comap_map_eq_self_of_injective K.subtype_injective]
      have hHN : H ≤ N := by
        have : (H.subgroupOf K).map K.subtype ≤ M.map K.subtype := map_mono hHM
        rwa [map_subgroupOf_eq_of_le hHK] at this
      have hNnorm : (N.subgroupOf K).Normal := by rw [hMback]; exact hMnorm
      rcases hmax N hHN hNK hNnorm with h | h
      · left; rw [← hMback, h]
      · right; rw [← hMback, h, subgroupOf_self]

/-! ## The packaged relative correspondence -/

/-- **General relative correspondence** (the deferred `subgroupOf` case).

For `H ≤ K` with `H.subgroupOf K` normal in `↥K`, the subtype quotient
`↥K ⧸ H.subgroupOf K` is simple iff `H` is a maximal normal subgroup of `K`. -/
theorem isSimpleGroup_quotient_subgroupOf_iff_isMaxNorm
    {H K : Subgroup G} (hHK : H ≤ K) [(H.subgroupOf K).Normal] :
    IsSimpleGroup (↥K ⧸ H.subgroupOf K) ↔ IsMaxNorm H K := by
  rw [isSimpleGroup_quotient_iff_isMaximalNormal (H.subgroupOf K),
      isMaximalNormal_subgroupOf_iff_isMaxNorm hHK]

/-- Maximal-normal ⇒ simple subtype quotient. -/
theorem IsMaxNorm.isSimpleGroup_quotient
    {H K : Subgroup G} (hHK : H ≤ K) (h : IsMaxNorm H K) :
    haveI := h.2.1; IsSimpleGroup (↥K ⧸ H.subgroupOf K) := by
  haveI := h.2.1
  exact (isSimpleGroup_quotient_subgroupOf_iff_isMaxNorm hHK).mpr h

/-- Simple subtype quotient ⇒ maximal-normal. -/
theorem IsMaxNorm.of_isSimpleGroup_quotient
    {H K : Subgroup G} (hHK : H ≤ K) [(H.subgroupOf K).Normal]
    (h : IsSimpleGroup (↥K ⧸ H.subgroupOf K)) : IsMaxNorm H K :=
  (isSimpleGroup_quotient_subgroupOf_iff_isMaxNorm hHK).mp h

end AbelRuffiniGaloisExtensionsOQ04OQ01OQ01
