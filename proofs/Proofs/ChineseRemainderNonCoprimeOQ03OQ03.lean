/-
  CRT Non-Coprime OQ-03-OQ-03: Chinese Remainder Theorem for Modules

  The parent chain (ChineseRemainderNonCoprime …) established the Chinese
  Remainder Theorem for **elements** of a Euclidean domain: a system of
  congruences `x ≡ aᵢ (mod mᵢ)` is solvable iff the pairwise gcd conditions
  hold.  This open question elevates the result to the **module** level, where
  it becomes a structural isomorphism rather than a solvability criterion.

  ## Main result

  Let `R` be a commutative ring, `M` an `R`-module, and `I, J ⊆ R` two
  *comaximal* ideals (`I ⊔ J = ⊤`).  Then

        M ⧸ (I • M ⊓ J • M)  ≅  (M ⧸ I • M) × (M ⧸ J • M)

  as `R`-modules, where `I • M` abbreviates the submodule `I • (⊤ : Submodule R M)`.

  Under comaximality the "denominator" simplifies, `(I ⊓ J) • M = I • M ⊓ J • M`,
  so the isomorphism takes the textbook form

        M ⧸ (I ⊓ J) • M  ≅  (M ⧸ I • M) × (M ⧸ J • M).

  Specialising to a principal ideal domain, two coprime elements `a, b` generate
  comaximal ideals, recovering `M ⧸ (a * b) • M ≅ M ⧸ a • M × M ⧸ b • M`.

  ## Proof architecture

  The whole theorem is the first isomorphism theorem applied to the product of
  the two quotient maps `φ = (I • ⊤).mkQ.prod (J • ⊤).mkQ`:

  * `crtMap_surjective` — surjectivity of `φ`.  This is the only place the
    comaximality hypothesis is used: writing `1 = i + j` with `i ∈ I`, `j ∈ J`,
    the element `j • m₁ + i • m₂` reduces to `m₁` modulo `I • M` and to `m₂`
    modulo `J • M`.
  * `ker_crtMap` — the kernel of `φ` is `I • ⊤ ⊓ J • ⊤` (a formal consequence of
    `LinearMap.ker_prod` and `Submodule.ker_mkQ`, needing no hypothesis).
  * `crtEquiv` — `LinearMap.quotKerEquivOfSurjective` packages the two facts
    into the isomorphism.
  * `inf_smul_top` — comaximality forces `(I ⊓ J) • ⊤ = I • ⊤ ⊓ J • ⊤`.
  * `crtEquiv'` / `crtEquivPID` — the textbook form and the PID specialisation.

  No axioms, no sorries; self-contained over Mathlib.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace ChineseRemainderModuleCRT

open Submodule LinearMap

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable (I J : Ideal R)

/-- The Chinese-Remainder linear map `M → (M ⧸ I•M) × (M ⧸ J•M)`,
the pairing of the two canonical quotient projections. -/
noncomputable def crtMap : M →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) × (M ⧸ J • (⊤ : Submodule R M)) :=
  (I • (⊤ : Submodule R M)).mkQ.prod (J • (⊤ : Submodule R M)).mkQ

@[simp] theorem crtMap_apply (m : M) :
    crtMap I J m =
      ((I • (⊤ : Submodule R M)).mkQ m, (J • (⊤ : Submodule R M)).mkQ m) := rfl

/-- The kernel of the CRT map is `I•M ⊓ J•M`.  No coprimality is needed. -/
theorem ker_crtMap :
    LinearMap.ker (crtMap I J) =
      I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M) := by
  rw [crtMap, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]

/-- **Surjectivity** of the CRT map for comaximal ideals.  This is the analytic
heart of the theorem: the witness `1 = i + j` lets us hit any target pair. -/
theorem crtMap_surjective (h : I ⊔ J = ⊤) :
    Function.Surjective (crtMap (M := M) I J) := by
  -- Comaximality gives `i ∈ I`, `j ∈ J` with `i + j = 1`.
  obtain ⟨i, hi, j, hj, hij⟩ :=
    Submodule.mem_sup.mp (show (1 : R) ∈ I ⊔ J by rw [h]; exact Submodule.mem_top)
  rintro ⟨y₁, y₂⟩
  -- Lift the two quotient targets to honest module elements.
  obtain ⟨m₁, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective y₁
  obtain ⟨m₂, rfl⟩ := (J • (⊤ : Submodule R M)).mkQ_surjective y₂
  refine ⟨j • m₁ + i • m₂, ?_⟩
  rw [crtMap_apply, Prod.mk.injEq]
  constructor
  · -- `(j•m₁ + i•m₂) - m₁ = i • (m₂ - m₁) ∈ I•M`.
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hsub : (j • m₁ + i • m₂) - m₁ = i • (m₂ - m₁) := by
      have hj1 : j = 1 - i := by linear_combination hij
      subst hj1; module
    rw [hsub]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  · -- `(j•m₁ + i•m₂) - m₂ = j • (m₁ - m₂) ∈ J•M`.
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hsub : (j • m₁ + i • m₂) - m₂ = j • (m₁ - m₂) := by
      have hi1 : i = 1 - j := by linear_combination hij
      subst hi1; module
    rw [hsub]
    exact Submodule.smul_mem_smul hj Submodule.mem_top

/-- **Chinese Remainder Theorem for modules** (core form).
For comaximal ideals `I, J`, the canonical map induces an `R`-linear isomorphism

    `M ⧸ (I•M ⊓ J•M) ≃ₗ[R] (M ⧸ I•M) × (M ⧸ J•M)`. -/
noncomputable def crtEquiv (h : I ⊔ J = ⊤) :
    (M ⧸ (I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M))) ≃ₗ[R]
      (M ⧸ I • (⊤ : Submodule R M)) × (M ⧸ J • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (ker_crtMap I J).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (crtMap_surjective I J h))

/-- Under comaximality the two natural "denominators" coincide:
`(I ⊓ J) • M = I • M ⊓ J • M`.  (The inclusion `⊆` always holds; `⊇` uses
`1 = i + j` together with `I • J • M ≤ (I ⊓ J) • M`.) -/
theorem inf_smul_top (h : I ⊔ J = ⊤) :
    (I ⊓ J) • (⊤ : Submodule R M) =
      I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M) := by
  refine le_antisymm ?_ ?_
  · -- `(I ⊓ J) • ⊤ ≤ I • ⊤` and `≤ J • ⊤`, hence `≤` the inf.
    refine le_inf ?_ ?_
    · exact Submodule.smul_le.2 fun r hr m _ =>
        Submodule.smul_mem_smul (Submodule.mem_inf.1 hr).1 Submodule.mem_top
    · exact Submodule.smul_le.2 fun r hr m _ =>
        Submodule.smul_mem_smul (Submodule.mem_inf.1 hr).2 Submodule.mem_top
  · -- For `x` in both, `x = i•x + j•x` with each summand in `(I⊓J)•⊤`.
    obtain ⟨i, hi, j, hj, hij⟩ :=
      Submodule.mem_sup.mp (show (1 : R) ∈ I ⊔ J by rw [h]; exact Submodule.mem_top)
    -- `I • (J • ⊤) ≤ (I ⊓ J) • ⊤` and symmetrically.
    have hIJ : I • (J • (⊤ : Submodule R M)) ≤ (I ⊓ J) • (⊤ : Submodule R M) := by
      rw [← Submodule.mul_smul]
      exact Submodule.smul_mono_left Ideal.mul_le_inf
    have hJI : J • (I • (⊤ : Submodule R M)) ≤ (I ⊓ J) • (⊤ : Submodule R M) := by
      rw [← Submodule.mul_smul]
      exact Submodule.smul_mono_left (le_trans Ideal.mul_le_inf (le_of_eq (inf_comm J I)))
    intro x hx
    obtain ⟨hxI, hxJ⟩ := Submodule.mem_inf.1 hx
    have hx_eq : x = i • x + j • x := by
      rw [← add_smul, hij, one_smul]
    rw [hx_eq]
    refine Submodule.add_mem _ ?_ ?_
    · exact hIJ (Submodule.smul_mem_smul hi hxJ)
    · exact hJI (Submodule.smul_mem_smul hj hxI)

/-- **Chinese Remainder Theorem for modules** (textbook form).
For comaximal ideals, `M ⧸ (I ⊓ J)•M ≅ (M ⧸ I•M) × (M ⧸ J•M)`. -/
noncomputable def crtEquiv' (h : I ⊔ J = ⊤) :
    (M ⧸ (I ⊓ J) • (⊤ : Submodule R M)) ≃ₗ[R]
      (M ⧸ I • (⊤ : Submodule R M)) × (M ⧸ J • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (inf_smul_top I J h)).trans (crtEquiv I J h)

/-- **PID specialisation.**  Two coprime ring elements generate comaximal
principal ideals, so the module CRT applies to `span {a}` and `span {b}`. -/
noncomputable def crtEquivPID {a b : R} (hab : IsCoprime a b) :
    (M ⧸ (Ideal.span {a} ⊓ Ideal.span {b}) • (⊤ : Submodule R M)) ≃ₗ[R]
      (M ⧸ Ideal.span {a} • (⊤ : Submodule R M)) ×
        (M ⧸ Ideal.span {b} • (⊤ : Submodule R M)) :=
  crtEquiv' (Ideal.span {a}) (Ideal.span {b})
    (Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_span_singleton_iff a b).2 hab))

end ChineseRemainderModuleCRT
