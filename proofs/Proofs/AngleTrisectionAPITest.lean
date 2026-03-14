/-
  Test: Proving σ(ζ) = ζ⁻¹ for the -1 automorphism.
-/
import Mathlib

open Polynomial

section ConjAuto

-- Follow the same pattern as complex_conj_order_two in OQ01
variable (n : ℕ) (hn : 3 ≤ n)

private def np : ℕ+ := ⟨n, by omega⟩

-- Work in CyclotomicField directly
private noncomputable abbrev K := CyclotomicField (np n hn) ℚ

instance : FiniteDimensional ℚ (K n hn) := by
  unfold K np
  exact CyclotomicField.finiteDimensional {⟨n, by omega⟩} ℚ

-- Get primitive root
-- In the OQ01 file, exists_prim_root is used but deprecated.
-- Let me use the pattern from KroneckersJugendtraum.lean
noncomputable def getζ : K n hn := by
  have := IsCyclotomicExtension.exists_prim_root ℚ (B := K n hn)
    (Set.mem_singleton (np n hn)) (by simp [np]; omega)
  exact this.choose

lemma getζ_prim : IsPrimitiveRoot (getζ n hn) (np n hn) := by
  have := IsCyclotomicExtension.exists_prim_root ℚ (B := K n hn)
    (Set.mem_singleton (np n hn)) (by simp [np]; omega)
  exact this.choose_spec

-- The cyclotomic polynomial is irreducible
lemma hirr : Irreducible (cyclotomic (np n hn) ℚ) :=
  cyclotomic.irreducible_rat (np n hn).val (np n hn).pos

-- autEquivPow
noncomputable def hequiv : (K n hn ≃ₐ[ℚ] K n hn) ≃* (ZMod (np n hn))ˣ :=
  IsCyclotomicExtension.autEquivPow ℚ (K n hn) (np n hn) (hirr n hn)

-- The -1 automorphism
noncomputable def σ_neg1 : K n hn ≃ₐ[ℚ] K n hn :=
  (hequiv n hn).symm (-1 : (ZMod (np n hn))ˣ)

-- Key fact: hequiv σ_neg1 = -1
lemma hequiv_σ_neg1 : hequiv n hn (σ_neg1 n hn) = -1 :=
  MulEquiv.apply_symm_apply _ _

-- Now: σ_neg1 sends ζ to ζ⁻¹
-- Strategy: use autToPow_spec and the fact that autEquivPow.toFun = autToPow
theorem σ_neg1_sends_inv :
    σ_neg1 n hn (getζ n hn) = (getζ n hn)⁻¹ := by
  set ζ := getζ n hn
  set hζ := getζ_prim n hn
  set σ := σ_neg1 n hn
  -- Use autToPow_spec: ζ ^ (autToPow ℚ hζ σ).val = σ ζ
  have spec := IsPrimitiveRoot.autToPow_spec ℚ hζ σ
  rw [← spec]
  -- Goal: ζ ^ (autToPow ℚ hζ σ).val = ζ⁻¹
  -- Need: (autToPow ℚ hζ σ).val = ZMod.val (-1 : ZMod (np n hn))
  -- Which: = n - 1
  -- Then: ζ^(n-1) = ζ⁻¹ (from ζ^n = 1)
  sorry

end ConjAuto
