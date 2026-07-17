/-
  Primitive Solvable Permutation Groups of Prime Degree — Metabelian corollary
  (downstream of sub-OQ-06 Galois direction)

  The parent file `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`
  proves Galois's 1832 structure theorem: every primitive solvable subgroup
  `H ≤ S_p = Equiv.Perm (ZMod p)` embeds into the affine group
  `AGL(1, p) = ℤ/pℤ ⋊ (ℤ/pℤ)ˣ` via an injective homomorphism
  `φ : H →* AGL1Z p` (`primitive_solvable_subgroup_embeds_AGL1Z`).

  This file records the **metabelian** structural consequence of that
  embedding — a materially weaker structural corollary flagged as a valid
  child OQ in the parent's `nextSteps`:

    every primitive solvable subgroup `H ≤ S_p` is metabelian
    (its derived length is at most `2`, i.e. `derivedSeries ↥H 2 = ⊥`).

  The proof has two ingredients, both self-contained here:

  1. `AGL1Z_derivedSeries_two_eq_bot` — `AGL(1, p)` is itself metabelian.
     The scale projection `scaleHom : AGL1Z p →* (ZMod p)ˣ` has commutative
     codomain, so the first derived subgroup lands in its kernel (the pure
     translations `K = ker scaleHom`); and `K` is commutative (translations
     `(a, 1)` commute), so `⁅K, K⁆ = ⊥`.  Hence
     `derivedSeries (AGL1Z p) 2 = ⁅derivedSeries 1, derivedSeries 1⁆
        ≤ ⁅K, K⁆ = ⊥`.

  2. Transfer along the injective embedding: derived series are functorial
     (`map_derivedSeries_le_derivedSeries`), so
     `(derivedSeries ↥H 2).map φ ≤ derivedSeries (AGL1Z p) 2 = ⊥`, and
     injectivity of `φ` (`φ.ker = ⊥`) pulls the bound back to
     `derivedSeries ↥H 2 = ⊥`.

  This is *strictly weaker* than the embedding theorem it is derived from
  (metabelian-ness does not recover the affine embedding), so it is a
  legitimate downstream corollary rather than an equivalent-strength
  restatement.  No new `sorry`, no axiom.
-/

import Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection
import Mathlib

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirection

open AbelRuffiniGaloisExtensionsOQ06

variable {p : ℕ} [Fact p.Prime]

/-- **The translation kernel of `AGL(1, p)` is commutative.**  The kernel of
    the scale projection `scaleHom : AGL1Z p →* (ZMod p)ˣ` is the subgroup of
    pure translations `(a, 1)`; any two such elements commute, so the
    subgroup-commutator `⁅K, K⁆` is trivial.

    Concretely `(a, 1)·(b, 1) = (a + b, 1) = (b, 1)·(a, 1)` because the scale
    factor is `1`, collapsing the semidirect-product twist to ordinary
    addition of translations. -/
theorem AGL1Z_scaleHom_ker_commutator_eq_bot :
    ⁅(AGL1Z.scaleHom p).ker, (AGL1Z.scaleHom p).ker⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  -- `g, h` are pure translations: their scale factors are `1`.
  have hgs : g.scale = 1 := MonoidHom.mem_ker.mp hg
  have hhs : h.scale = 1 := MonoidHom.mem_ker.mp hh
  apply AGL1Z.ext
  · -- translation coordinate: `h.trans + 1·g.trans = g.trans + 1·h.trans`
    rw [AGL1Z.mul_trans, AGL1Z.mul_trans, hgs, hhs]
    push_cast
    ring
  · -- scale coordinate: `1 · 1 = 1 · 1`
    rw [AGL1Z.mul_scale, AGL1Z.mul_scale, hgs, hhs]

/-- **`AGL(1, p)` is metabelian.**  Its second derived subgroup is trivial:
    `derivedSeries (AGL1Z p) 2 = ⊥`, i.e. the derived length is at most `2`.

    This sharpens the parent file's `AGL1Z_isSolvable` (which only asserts
    solvability, with no length bound) to the exact derived length of the
    abelian-by-abelian extension
    `1 → ℤ/pℤ → AGL(1, p) → (ℤ/pℤ)ˣ → 1`.

    Route: the first derived subgroup lands in `K = ker scaleHom` (the
    quotient `(ℤ/pℤ)ˣ` is abelian, so every commutator maps to `1`), and
    `K` is commutative (`AGL1Z_scaleHom_ker_commutator_eq_bot`), so
    `derivedSeries 2 = ⁅derivedSeries 1, derivedSeries 1⁆ ≤ ⁅K, K⁆ = ⊥`. -/
theorem AGL1Z_derivedSeries_two_eq_bot :
    derivedSeries (AGL1Z p) 2 = ⊥ := by
  -- (1) The first derived subgroup lands in the translation kernel `K`.
  have h1 : derivedSeries (AGL1Z p) 1 ≤ (AGL1Z.scaleHom p).ker := by
    rw [derivedSeries_succ, derivedSeries_zero, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact mul_comm _ _
  -- (2) `derivedSeries 2 = ⁅derivedSeries 1, derivedSeries 1⁆`.
  have e2 : derivedSeries (AGL1Z p) 2
      = ⁅derivedSeries (AGL1Z p) 1, derivedSeries (AGL1Z p) 1⁆ :=
    derivedSeries_succ (AGL1Z p) 1
  rw [e2]
  -- (3) Bound by `⁅K, K⁆ = ⊥` via monotonicity of the commutator.
  exact le_bot_iff.mp
    ((Subgroup.commutator_mono h1 h1).trans
      (le_of_eq AGL1Z_scaleHom_ker_commutator_eq_bot))

/-- **Corollary (Galois metabelian structure).**  Every primitive solvable
    subgroup `H ≤ S_p = Equiv.Perm (ZMod p)` is **metabelian**: its derived
    length is at most `2`, i.e. `derivedSeries ↥H 2 = ⊥`.

    Equivalently, the commutator subgroup `⁅H, H⁆` is abelian.  This is the
    structural refinement of the qualitative fact that `H` is solvable
    (`hSolv`): the affine embedding `φ : H ↪ AGL(1, p)`
    (`primitive_solvable_subgroup_embeds_AGL1Z`) into the metabelian group
    `AGL(1, p)` (`AGL1Z_derivedSeries_two_eq_bot`) pins the derived length to
    at most `2`, since derived series are functorial and `φ` is injective.

    It is strictly weaker than the embedding theorem (metabelian-ness does not
    reconstruct the affine embedding), a genuine downstream corollary of
    Galois's 1832 classification.  No new `sorry`, no axiom. -/
theorem primitive_solvable_subgroup_metabelian
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H) :
    derivedSeries (H : Type _) 2 = ⊥ := by
  obtain ⟨φ, hφ⟩ := primitive_solvable_subgroup_embeds_AGL1Z H hPrim hSolv
  -- Functoriality: the second derived subgroup maps into `AGL(1,p)`'s, which is `⊥`.
  have hmap : (derivedSeries (H : Type _) 2).map φ ≤ derivedSeries (AGL1Z p) 2 :=
    map_derivedSeries_le_derivedSeries φ 2
  rw [AGL1Z_derivedSeries_two_eq_bot] at hmap
  have hbot : (derivedSeries (H : Type _) 2).map φ = ⊥ := le_bot_iff.mp hmap
  rw [Subgroup.map_eq_bot_iff, φ.ker_eq_bot_iff.mpr hφ] at hbot
  exact le_bot_iff.mp hbot

end AbelRuffiniGaloisExtensionsOQ06GaloisDirection
