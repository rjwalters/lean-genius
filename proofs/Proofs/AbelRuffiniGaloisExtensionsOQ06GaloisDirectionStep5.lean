/-
  Step 5 decomposition for sub-OQ-06 (Galois direction)
  ──────────────────────────────────────────────────────

  Companion to `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`.
  This file is **deliberately NOT registered in `Proofs.lean`**: it is a
  build-pending decomposition candidate produced under a dual-backend
  blackout (Aristotle `prove` returns "Resource not found"; Docker host
  saturated at 6 concurrent build containers, ~10 GB free — below the safe
  ≤2-container build threshold). Registering it would risk the gallery
  build until a Docker-up session verifies it.

  ## What this contributes (researcher-4, 2026-06-15)

  The main file's `H_le_normalizer` (Step 5) is a single monolithic `sorry`.
  This file **decomposes** it: the corrected (S12/S13) signature reduces — via
  ONE verified Mathlib bearer — to a single isolated subgroup-equality fact.

  Verified closing bearer (exact signature confirmed against the lake pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0,
  `Mathlib/Algebra/Group/Subgroup/Basic.lean:378`):

      theorem Subgroup.le_normalizer_of_normal_subgroupOf
          [hK : (H.subgroupOf K).Normal] (HK : H ≤ K) : K ≤ H.normalizer

  Instantiated with lemma-`H := zpowers σ`, lemma-`K := H`, its hypotheses are
  exactly `zpowers σ ≤ H` (from `σ ∈ H` via `Subgroup.zpowers_le`, confirmed
  `Mathlib/Algebra/Group/Subgroup/ZPowers/Basic.lean:121`) and the instance
  `((zpowers σ).subgroupOf H).Normal`. Its conclusion is exactly Step 5's goal
  `H ≤ (zpowers σ).normalizer`.

  Consequently the ENTIRE Step 5 collapses to producing that one Normal
  instance, and that in turn follows by rewriting along the single residual
  fact

      hPeq : (zpowers σ).subgroupOf H = (P : Subgroup H)

  which transports `P`'s normality (`hPnorm`, the output of Step 2
  `sylow_p_normal`). Everything below `hPeq` is discharged here; `hPeq` is the
  lone remaining `sorry` and is now a clean, isolated target for Aristotle
  `prove` / a Docker build (the S13 cardinality argument: `|ι(P)| = |P| = p`,
  `|zpowers σ| = orderOf σ = p` from `hσ_cycle.orderOf.trans hσ_card`, and
  `ι(P) ⊆ zpowers σ` from `hgen`, upgrading ⊆ to = by equal finite card; then
  `(P.map H.subtype).subgroupOf H = P` by injectivity of `H.subtype`).

  This is a decomposition only — NOT a verified proof. The glue (`zpowers_le`,
  `le_normalizer_of_normal_subgroupOf`, the `rw`) uses three bearers whose
  signatures are confirmed at the pin, but the whole has not been typechecked
  this session (no backend available). 1 sorry intact (down from 1 monolithic;
  the value is the isolation of the residual, not a sorry-count change).
-/
import Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection
import Mathlib.GroupTheory.Sylow

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirection

variable {p : ℕ} [Fact p.Prime]

/-- Step 5, decomposed: with the corrected (S13) sound signature, the embedding
    hypothesis `H ≤ N_{S_p}(⟨σ⟩)` reduces to the single isolated subgroup
    equality `hPeq : (zpowers σ).subgroupOf H = P`. The normalizer-closing half
    is fully discharged here via the verified bearer
    `Subgroup.le_normalizer_of_normal_subgroupOf`. -/
theorem H_le_normalizer_decomposed
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (P : Sylow p H)
    (hPnorm : (P : Subgroup H).Normal)
    (σ : Equiv.Perm (ZMod p))
    (_hσ_cycle : σ.IsCycle)
    (_hσ_card : σ.support.card = p)
    (_hgen : ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
      Subgroup.zpowers σ)
    (hσH : σ ∈ H) :
    H ≤ (Subgroup.zpowers σ).normalizer := by
  -- ⟨σ⟩ ≤ H, from σ ∈ H (verified bearer: Subgroup.zpowers_le, ZPowers/Basic:121)
  have hle : Subgroup.zpowers σ ≤ H := Subgroup.zpowers_le.mpr hσH
  -- Sole residual: the normal Sylow-p P, pulled back to H, is exactly ⟨σ⟩.
  -- S13 plan items 1–4 (cardinality: |ι(P)| = p = orderOf σ, hgen gives ⊆,
  -- equal finite card gives =; then subgroupOf/map cancel by H.subtype inj).
  have hPeq : (Subgroup.zpowers σ).subgroupOf H = (P : Subgroup H) := by
    sorry
  -- Transport P's normality (hPnorm, Step 2 output) along hPeq.
  haveI : ((Subgroup.zpowers σ).subgroupOf H).Normal := by
    rw [hPeq]; exact hPnorm
  -- Close: verified bearer, Subgroup/Basic:378.
  exact Subgroup.le_normalizer_of_normal_subgroupOf hle

end AbelRuffiniGaloisExtensionsOQ06GaloisDirection
