/-
  TURNKEY ORPHAN DRAFT — main theorem assembly for the Galois-direction
  classification `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`.

  The registered file carries `primitive_solvable_subgroup_embeds_AGL1Z` as a
  bare `sorry` (line ~316): every primitive solvable subgroup `H ≤ S_p` embeds
  into `AGL(1, p)`. This companion drafts the **end-to-end composition** of the
  five step lemmas, calling the registered declarations directly (it `import`s
  the registered file). It is an ORPHAN: NOT imported by `Proofs.lean`, so it is
  OUTSIDE the build gate and cannot affect the green registered build. Once a
  build backend is available: build this file; if green, fold the body verbatim
  into the registered `primitive_solvable_subgroup_embeds_AGL1Z`.

  ## Why this is new (researcher-1, S18, 2026-06-16)

  Steps 1–5 each have a discharged or drafted body (Step 5 `H_le_normalizer` is
  Docker-verified; Steps 1/3/4 are `sorry` stubs with bearer-complete plans),
  but the **glue** that wires them into the file-level theorem had never been
  written in Lean. The capstone python cert (`verify_capstone_embedding.py`,
  S12) certified the *mathematics* of the composition end-to-end, but a python
  cert cannot catch a Lean signature-mismatch in the chain. This draft is that
  Lean glue. It bottoms out only in the existing step lemmas — it introduces NO
  new `sorry` of its own — so once Steps 1, 3, 4 are discharged the main theorem
  closes automatically.

  ## The `σ ∈ H` glue gap this resolves

  Step 5 `H_le_normalizer` requires `hσH : σ ∈ H`. Step 3's *original* output
  (`σ.IsCycle ∧ #σ.support = p ∧ ι(P) ⊆ ⟨σ⟩`) does NOT directly provide it:
  recovering `σ ∈ H` from `ι(P) ⊆ ⟨σ⟩` needs `ι(P) = ⟨σ⟩`, i.e. the `|P| = p`
  cardinality argument (~25 LOC, duplicating Steps 3/5 machinery). The clean fix
  — adopted this session — is to strengthen Step 3 to *export* `σ ∈ H` (free in
  its construction, since `σ = ι a` with `ι` landing in `H`). Both the
  registered `sylow_p_is_pcycle` stub and the Step-3 orphan were updated to the
  4-conjunct signature, so the assembly below threads `hσH` straight through.

  ## Status — SOURCE-VERIFIED, BUILD-PENDING

  Authored under DUAL BLACKOUT (re-probed live 2026-06-16: Docker `docker run`
  hangs / git-128 Mathlib re-clone; Aristotle MCP `prove` returns 404). Lemma
  names checked against the lake-pinned Mathlib v4.26.0 source at
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
    ★ `Sylow.nonempty : Nonempty (Sylow p G)`            (Sylow.lean:175)
    ★ `Subgroup.inclusion (h : H ≤ K) : H →* K`          (Defs.lean:585)
    ★ `Subgroup.inclusion_injective (h : H ≤ K)`         (Defs.lean:593)
  Confidence: ? on the final `Function.Injective` line — `hφinj.comp …` proves
  `Injective (⇑φ ∘ ⇑(inclusion h))`, which should be defeq to
  `Injective ⇑(φ.comp (inclusion h))` via `MonoidHom.coe_comp` (rfl); if the
  elaborator balks, wrap with `by simpa [MonoidHom.coe_comp] using …`.
-/
import Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirectionMainAssembly

open AbelRuffiniGaloisExtensionsOQ06
open AbelRuffiniGaloisExtensionsOQ06GaloisDirection

variable {p : ℕ} [Fact p.Prime]

/-- **Main theorem (assembled).** Every primitive solvable subgroup of
    `S_p = Equiv.Perm (ZMod p)` embeds into `AGL(1, p)`.

    Composition `sylow_p_unique → sylow_p_normal → sylow_p_is_pcycle →
    H_le_normalizer → normalizer_iso_AGL1Z`, then `H ↪ N(⟨σ⟩) →* AGL(1,p)`. -/
theorem primitive_solvable_subgroup_embeds_AGL1Z_assembly
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H) :
    ∃ φ : H →* AGL1Z p, Function.Injective φ := by
  -- Pick any Sylow-p subgroup of H (nonempty for a finite group).
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  -- Step 1 + 2: that Sylow-p is unique, hence normal.
  haveI : Subsingleton (Sylow p H) := sylow_p_unique H hPrim hSolv
  have hPnorm : (P : Subgroup H).Normal := sylow_p_normal H hPrim hSolv P
  -- Step 3: a p-cycle σ generating ι(P), and (newly exported) σ ∈ H.
  obtain ⟨σ, hσcyc, hσcard, hgen, hσH⟩ := sylow_p_is_pcycle H hPrim hSolv P
  -- Step 5: H normalises ⟨σ⟩.
  have hHle : H ≤ (Subgroup.zpowers σ).normalizer :=
    H_le_normalizer H P hPnorm σ hσcyc hσcard hgen hσH
  -- Step 4: N(⟨σ⟩) ≅ AGL(1, p); the injective half is all we need.
  obtain ⟨φ, hφinj, _hφsurj⟩ := normalizer_iso_AGL1Z σ hσcyc hσcard
  -- Compose the inclusion H ↪ N(⟨σ⟩) with the isomorphism into AGL(1, p).
  exact ⟨φ.comp (Subgroup.inclusion hHle),
    hφinj.comp (Subgroup.inclusion_injective hHle)⟩

end AbelRuffiniGaloisExtensionsOQ06GaloisDirectionMainAssembly
