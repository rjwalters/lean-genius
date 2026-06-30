/-
  TURNKEY ORPHAN DRAFT — Capstone assembly of the Galois-direction
  classification `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`.

  The registered file's main theorem `primitive_solvable_subgroup_embeds_AGL1Z`
  is still a bare `sorry`. Its docstring states the intended discharge as the
  composition
    `sylow_p_unique → sylow_p_normal → sylow_p_is_pcycle →
     normalizer_iso_AGL1Z → H_le_normalizer`.
  This companion REALISES that composition, demonstrating that the 5-step plan
  actually closes the main goal. It is an ORPHAN (NOT imported by `Proofs.lean`),
  so it cannot affect the registered build. Once a backend is available: build
  this file; if green, fold `primitive_solvable_subgroup_embeds_AGL1Z_capstone`
  into the registered `primitive_solvable_subgroup_embeds_AGL1Z`, and fold
  `sylow_p_is_pcycle_strong` into the registered `sylow_p_is_pcycle` (adding the
  `σ ∈ H` conjunct to its statement — see the integration gap below).

  ## Integration gap discovered & fixed (researcher-1, 2026-06-16)

  The registered `H_le_normalizer` (Step 5, Docker-verified GREEN) requires the
  hypothesis `hσH : σ ∈ H`. But the registered `sylow_p_is_pcycle` (Step 3)
  returns only `σ.IsCycle ∧ σ.support.card = p ∧ (∀ g:P, ι g ∈ ⟨σ⟩)` — it does
  NOT expose `σ ∈ H`, and the witness `σ = ι a` is hidden inside the
  existential, so `σ ∈ H` cannot be recovered from the Step-3 statement alone
  (without re-running Step 5's cardinality argument). The composition in the
  main theorem therefore CANNOT be assembled from the steps as currently stated.

  Fix: strengthen Step 3 to also return `σ ∈ H`. This is free: in Step 3,
  `σ = ι a` where `ι = H.subtype ∘ (P:Subgroup H).subtype`, so
  `σ = ↑((P:Subgroup H).subtype a) ∈ H` by `SetLike.coe_mem`. The strengthened
  statement is `sylow_p_is_pcycle_strong` below; its proof is the source-verified
  Step-3 companion body (S15/S17, researcher-5) with the `σ ∈ H` conjunct added.

  ## Status — SOURCE-VERIFIED, BUILD-PENDING (dual blackout 2026-06-16)

  Authored under DUAL BLACKOUT: Aristotle MCP `prove`/`prove_file` return 404
  ("Resource not found"); host `proofs/.lake` is a self-referential symlink, so
  no local Docker/Mathlib build is possible. All Mathlib lemma names used in the
  capstone were re-checked against the v4.26.0 source mirror at the lake pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
    - `Subgroup.inclusion` / `Subgroup.inclusion_injective`
      (`Algebra/Group/Subgroup/Defs.lean:585,593`)
    - `Sylow.nonempty : Nonempty (Sylow p G)` — needs only `[Group G]`
      (`GroupTheory/Sylow.lean:175`, Zorn-based, NO `[Finite G]`)
    - `MonoidHom.coe_comp` (simp), `Function.Injective.comp`.
  The Step-3 body lemma names are inherited source-verified from the S17 pass on
  the Step-3 companion (see `knowledge.md` §"S17 lemma-name resolution").
-/
import Mathlib
import Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirectionAssembly

open AbelRuffiniGaloisExtensionsOQ06 AbelRuffiniGaloisExtensionsOQ06GaloisDirection

variable {p : ℕ} [Fact p.Prime]

/-- Legendre at the prime `p` itself: `v_p(p!) = 1`. (Source-verified S17;
    copied here so this companion is self-contained.) -/
theorem padicValNat_factorial_self (hp : p.Prime) :
    (Nat.factorial p).factorization p = 1 := by
  have hlog : Nat.log p p < p := Nat.log_lt_self p hp.pos.ne'
  rw [Nat.factorization_factorial hp hlog]
  rw [Finset.sum_eq_single 1]
  · rw [pow_one, Nat.div_self hp.pos]
  · intro i hi hne
    apply Nat.div_eq_of_lt
    have hi2 : 2 ≤ i := by
      rcases Finset.mem_Ico.mp hi with ⟨h1, _⟩; omega
    calc p < p ^ 2 := by nlinarith [hp.two_le]
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos.le hi2
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨le_refl 1, hp.one_lt⟩) h

/-- **Step 3, strengthened (p-cycle structure + `σ ∈ H`).** Identical to the
    registered `sylow_p_is_pcycle` but additionally returns `σ ∈ H`, the
    hypothesis required by Step 5 (`H_le_normalizer`). The body is the
    source-verified S15/S17 Step-3 companion proof; the only addition is the
    final `σ ∈ H` conjunct, discharged by `SetLike.coe_mem` since `σ = ι a` and
    `ι` lands in `H` by construction. -/
theorem sylow_p_is_pcycle_strong
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H)
    (P : Sylow p H) :
    ∃ σ : Equiv.Perm (ZMod p), σ.IsCycle ∧ σ.support.card = p ∧
      (∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
        Subgroup.zpowers σ) ∧ σ ∈ H := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  set ι : (P : Subgroup H) →* Equiv.Perm (ZMod p) :=
    H.subtype.comp (P : Subgroup H).subtype with hιdef
  have hι_inj : Function.Injective ι :=
    (Subgroup.subtype_injective H).comp (Subgroup.subtype_injective _)
  -- Step A:  p ∣ Nat.card H.
  haveI : MulAction.IsPretransitive H (ZMod p) := _hPrim.toIsPretransitive
  have horbit : Nat.card (MulAction.orbit H (0 : ZMod p)) = p := by
    have huniv : MulAction.orbit H (0 : ZMod p) = Set.univ :=
      MulAction.orbit_eq_univ (0 : ZMod p)
    rw [huniv, Nat.card_congr (Equiv.Set.univ (ZMod p)),
        Nat.card_eq_fintype_card, ZMod.card]
  have hpH : p ∣ Nat.card H := by
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      H (0 : ZMod p)
    exact ⟨Nat.card (MulAction.stabilizer H (0 : ZMod p)), by rw [← hos, horbit]⟩
  -- Step B:  Nat.card ↥P = p.
  have hkpos : 0 < (Nat.card H).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpH
  have hpP : p ∣ Nat.card (P : Subgroup H) := by
    rw [P.card_eq_multiplicity]
    exact dvd_pow_self p hkpos.ne'
  have hHdvd : Nat.card H ∣ Nat.card (Equiv.Perm (ZMod p)) :=
    Subgroup.card_subgroup_dvd_card H
  have hcard_perm : Nat.card (Equiv.Perm (ZMod p)) = Nat.factorial p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card]
  have hvpH : (Nat.card H).factorization p ≤ 1 := by
    have hle : (Nat.card H).factorization p
        ≤ (Nat.card (Equiv.Perm (ZMod p))).factorization p :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by rw [hcard_perm]; exact (Nat.factorial_pos p).ne')).2 hHdvd p
    rwa [hcard_perm, padicValNat_factorial_self hp] at hle
  have hcardP : Nat.card (P : Subgroup H) = p := by
    have hk1 : (Nat.card H).factorization p = 1 := le_antisymm hvpH hkpos
    rw [P.card_eq_multiplicity, hk1, pow_one]
  have hcardP_ft : Fintype.card (P : Subgroup H) = p := by
    rw [← Nat.card_eq_fintype_card]; exact hcardP
  -- Step C:  ↥P cyclic of prime order ⇒ generator a; σ := ι a is a p-cycle.
  haveI hcyc : IsCyclic (P : Subgroup H) := isCyclic_of_prime_card hcardP
  obtain ⟨a, ha⟩ := hcyc.exists_generator
  have horda : orderOf a = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hcardP_ft]
  have hords : orderOf (ι a) = p := by
    rw [orderOf_injective ι hι_inj a, horda]
  have hcycσ : (ι a).IsCycle := by
    have hprime : (orderOf (ι a)).Prime := hords ▸ hp
    have hsupp_lt : (ι a).support.card < 2 * orderOf (ι a) := by
      have hle : (ι a).support.card ≤ Fintype.card (ZMod p) :=
        Finset.card_le_univ _
      rw [ZMod.card] at hle
      rw [hords]; omega
    exact Equiv.Perm.isCycle_of_prime_order hprime hsupp_lt
  refine ⟨ι a, hcycσ, ?_, ?_, ?_⟩
  · -- support.card = orderOf = p
    rw [← hcycσ.orderOf, hords]
  · -- ι sends every element of P into ⟨σ⟩
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha g)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow ι a k, hk]⟩
  · -- σ = ι a ∈ H : ι lands in H by construction.
    show (H.subtype.comp (P : Subgroup H).subtype) a ∈ H
    exact SetLike.coe_mem ((P : Subgroup H).subtype a)

/-- **Main theorem (capstone assembly).** Every primitive solvable subgroup
    `H ≤ S_p = Equiv.Perm (ZMod p)` embeds into `AGL(1, p)`.

    This realises the registered file's intended 5-step composition. It is
    conditional only on the still-`sorry` Steps 1 (`sylow_p_unique`, used inside
    `sylow_p_normal`) and 4 (`normalizer_iso_AGL1Z`) of the registered file;
    Steps 2, 3 (strengthened above), and 5 are complete. -/
theorem primitive_solvable_subgroup_embeds_AGL1Z_capstone
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H) :
    ∃ φ : H →* AGL1Z p, Function.Injective φ := by
  -- A Sylow-p subgroup of ↥H exists (Zorn; no finiteness needed).
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p H))
  -- Step 2: P is normal in H.
  have hPnorm : (P : Subgroup H).Normal := sylow_p_normal H hPrim hSolv P
  -- Step 3 (strengthened): P is generated by a p-cycle σ, and σ ∈ H.
  obtain ⟨σ, hcyc, hcard, hgen, hσH⟩ :=
    sylow_p_is_pcycle_strong H hPrim hSolv P
  -- Step 5: H ≤ N_{S_p}(⟨σ⟩).
  have hHN : H ≤ (Subgroup.zpowers σ).normalizer :=
    H_le_normalizer H P hPnorm σ hcyc hcard hgen hσH
  -- Step 4: N_{S_p}(⟨σ⟩) ≅ AGL(1, p); take the injective half.
  obtain ⟨φ, hφinj, _hφsurj⟩ := normalizer_iso_AGL1Z σ hcyc hcard
  -- Compose: H ↪ N(⟨σ⟩) →φ AGL1Z, injective.
  refine ⟨φ.comp (Subgroup.inclusion hHN), ?_⟩
  have hinj : Function.Injective (φ ∘ Subgroup.inclusion hHN) :=
    hφinj.comp (Subgroup.inclusion_injective hHN)
  simpa [MonoidHom.coe_comp] using hinj

end AbelRuffiniGaloisExtensionsOQ06GaloisDirectionAssembly
