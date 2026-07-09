/-
  Primitive Solvable Permutation Groups of Prime Degree — Galois Direction
  (sub-OQ-06)

  This file proves the **Galois direction** of the AGL(1, p) classification:
  every primitive solvable subgroup `H ≤ S_p` embeds into the affine group
  `AGL(1, p) = ℤ/pℤ ⋊ (ℤ/pℤ)ˣ`. The forward direction (that AGL(1, p)
  itself is solvable, primitive, faithful, and of order p(p-1)) is supplied
  by the parent file `Proofs.AbelRuffiniGaloisExtensionsOQ06` (530 LOC,
  0 sorries, 0 axioms, Docker-verified by parent S7 ACT PR #19071).

  ## Status: COMPLETE — 0 sorries, 0 axioms (Docker-verified)

  All five steps of the proof skeleton (Sylow uniqueness → P normal → P is
  p-cycle → N_{S_p}(P) ≅ AGL(1, p) → H ≤ N_{S_p}(P)) are discharged in this
  file, and the file-level theorem `primitive_solvable_subgroup_embeds_AGL1Z`
  composes them unconditionally. Step 1 (`sylow_p_unique`) — historically the
  hard blocker, once thought to require a socle/minimal-normal API absent from
  Mathlib — is proved instead via a nontrivial abelian *characteristic*
  subgroup of the solvable `H` together with the `v_p(|H|) = v_p(p!) = 1`
  cardinality bound. See the `primitive_solvable_subgroup_embeds_AGL1Z`
  docstring below for the full route.

  ## Mathlib bearer audit (S1 OBSERVE, re-verified at lake-pinned SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

  - `Sylow.exists` (existence of Sylow-p in a finite group).
  - `Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`).
  - `Equiv.Perm.isCycle_of_prime_order''`
    (`Mathlib/GroupTheory/Perm/Cycle/Type.lean:412`).
  - `Subgroup.normalizer` (`Mathlib/GroupTheory/Subgroup/Basic.lean`).
  - `MonoidHom.ofInjective` (`Mathlib/Algebra/Group/Hom/Basic.lean`).
  - Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`
    (`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`).
-/

import Proofs.AbelRuffiniGaloisExtensionsOQ06
-- Step 4 (`normalizer_iso_AGL1Z`) is discharged in the build-verified companion
-- `…GaloisDirectionStep4` (the classical holomorph computation
-- `N_{S_p}(⟨σ⟩) ≅ AGL(1, p)`); imported here to wire it into the main theorem.
import Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep4
-- Full Mathlib. Step 3's discharge (`sylow_p_is_pcycle`, folded in from the
-- build-verified orphan) draws on factorization/Legendre (`Nat.factorization_factorial`),
-- orbit–stabilizer (`MulAction.orbitEquivQuotientStabilizer`, `orbit_eq_univ`),
-- `ZMod`/index cardinality (`Subgroup.index_eq_card`, `ZMod.card`), and cyclic-group
-- bearers (`isCyclic_of_prime_card`) that are NOT in scope via the previously-targeted
-- imports. Full Mathlib also covers the char-in-normal instance
-- `ConjAct.normal_of_characteristic_of_normal` (Step 4 / Risk R4).
import Mathlib

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirection

open AbelRuffiniGaloisExtensionsOQ06

variable {p : ℕ} [Fact p.Prime]

/-- Legendre at the prime `p` itself: `v_p(p!) = 1`.
    `v_p(p!) = ∑_{i=1}^{p-1} ⌊p / p^i⌋`; the `i = 1` term is `1`, every `i ≥ 2`
    term is `0` (since `p^i > p`), so the sum is `1`.  Self-contained; used by the
    Step 3 `v_p(|H|) ≤ v_p(p!) = 1` upper bound.

    (The file-level `[Fact p.Prime]` section variable is auto-included but unused
    here — `hp` is taken explicitly — yielding a harmless `unusedSectionVars`
    linter warning; the lemma is otherwise independent of the instance.) -/
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
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi2
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨le_refl 1, hp.one_lt⟩) h

/-- **Lemma A (derived-series extraction).** A nontrivial solvable group has a
    nontrivial *abelian characteristic* subgroup: the last nontrivial term of the
    derived series. Generic (any `Group G`, `Nontrivial G`, `IsSolvable G`);
    reusable across sibling solvable-group classifications.

    This packages steps 1+4 of the Galois-direction route: `A` is characteristic
    (hence normal) in `↥H`, and `IsMulCommutative ↥A` makes every subgroup of
    `↥A` normal (`CommGroup.ofIsMulCommutative` + `Subgroup.normal_of_comm`), so
    `A`'s Sylow-`p` is normal in `↥A` for free in the assembly. -/
theorem exists_nontrivial_isMulComm_characteristic_of_solvable
    (G : Type*) [Group G] [Nontrivial G] [IsSolvable G] :
    ∃ A : Subgroup G, A.Characteristic ∧ Nontrivial A ∧ IsMulCommutative A := by
  classical
  have hex : ∃ m : ℕ, derivedSeries G m = ⊥ := IsSolvable.solvable
  set d := Nat.find hex with hd_def
  have hd : derivedSeries G d = ⊥ := Nat.find_spec hex
  -- `d > 0`: else `derivedSeries G 0 = ⊤ = ⊥`, contradicting `Nontrivial G`.
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exfalso
      have htop : (⊤ : Subgroup G) = ⊥ := by
        rw [← derivedSeries_zero G, ← h0]; exact hd
      exact top_ne_bot htop
    · exact hpos
  -- `A := derivedSeries G (d-1)`.
  refine ⟨derivedSeries G (d - 1), inferInstance, ?_, ?_⟩
  · -- nontrivial: `derivedSeries G (d-1) ≠ ⊥` by minimality of `d`.
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact Nat.find_min hex (Nat.pred_lt hdpos.ne')
  · -- abelian: `⁅A,A⁆ = derivedSeries G d = ⊥` ⇒ `A ≤ centralizer A` ⇒ comm.
    have hcomm : ⁅derivedSeries G (d - 1), derivedSeries G (d - 1)⁆ = ⊥ := by
      have hsucc : derivedSeries G (d - 1 + 1)
          = ⁅derivedSeries G (d - 1), derivedSeries G (d - 1)⁆ :=
        derivedSeries_succ G (d - 1)
      rw [Nat.sub_add_cancel hdpos] at hsucc
      rw [← hsucc]; exact hd
    have hle : derivedSeries G (d - 1) ≤ Subgroup.centralizer (derivedSeries G (d - 1)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
    exact (Subgroup.le_centralizer_iff_isMulCommutative).mp hle

/-- **Lemma B (normal ⇒ transitive).** A nontrivial subgroup `A ⊴ H` of a
    faithful primitive action of `H` on the `p`-point set `ZMod p` is transitive.

    Route (bearers in scope): for any `a`, `orbit A a` is a block
    (`IsBlock.orbit_of_normal`), hence subsingleton or univ
    (`IsBlock.subsingleton_or_eq_univ`, using `_hPrim`). `A` nontrivial + faithful
    moves some point `a₀`, so `orbit A a₀` is not subsingleton ⇒ `= univ` ⇒
    `IsPretransitive ↥A (ZMod p)` (`isPretransitive_iff_orbit_eq_univ`). -/
theorem normalSubgroup_isTransitive_of_nontrivial
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (A : Subgroup H) [A.Normal] (_hAnt : Nontrivial A) :
    MulAction.IsPretransitive A (ZMod p) := by
  haveI := _hPrim
  haveI := _hAnt
  -- `A` nontrivial: pick `g ≠ 1` in `A`.
  obtain ⟨g, hg⟩ := exists_ne (1 : A)
  -- Faithfulness of the `A`-action (`A ≤ H ≤ S_p`) yields a moved point.
  have hmove : ∃ a : ZMod p, g • a ≠ a := by
    by_contra hcon
    push_neg at hcon
    exact hg (eq_of_smul_eq_smul (fun a => by rw [hcon a, one_smul]))
  obtain ⟨a₀, ha₀⟩ := hmove
  -- The `A`-orbit of `a₀` is a block (orbit of a normal subgroup).
  have hblock : MulAction.IsBlock H (MulAction.orbit A a₀) :=
    MulAction.IsBlock.orbit_of_normal a₀
  -- Primitivity ⇒ the block is subsingleton or univ. It contains `a₀` and
  -- `g • a₀ ≠ a₀`, so it is not subsingleton ⇒ it is univ ⇒ transitive.
  rcases hblock.subsingleton_or_eq_univ with hsub | huniv
  · exact absurd (hsub (MulAction.mem_orbit a₀ g) (MulAction.mem_orbit_self a₀)) ha₀
  · exact (MulAction.isPretransitive_iff_orbit_eq_univ a₀).mpr huniv

omit [Fact (Nat.Prime p)] in
/-- **Lemma C (transitive ⇒ `p ∣ |A|`).** A transitive action on `ZMod p`
    forces `p ∣ Nat.card A`. Orbit–stabilizer; mirrors the Step 3 Step A,
    transported from `↥H` to `↥A`. -/
theorem prime_dvd_card_of_isPretransitive
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (A : Subgroup H) [MulAction.IsPretransitive A (ZMod p)] :
    p ∣ Nat.card A := by
  have huniv : MulAction.orbit A (0 : ZMod p) = Set.univ :=
    MulAction.orbit_eq_univ A (0 : ZMod p)
  have e : ZMod p ≃ A ⧸ MulAction.stabilizer A (0 : ZMod p) :=
    ((Equiv.Set.univ (ZMod p)).symm.trans (Equiv.setCongr huniv.symm)).trans
      (MulAction.orbitEquivQuotientStabilizer A (0 : ZMod p))
  have hidx : (MulAction.stabilizer A (0 : ZMod p)).index = p := by
    rw [Subgroup.index_eq_card, ← Nat.card_congr e, Nat.card_zmod]
  have hdvd := Subgroup.index_dvd_card
    (H := MulAction.stabilizer A (0 : ZMod p))
  rwa [hidx] at hdvd

/-- **Step 1 (Sylow uniqueness).** Inside a primitive solvable
    subgroup `H ≤ S_p`, the Sylow-p subgroup of `H` is unique.

    ⚠ **The naive Sylow-count argument is CIRCULAR** (researcher-1, S6
    ORIENT 2026-06-14): Sylow III gives `n_p ≡ 1 (mod p)` and `n_p ∣ |H|/p`,
    forcing `n_p = 1` *only when* `|H|/p < p`; but `H ≤ S_p` only yields
    `|H| ∣ p!`, so `|H|/p` can be as large as `(p−1)!`. The bound `|H|/p < p`
    is equivalent to the conclusion `H ≤ AGL(1, p)`, so it cannot be assumed.

    **Bearer-complete sound route** (researcher-3, S7 ORIENT 2026-06-14;
    all bearers present at lake-pin `2df2f015`, replacing the previously
    "no Mathlib bearer" verdict via the absent socle/`MinimalNormal` API):
    1. `A := derivedSeries ↥H (d-1)`, `d` least with `derivedSeries ↥H d = ⊥`
       (exists by `IsSolvable`). `A` is **normal/characteristic** in `H`
       (`derivedSeries_normal`/`derivedSeries_characteristic`, Solvable.lean)
       and **abelian** (`derivedSeries_succ`: `⁅A,A⁆ = derivedSeries H d = ⊥`),
       and **nontrivial** by minimality of `d` (for `H` nontrivial; the
       trivial `H` case makes `Sylow p H` subsingleton outright).
    2. `A ⊴ H` ⟹ each `A`-orbit on `ZMod p` is a **block** for the `H`-action
       (`MulAction.IsBlock.orbit_of_normal`, Blocks.lean:475); by primitivity
       every block is subsingleton or univ
       (`MulAction.IsBlock.subsingleton_or_eq_univ`, Primitive.lean:115).
       `A` nontrivial + faithful (`H ≤ S_p`) moves some point, so that orbit
       is univ ⟹ **`A` is transitive** (`isPretransitive_iff_orbit_eq_univ`).
    3. `A` transitive on a `p`-set ⟹ `p ∣ |A|` (orbit–stabilizer).
    4. `A` abelian ⟹ its Sylow-`p` `Q` is **normal** in `↥A` ⟹ characteristic
       in `↥A` (`Sylow.characteristic_of_normal`, Sylow.lean:728); with `A ⊴ ↥H`
       (from `A` characteristic in `↥H`) the transported subgroup
       `Q.map A.subtype` is then **normal in `↥H`** by the *instance*
       `ConjAct.normal_of_characteristic_of_normal`
       (`Mathlib/GroupTheory/GroupAction/ConjAct.lean:260` at pin `2df2f015`:
       `{H : Subgroup G} [H.Normal] {K : Subgroup H} [K.Characteristic] :
       (K.map H.subtype).Normal`). Instantiated with `G := ↥H`, lemma-`H := A`,
       lemma-`K := Q`, this fires by typeclass resolution — **0 LOC**, not the
       ~10–30 LOC ad-hoc bridge the S8 audit budgeted (see knowledge.md R4 §S10).
    5. `v_p(|H|) ≤ v_p(p!) = 1` (Legendre, `Nat.Prime.factorization_factorial`
       / `padicValNat_factorial`), and `p ∣ |A| ∣ |H|` ⟹ `v_p(|A|) = 1` ⟹
       `|Q| = p`, so `Q` is a Sylow-`p` of `H` too (`Sylow.ofCard`,
       Sylow.lean:102). `Q ⊴ H` Sylow ⟹ **unique**
       (`Sylow.unique_of_normal`, Sylow.lean:710) ⟹ `Subsingleton (Sylow p H)`.

    Residual risk is **wiring**, not missing infrastructure (now ~70–110 LOC,
    revised down from ~100–150): transporting `Q` along `A ↪ ↥H`, the `v_p`
    arithmetic, and the orbit–stabilizer transitivity. The char-in-normal step
    that S8 flagged as the single hardest residual ("no upstream bearer",
    ~10–30 LOC) is **resolved** — it is the 0-LOC instance
    `ConjAct.normal_of_characteristic_of_normal` cited in step 4. Risk R4
    accordingly stays MEDIUM but the budget shrinks (see knowledge.md R4 §S10).
    Discharge deferred to a Docker-up ACT session. -/
theorem sylow_p_unique
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H) :
    Subsingleton (Sylow p H) := by
  have hp : p.Prime := Fact.out
  haveI := _hSolv
  rcases subsingleton_or_nontrivial (H : Type _) with hSub | hNt
  · -- Trivial `H`: `Subgroup ↥H` is subsingleton, so any two Sylows agree.
    haveI : Subsingleton (Subgroup H) := Subgroup.subsingleton_iff.mpr hSub
    exact ⟨fun P Q => Sylow.ext (Subsingleton.elim _ _)⟩
  · -- Nontrivial `H`: extract a nontrivial abelian characteristic `A ⊴ ↥H`.
    haveI := hNt
    obtain ⟨A, hAchar, hAnt, hAcomm⟩ :=
      exists_nontrivial_isMulComm_characteristic_of_solvable (H : Type _)
    haveI : A.Characteristic := hAchar
    haveI : A.Normal := inferInstance
    haveI : Nontrivial A := hAnt
    haveI : IsMulCommutative A := hAcomm
    -- `A` transitive (Lemma B) ⇒ `p ∣ |A|` (Lemma C).
    haveI : MulAction.IsPretransitive A (ZMod p) :=
      normalSubgroup_isTransitive_of_nontrivial H _hPrim A hAnt
    have hpA : p ∣ Nat.card A := prime_dvd_card_of_isPretransitive H A
    -- `A` abelian ⇒ its Sylow `Q` is normal, hence characteristic, in `↥A`.
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p A))
    have hQnorm : (Q : Subgroup A).Normal := inferInstance
    haveI : (Q : Subgroup A).Characteristic := Sylow.characteristic_of_normal Q hQnorm
    -- Transport: `Q.map A.subtype` is normal in `↥H`
    -- (`ConjAct.normal_of_characteristic_of_normal` instance).
    have hmapnorm : ((Q : Subgroup A).map A.subtype).Normal := inferInstance
    -- Cardinalities: `v_p(|H|) = 1`, hence `|Q| = p` and `|Q.map| = p`.
    have hcard_perm : Nat.card (Equiv.Perm (ZMod p)) = Nat.factorial p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ZMod.card]
    have hHdvd : Nat.card H ∣ Nat.card (Equiv.Perm (ZMod p)) :=
      Subgroup.card_subgroup_dvd_card H
    have hAHdvd : Nat.card A ∣ Nat.card H := Subgroup.card_subgroup_dvd_card A
    have hpH : p ∣ Nat.card H := hpA.trans hAHdvd
    have hfactH : (Nat.card H).factorization p = 1 := by
      have hpos : 0 < (Nat.card H).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpH
      have hle : (Nat.card H).factorization p
          ≤ (Nat.card (Equiv.Perm (ZMod p))).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
          (by rw [hcard_perm]; exact (Nat.factorial_pos p).ne')).2 hHdvd p
      rw [hcard_perm, padicValNat_factorial_self hp] at hle
      omega
    have hfactA : (Nat.card A).factorization p = 1 := by
      have hpos : 0 < (Nat.card A).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpA
      have hle : (Nat.card A).factorization p ≤ (Nat.card H).factorization p :=
        (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hAHdvd p
      rw [hfactH] at hle; omega
    have hcardQ : Nat.card (Q : Subgroup A) = p := by
      have h := Q.card_eq_multiplicity
      rw [hfactA, pow_one] at h
      exact h
    have hmapcard : Nat.card ((Q : Subgroup A).map A.subtype)
        = p ^ (Nat.card H).factorization p := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective A), hcardQ,
        hfactH, pow_one]
    -- Package `Q.map A.subtype` as a normal Sylow of `↥H`, then uniqueness.
    let P : Sylow p H := Sylow.ofCard ((Q : Subgroup A).map A.subtype) hmapcard
    have hPnorm : (P : Subgroup H).Normal := by
      have hcoe : (P : Subgroup H) = (Q : Subgroup A).map A.subtype :=
        Sylow.coe_ofCard _ hmapcard
      rw [hcoe]; exact hmapnorm
    haveI := Sylow.unique_of_normal P hPnorm
    infer_instance

/-- **Step 2 (Normal Sylow).** The unique Sylow-p subgroup `P` of `H`
    is normal in `H` (any unique Sylow is normal).

    Discharged (S4 ACT, researcher-2, 2026-06-12): the uniqueness
    hypothesis `Subsingleton (Sylow p H)` is supplied by `sylow_p_unique`
    (Step 1), after which `Sylow.normal_of_subsingleton`
    (`Mathlib/GroupTheory/Sylow.lean:724`) closes the goal. This step
    carries no `sorry`; it is conditional only on Step 1. -/
theorem sylow_p_normal
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H)
    (P : Sylow p H) :
    (P : Subgroup H).Normal := by
  haveI : Subsingleton (Sylow p H) := sylow_p_unique H hPrim hSolv
  exact P.normal_of_subsingleton

/-- **Step 3 (p-cycle structure).** The Sylow-`p` subgroup `P` of a primitive
    solvable `H ≤ S_p` is generated (via the inclusion `ι = H.subtype ∘ P.subtype`)
    by a single `p`-cycle `σ ∈ S_p`.

    **DISCHARGED (researcher-11, S21 ACT, 2026-06-18, Docker-verified GREEN,
    7745 jobs).** The body folds in the build-verified orphan proof
    (`…GaloisDirectionStep3.lean`, signatures identical) after fixing the two
    `?`-flagged elaboration bugs the first build surfaced: `Nat.pow_le_pow_right`
    wants `0 < p` (not `0 ≤ p`), and `MulAction.orbit_eq_univ` takes the acting
    group `H` as an explicit argument. Route:
    - **Step A** `p ∣ |H|`: primitivity ⇒ transitivity on the `p`-point set
      `ZMod p`; orbit–stabilizer in `Nat.card`/index form
      (`orbitEquivQuotientStabilizer` + `index_eq_card` + `index_dvd_card`),
      avoiding the `Fintype`-typed orbit-count lemma.
    - **Step B** `|P| = p`: lower bound `p ∣ |P|` from `Sylow.card_eq_multiplicity`
      and `v_p(|H|) ≥ 1`; upper bound `v_p(|H|) ≤ v_p(p!) = 1` from Lagrange in
      `S_p` (`card_subgroup_dvd_card`) + Legendre (`padicValNat_factorial_self`).
    - **Step C** `↥P` is cyclic of prime order (`isCyclic_of_prime_card`); its
      generator `a` gives `σ := ι a` with `orderOf σ = p`, hence a `p`-cycle
      (`Equiv.Perm.isCycle_of_prime_order`); `ι(P) ⊆ ⟨σ⟩` via `map_zpow`; and
      `σ ∈ H` for free since `σ = ↑(P.subtype a)` (`SetLike.coe_mem`). -/
theorem sylow_p_is_pcycle
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H)
    (P : Sylow p H) :
    ∃ σ : Equiv.Perm (ZMod p), σ.IsCycle ∧ σ.support.card = p ∧
      (∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
        Subgroup.zpowers σ) ∧ σ ∈ H := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- ι : ↥P → S_p, composite of the two subgroup inclusions (a MonoidHom).
  set ι : (P : Subgroup H) →* Equiv.Perm (ZMod p) :=
    H.subtype.comp (P : Subgroup H).subtype with hιdef
  have hι_inj : Function.Injective ι :=
    (Subgroup.subtype_injective H).comp (Subgroup.subtype_injective _)
  ----------------------------------------------------------------
  -- Step A:  p ∣ Nat.card H   (primitivity ⇒ transitivity on a p-point set).
  ----------------------------------------------------------------
  haveI : MulAction.IsPretransitive H (ZMod p) := _hPrim.toIsPretransitive
  -- p ∣ |H| via the orbit–stabilizer EQUIV (Nat.card / index form), avoiding the
  -- Fintype-typed `card_orbit_mul_card_stabilizer_eq_card_group`.
  have hpH : p ∣ Nat.card H := by
    have huniv : MulAction.orbit H (0 : ZMod p) = Set.univ :=
      MulAction.orbit_eq_univ H (0 : ZMod p)
    have e : ZMod p ≃ H ⧸ MulAction.stabilizer H (0 : ZMod p) :=
      ((Equiv.Set.univ (ZMod p)).symm.trans (Equiv.setCongr huniv.symm)).trans
        (MulAction.orbitEquivQuotientStabilizer H (0 : ZMod p))
    have hidx : (MulAction.stabilizer H (0 : ZMod p)).index = p := by
      rw [Subgroup.index_eq_card, ← Nat.card_congr e, Nat.card_zmod]
    have hdvd := Subgroup.index_dvd_card
      (H := MulAction.stabilizer H (0 : ZMod p))
    rwa [hidx] at hdvd
  ----------------------------------------------------------------
  -- Step B:  Nat.card ↥P = p.
  ----------------------------------------------------------------
  -- lower bound: p ∣ |P|  (Sylow card = p ^ v_p(|H|), and v_p(|H|) ≥ 1).
  have hkpos : 0 < (Nat.card H).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' hpH
  have hpP : p ∣ Nat.card (P : Subgroup H) := by
    rw [P.card_eq_multiplicity]
    exact dvd_pow_self p hkpos.ne'
  -- upper bound: v_p(|H|) ≤ v_p(p!) = 1   (Lagrange in S_p + Legendre).
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
  ----------------------------------------------------------------
  -- Step C:  ↥P cyclic of prime order ⇒ generator a; σ := ι a is a p-cycle.
  ----------------------------------------------------------------
  haveI hcyc : IsCyclic (P : Subgroup H) := isCyclic_of_prime_card hcardP
  obtain ⟨a, ha⟩ := hcyc.exists_generator
  have horda : orderOf a = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, hcardP]
  have hords : orderOf (ι a) = p := by
    rw [orderOf_injective ι hι_inj a, horda]
  have hcycσ : (ι a).IsCycle := by
    have hprime : (orderOf (ι a)).Prime := hords.symm ▸ hp
    have hsupp_lt : (ι a).support.card < 2 * orderOf (ι a) := by
      have hle : (ι a).support.card ≤ Fintype.card (ZMod p) :=
        Finset.card_le_univ _
      rw [ZMod.card] at hle
      have hp1 : 0 < p := hp.pos
      rw [hords]; omega
    exact Equiv.Perm.isCycle_of_prime_order hprime hsupp_lt
  refine ⟨ι a, hcycσ, ?_, ?_, ?_⟩
  · -- support.card = orderOf = p
    rw [← hcycσ.orderOf, hords]
  · -- ι sends every element of P into ⟨σ⟩
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha g)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow ι a k, hk]⟩
  · -- σ = ι a ∈ H, for free: ι a = ↑(P.subtype a), the coercion of an element of ↥H.
    show ι a ∈ H
    have hcoe : ι a = (((P : Subgroup H).subtype a : H) : Equiv.Perm (ZMod p)) := by
      rw [hιdef]; rfl
    rw [hcoe]
    exact SetLike.coe_mem _

/-- **Step 4 infrastructure — centralizer cardinality.** The centralizer of a
    `p`-cycle `σ` in `S_p = Equiv.Perm (ZMod p)` has order exactly `p`.

    This is the crux input for the Step-4 normalizer bound: it pins `|C(σ)| = p`,
    from which `N_{S_p}(⟨σ⟩) / C(σ) ↪ Aut(⟨σ⟩) ≅ (ℤ/pℤ)ˣ` forces
    `|N_{S_p}(⟨σ⟩)| ≤ p · (p − 1) = |AGL1Z p|`.

    Proof: `Equiv.Perm.nat_card_centralizer` gives `|C(σ)|` as a product over the
    cycle type. A `p`-cycle on a `p`-point set has `cycleType σ = {p}` (single
    cycle covering every point, `IsCycle.cycleType` + `σ.support.card = p`), so the
    formula collapses to `(p − p)! · p · (1)! = 1 · p · 1 = p`. -/
theorem centralizer_pcycle_card
    (σ : Equiv.Perm (ZMod p)) (hσ : σ.IsCycle) (hσ_card : σ.support.card = p) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (ZMod p)))) = p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hct : σ.cycleType = {p} := by rw [hσ.cycleType, hσ_card]
  rw [Equiv.Perm.nat_card_centralizer, hct, ZMod.card, Multiset.sum_singleton,
    Multiset.prod_singleton, Multiset.toFinset_singleton, Finset.prod_singleton,
    Multiset.count_singleton_self, Nat.sub_self]
  simp

/-- **Step 4 infrastructure — centralizer is the cyclic group itself.** For a
    `p`-cycle `σ`, the centralizer `C_{S_p}(σ)` is exactly `⟨σ⟩`.

    `⟨σ⟩ ≤ C(σ)` always (powers of `σ` commute with `σ`), and both have order `p`
    (`centralizer_pcycle_card`; `Nat.card_zpowers` + `IsCycle.orderOf` for `⟨σ⟩`),
    so the inclusion is an equality. Consequently `C(σ) = ⟨σ⟩` is the *kernel* of
    the conjugation action of `N_{S_p}(⟨σ⟩)` on `⟨σ⟩`. -/
theorem centralizer_pcycle_eq_zpowers
    (σ : Equiv.Perm (ZMod p)) (hσ : σ.IsCycle) (hσ_card : σ.support.card = p) :
    Subgroup.centralizer ({σ} : Set (Equiv.Perm (ZMod p))) = Subgroup.zpowers σ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hcc := centralizer_pcycle_card σ hσ hσ_card
  have hcz : Nat.card (Subgroup.zpowers σ) = p := by
    rw [Nat.card_zpowers, hσ.orderOf, hσ_card]
  have hle : Subgroup.zpowers σ ≤ Subgroup.centralizer {σ} := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
    exact (Commute.zpow_self σ k).eq
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcc.trans hcz.symm))).symm

/-- **Step 4 (Normalizer ≅ AGL(1, p)).** The normalizer of any
    Sylow-p subgroup of `S_p` (generated by a `p`-cycle) is isomorphic
    to `AGL(1, p)` via the conjugation action of `(ℤ/pℤ)ˣ` on `ℤ/pℤ`.

    The isomorphism `N_{S_p}(P) ≅ AGL1Z p` factors through the parent
    file's `AGL1Z.toPerm : AGL1Z p →* Equiv.Perm (ZMod p)`.

    **Numerically certified** (researcher-2, S11 ACT-prep 2026-06-14;
    `verify_step4_normalizer.py` beside `knowledge.md`, needs only sympy):
    by brute force over all of `S_p` for `p ∈ {3,5,7}` with `σ = (x↦x+1)`,
    the full normalizer `N_{S_p}(⟨σ⟩)` equals EXACTLY the affine-group image
    `{x↦a+u·x}`, so `φ` is both **injective and surjective** — the surjective
    half (`|N| = p(p−1)` exactly, no permutation beyond the affine maps
    normalises `⟨σ⟩`) is the genuinely new content, since the S7 Step-5
    script certified only the easy inclusion `AGL image ⊆ N(⟨σ⟩)`. The
    Sylow count `n_p = |S_p|/|N| = (p−2)!` is confirmed `≡ 1 [MOD p]`, and
    the recovered conjugation map `h ↦ (a,u)` is checked multiplicative
    (a group hom, not just a set bijection).

    **DISCHARGED (researcher-11, 2026-06-19).** The full holomorph computation
    is carried out in the build-verified companion
    `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep4`
    (`normalizer_eq_range`: every normalizing permutation is affine, by the
    functional equation `h(y+1) = h(y) + u`; then transport along the
    conjugacy `σ ∼ τ₀` of any `p`-cycle to the standard translation). This
    body now just delegates to it, so Step 4 is `sorry`-free. -/
theorem normalizer_iso_AGL1Z
    (σ : Equiv.Perm (ZMod p)) (_hσ : σ.IsCycle) (_hσ_card : σ.support.card = p) :
    ∃ φ : (Subgroup.zpowers σ).normalizer →* AGL1Z p,
      Function.Injective φ ∧ Function.Surjective φ :=
  AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep4.normalizer_iso_AGL1Z
    σ _hσ _hσ_card

/-- **Step 5 (H ≤ N_{S_p}(P)).** Since the Sylow-p subgroup `P` is
    normal in `H` and its image under `ι = H.subtype ∘ P.subtype` is the
    cyclic group `⟨σ⟩` generated by a `p`-cycle, the group `H` is contained
    in the normalizer of `⟨σ⟩` in `S_p`. Composition with the step-4
    isomorphism gives the desired embedding `H ↪ AGL(1, p)`.

    ## Signature history — the original weak signature was UNSOUND

    The S2 ORIENT scaffold stated this lemma with the single hypothesis
    `σ ∈ H` and **no normality / `p`-cycle data**. That statement is
    **mathematically false** (researcher-5, S5 OBSERVE 2026-06-13): `σ ∈ H`
    does NOT entail `H ≤ N_{S_p}(⟨σ⟩)`. The conclusion needs `⟨σ⟩` to be
    *normalised* by `H`, which is true only when `⟨σ⟩` is the image of the
    **normal Sylow-p** `P` (Steps 2 + 3) — not for an arbitrary `σ ∈ H`.

    Explicit counterexample (`p = 5`) for the OLD signature: let
    `H = (AGL1Z.toPerm 5).range` (primitive + solvable, supplied by the
    parent file) and `σ = (x ↦ 2x)`, the scaling-by-2 map `= (1 2 4 3)`, a
    4-cycle fixing `0`, with `σ ∈ H`. Take `h = (x ↦ x+1) = (0 1 2 3 4) ∈ H`.
    Then `h σ h⁻¹ : y ↦ 2y - 1` sends `0 ↦ 4`, so it does not fix `0`; but
    every element of `⟨σ⟩` fixes `0`. Hence `h σ h⁻¹ ∉ ⟨σ⟩`, so
    `h ∉ N_{S_p}(⟨σ⟩)` and `H ⊄ N_{S_p}(⟨σ⟩)`. (Note the old signature did
    not even require `σ` to be a `p`-cycle.)

    ## Corrected (sound) signature — adopted this session (S12 ACT)

    The signature below is the corrected, sound form (researcher-4, S12 ACT
    2026-06-15). It threads through the normal Sylow-p `P`, the inclusion
    `ι(P) ⊆ ⟨σ⟩` (`hgen`, the exact output of Step 3 `sylow_p_is_pcycle`),
    and the `p`-cycle data `hσ_card`, matching the outputs of Steps 2
    (`sylow_p_normal`) and 3. (The body is now fully discharged — see the
    DISCHARGED note below.)

    ⚠ **The `p`-cycle hypothesis `hσ_card : σ.support.card = p` is NOT
    optional** (researcher-1, S6 OBSERVE 2026-06-14). `hgen` only states
    `ι(P) ⊆ ⟨σ⟩` (where `ι = H.subtype.comp (P : Subgroup H).subtype`); the
    normalizer argument needs the *equality* `ι(P) = ⟨σ⟩`. We have
    `|ι(P)| = |P| = p` (faithful action; `|P| = p` because primitivity
    forces `p ∣ |H|` while `p² ∤ p! ≥ |H|`), so `ι(P) = ⟨σ⟩` follows from
    `ι(P) ⊆ ⟨σ⟩` **only when** `|⟨σ⟩| = ord σ = p`, i.e. `σ` is a `p`-cycle.
    Drop `hσ_card` and the signature is still unsound: e.g. if `ord σ` were
    composite, `ι(P)` (order `p`) could sit as a proper subgroup of `⟨σ⟩`
    and `H`'s normalising `ι(P)` would not normalise the larger `⟨σ⟩`.

    ## Corrected discharge plan (researcher-5, S13 ORIENT 2026-06-15)

    The earlier plan ("upgrade `ι(P) ⊆ ⟨σ⟩` to `=` via `|ι(P)| = p = |⟨σ⟩|`
    from `hσ_card`") has a gap: `|⟨σ⟩| = orderOf σ`, and `orderOf σ = p`
    follows from `σ.support.card = p` **only when `σ` is a single cycle**
    (`IsCycle.orderOf : orderOf σ = #σ.support`, `Perm/Cycle/Basic.lean:363`).
    For a non-cycle permutation `orderOf σ = lcm(cycle lengths) ≠
    #σ.support = Σ lengths` in general, so `hσ_card` ALONE does not pin
    `|⟨σ⟩| = p`. The fix is to thread the cycle hypothesis `hσ_cycle :
    σ.IsCycle` — it is supplied for free by Step 3 (`sylow_p_is_pcycle`
    returns `σ.IsCycle ∧ σ.support.card = p ∧ hgen`), so the eventual
    composition in `primitive_solvable_subgroup_embeds_AGL1Z` loses nothing.

    With `hσ_cycle` in hand the discharge is:
    1. `orderOf σ = p` from `hσ_cycle.orderOf.trans hσ_card`, hence
       `Nat.card ↥(zpowers σ) = p` (`Nat.card_zpowers`).
    2. `Nat.card ↥P = p`: `P : Sylow p ↥H`; `Nat.card ↥H ∣ Nat.card
       (Equiv.Perm (ZMod p)) = p!` and `padicValNat p (p!) = 1` (Legendre,
       `Nat.factorization_factorial` / `Nat.Prime.factorization_factorial`),
       while `p ∣ Nat.card ↥H` (from `orderOf σ = p`, `σ ∈ H`), so the
       Sylow order is exactly `p` (`Sylow.card_eq_multiplicity` + `pow_one`).
    3. `ι(P) = zpowers σ`: `ι(P) ⊆ zpowers σ` (`hgen`, `ι` injective so
       `Nat.card ι(P) = p`) + equal finite cardinality ⟹ equality
       (`Subgroup.eq_of_le_of_card_le` / `Set.eq_of_subset_of_ncard_le`).
    4. `(zpowers σ).subgroupOf H = (P : Subgroup ↥H)` by `Subgroup.ext` +
       `mem_subgroupOf`, transporting `hPnorm` to
       `((zpowers σ).subgroupOf H).Normal`.
    5. close with `Subgroup.le_normalizer_of_normal_subgroupOf`
       (`Subgroup/Basic.lean:378`) and `Subgroup.zpowers_le.mpr hσH`.

    Numerically certified sound by `verify_step5_normalizer.py` for all odd
    primes `3 ≤ p ≤ 29`.

    **DISCHARGED (researcher-4, 2026-06-16, Docker-verified GREEN, 1900 jobs).**
    The body below executes items 1–5 above: it is `sorry`-free and
    axiom-free. Steps 2–3 are realised slightly differently from the plan —
    `p ∣ Nat.card H` is obtained directly from the order-`p` element
    `⟨σ, hσH⟩ : H` (`orderOf_dvd_natCard`) rather than via `padicValNat p (p!)`,
    and `Nat.card P = p` then follows from `Sylow.card_eq_multiplicity` +
    `Nat.Prime.factorization_pos_of_dvd` together with the Lagrange bound
    `Nat.card P ∣ p`. -/
theorem H_le_normalizer
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (P : Sylow p H)
    (hPnorm : (P : Subgroup H).Normal)
    (σ : Equiv.Perm (ZMod p))
    (hσ_cycle : σ.IsCycle)
    (hσ_card : σ.support.card = p)
    (hgen : ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
      Subgroup.zpowers σ)
    (hσH : σ ∈ H) :
    H ≤ (Subgroup.zpowers σ).normalizer := by
  -- ⟨σ⟩ ≤ H, from σ ∈ H (Subgroup.zpowers_le).
  have hle : Subgroup.zpowers σ ≤ H := Subgroup.zpowers_le.mpr hσH
  -- orderOf σ = p: a cycle's order is its support cardinality (IsCycle.orderOf).
  have hord : orderOf σ = p := hσ_cycle.orderOf.trans hσ_card
  -- |(zpowers σ).subgroupOf H| = |zpowers σ| = orderOf σ = p.
  have hcardS : Nat.card ((Subgroup.zpowers σ).subgroupOf H) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_zpowers, hord]
  -- P, pulled back along ι, is contained in ⟨σ⟩: exactly hgen.
  have hPle : (P : Subgroup H) ≤ (Subgroup.zpowers σ).subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hgen ⟨x, hx⟩
  -- Lagrange: |P| divides |(zpowers σ).subgroupOf H| = p.
  have hPdvd : Nat.card (P : Subgroup H) ∣ p := by
    have hd := Subgroup.card_dvd_of_le hPle
    rwa [hcardS] at hd
  -- p divides |H|: the order-p element ⟨σ,hσH⟩ lives in H.
  have hpH : p ∣ Nat.card H := by
    have h : orderOf σ = orderOf (⟨σ, hσH⟩ : H) :=
      orderOf_injective H.subtype (Subgroup.subtype_injective H) ⟨σ, hσH⟩
    have hτ : orderOf (⟨σ, hσH⟩ : H) = p := h.symm.trans hord
    have hdvd := orderOf_dvd_natCard (⟨σ, hσH⟩ : H)
    rwa [hτ] at hdvd
  -- |P| = p: Sylow card is p^(v_p |H|); v_p |H| ≥ 1 (p ∣ |H|), so p ∣ |P|;
  -- with |P| ∣ p and p prime, |P| = p.
  have hcardP : Nat.card (P : Subgroup H) = p := by
    have hkpos : 0 < (Nat.card H).factorization p :=
      Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hpH
    have hpP : p ∣ Nat.card (P : Subgroup H) := by
      rw [P.card_eq_multiplicity]
      exact dvd_pow_self p hkpos.ne'
    exact Nat.dvd_antisymm hPdvd hpP
  -- Equal finite cardinality + containment ⟹ equality (via the carrier sets).
  have hncS : ((Subgroup.zpowers σ).subgroupOf H : Set H).ncard = p := by
    rw [← Nat.card_coe_set_eq]; exact hcardS
  have hncP : ((P : Subgroup H) : Set H).ncard = p := by
    rw [← Nat.card_coe_set_eq]; exact hcardP
  have hPeq : (Subgroup.zpowers σ).subgroupOf H = (P : Subgroup H) := by
    have hset := Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hPle)
      (le_of_eq (hncS.trans hncP.symm)) (Set.toFinite _)
    exact (SetLike.coe_injective hset).symm
  -- Transport P's normality (hPnorm, Step 2 output) along hPeq.
  haveI : ((Subgroup.zpowers σ).subgroupOf H).Normal := by
    rw [hPeq]; exact hPnorm
  -- Close: Subgroup.le_normalizer_of_normal_subgroupOf.
  exact Subgroup.le_normalizer_of_normal_subgroupOf hle

/-- **Main theorem (COMPLETE — 0 sorry, 0 axiom).** Every primitive solvable
    subgroup of `S_p = Equiv.Perm (ZMod p)` embeds into `AGL(1, p)`.

    This is the full Galois-direction classification (Galois 1832 / Rotman 9.11):
    a solvable transitive group of prime degree `p` is (conjugate into) the
    affine group `AGL(1, p)`. All five steps are now discharged **in this file**
    (no remaining `sorry`, no axiom), so the theorem holds unconditionally:
    - pick a Sylow-`p` subgroup `P` of `↥H` (`Nonempty (Sylow p ↥H)`, `↥H` finite);
    - `sylow_p_unique` (Step 1) — `P` is the *unique* Sylow-`p` of `↥H`, proved
      via a nontrivial abelian characteristic subgroup `A ⊴ ↥H` (from solvability),
      its transitivity (⇒ `p ∣ |A|`), and `v_p(|H|) = v_p(p!) = 1` forcing
      `|P| = p`. (This route replaces the earlier — abandoned — plan that needed a
      socle/minimal-normal-subgroup API absent from Mathlib.)
    - `sylow_p_normal` (Step 2) — unique Sylow ⇒ normal;
    - `sylow_p_is_pcycle` (Step 3) — extract the generating `p`-cycle `σ`, with
      `σ ∈ H`;
    - `H_le_normalizer` (Step 5) — `H ≤ N_{S_p}(⟨σ⟩)`;
    - `normalizer_iso_AGL1Z` (Step 4) — `N_{S_p}(⟨σ⟩) ≅ AGL(1, p)`;
    - the embedding is `ψ ∘ inclusion(H ≤ N)`, injective as a composite of
      injectives (`Subgroup.inclusion_injective`).

    History: assembled researcher-11 S22 (2026-06-18); Steps 1/4 subsequently
    discharged, closing the whole classification. -/
theorem primitive_solvable_subgroup_embeds_AGL1Z
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H) :
    ∃ φ : H →* AGL1Z p, Function.Injective φ := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p H))
  have hPnorm := sylow_p_normal H _hPrim _hSolv P
  obtain ⟨σ, hσc, hσcard, hgen, hσH⟩ := sylow_p_is_pcycle H _hPrim _hSolv P
  have hHle := H_le_normalizer H P hPnorm σ hσc hσcard hgen hσH
  obtain ⟨ψ, hinj, _⟩ := normalizer_iso_AGL1Z σ hσc hσcard
  exact ⟨ψ.comp (Subgroup.inclusion hHle),
    hinj.comp (Subgroup.inclusion_injective hHle)⟩

/-- **Corollary (Galois order bound).** A primitive solvable subgroup of
    `S_p = Equiv.Perm (ZMod p)` has order dividing `p * (p - 1)`.

    This is the classical numeric form of Galois's 1832 theorem: a solvable
    transitive permutation group of prime degree `p` has order dividing
    `p (p - 1) = |AGL(1, p)|`.  It is immediate from
    `primitive_solvable_subgroup_embeds_AGL1Z`: that theorem provides an
    injective group homomorphism `φ : H ↪ AGL(1, p)`, so Lagrange's theorem
    (`Subgroup.card_dvd_of_injective`) gives `|H| ∣ |AGL(1, p)|`, and
    `AGL1Z.nat_card_eq` evaluates the right-hand side as `p (p - 1)`.  No new
    `sorry`, no axiom. -/
theorem primitive_solvable_subgroup_card_dvd
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H) :
    Nat.card H ∣ p * (p - 1) := by
  obtain ⟨φ, hφ⟩ := primitive_solvable_subgroup_embeds_AGL1Z H hPrim hSolv
  have hdvd : Nat.card H ∣ Nat.card (AGL1Z p) := Subgroup.card_dvd_of_injective φ hφ
  rwa [AGL1Z.nat_card_eq] at hdvd

/-- **Corollary (Galois exact order form, Rotman 9.11).** A primitive solvable
    subgroup `H ≤ S_p = Equiv.Perm (ZMod p)` has order `p * m` for some divisor
    `m ∣ (p - 1)`.

    This sharpens `primitive_solvable_subgroup_card_dvd` (`|H| ∣ p (p-1)`): it
    pins down that the prime `p` divides `|H|` *exactly once* and the cofactor
    `m = |H| / p` is a divisor of `p - 1 = |(ℤ/pℤ)ˣ|` — the textbook form of
    Galois's 1832 theorem (Rotman, *Galois Theory*, Thm 9.11: a solvable
    transitive group of prime degree `p` has order `p·d` with `d ∣ p-1`).
    Two ingredients:
    * `p ∣ |H|`: `H` acts transitively on the `p`-element set `ZMod p`
      (primitive ⇒ transitive), so the point-stabiliser has index `p`
      (orbit–stabiliser) and `index ∣ card` (`Subgroup.index_dvd_card`);
    * `|H| ∣ p (p-1)` from `primitive_solvable_subgroup_card_dvd`.
    Writing `|H| = p * m` and cancelling the positive prime `p` from
    `p * m ∣ p * (p-1)` yields `m ∣ (p-1)`.  No new `sorry`, no axiom. -/
theorem primitive_solvable_subgroup_card_eq_prime_mul
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H) :
    ∃ m, m ∣ (p - 1) ∧ Nat.card H = p * m := by
  have hp : p.Prime := Fact.out
  -- `p ∣ |H|` via orbit–stabiliser on the transitive `H`-action on `ZMod p`.
  haveI := hPrim
  have huniv : MulAction.orbit H (0 : ZMod p) = Set.univ :=
    MulAction.orbit_eq_univ H (0 : ZMod p)
  have e : ZMod p ≃ H ⧸ MulAction.stabilizer H (0 : ZMod p) :=
    ((Equiv.Set.univ (ZMod p)).symm.trans (Equiv.setCongr huniv.symm)).trans
      (MulAction.orbitEquivQuotientStabilizer H (0 : ZMod p))
  have hidx : (MulAction.stabilizer H (0 : ZMod p)).index = p := by
    rw [Subgroup.index_eq_card, ← Nat.card_congr e, Nat.card_zmod]
  have hpH : p ∣ Nat.card H := by
    have hdvd := Subgroup.index_dvd_card
      (H := MulAction.stabilizer H (0 : ZMod p))
    rwa [hidx] at hdvd
  -- `|H| ∣ p (p-1)` from the embedding into `AGL(1, p)`.
  have hdvd : Nat.card H ∣ p * (p - 1) :=
    primitive_solvable_subgroup_card_dvd H hPrim hSolv
  obtain ⟨m, hm⟩ := hpH
  refine ⟨m, ?_, hm⟩
  rw [hm] at hdvd
  exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hdvd

end AbelRuffiniGaloisExtensionsOQ06GaloisDirection
