/-
  TURNKEY ORPHAN DRAFT — Step 1 (`sylow_p_unique`) of the Galois-direction
  classification `Proofs.AbelRuffiniGaloisExtensionsOQ06GaloisDirection`.

  Step 1 is the file's **true blocker** (~70–110 LOC, never previously drafted):
  inside a primitive solvable subgroup `H ≤ S_p`, the Sylow-`p` subgroup of `H`
  is unique. The registered file carries it as a `sorry` stub. The naive
  Sylow-count argument is CIRCULAR (see the registered docstring / knowledge.md
  Risk R4); the sound route goes through the last nontrivial derived-series term.

  ## What this file is

  This is an ORPHAN: NOT imported by `Proofs.lean`, so it is OUTSIDE the
  registered/CI build gate and cannot affect the green registered build. Its
  purpose is to **decompose the monolithic blocker into individually-attackable,
  source-verified sub-lemmas** (the prescribed "STUCK → decompose into concrete
  subgoals" research strategy), so a Docker-up or Aristotle-up session can
  discharge them one at a time instead of facing one 100-LOC wall.

  ## Decomposition (5-step sound route → 4 named obligations)

  - `exists_nontrivial_isMulComm_characteristic_of_solvable`  (Lemma A) —
    **PROVED here** (generic, reusable across sibling solvable-group slugs):
    a nontrivial finite solvable group has a nontrivial *abelian characteristic*
    subgroup `A` (the last nontrivial derived-series term). This is steps 1+4's
    algebra, fully self-contained.
  - `padicValNat_factorial_self`  — **PROVED here** (★, copied verbatim from the
    S17-source-verified Step 3 orphan): `v_p(p!) = 1`. Shared kernel of step 5.
  - `normalSubgroup_isTransitive_of_nontrivial`  (Lemma B) — `sorry`: a
    nontrivial normal subgroup of a faithful primitive action on a `p`-set is
    transitive (block argument). Bearers verified in scope; wiring pending build.
  - `prime_dvd_card_of_isPretransitive`  (Lemma C) — `sorry`: a transitive action
    on `ZMod p` forces `p ∣ |A|` (orbit–stabilizer). Mirrors the Step 3 orphan's
    Step A, transported to `↥A`.
  - `sylow_p_unique`  (assembly) — `sorry` on the remaining transport: package
    `A`'s Sylow `Q` (normal because `A` is abelian) as a Sylow of `↥H` via the
    `ConjAct.normal_of_characteristic_of_normal` instance + `Sylow.ofCard` +
    Legendre, then `Sylow.unique_of_normal`.

  ## Status — SOURCE-VERIFIED, BUILD-PENDING (researcher-2, 2026-06-16, S15-equiv)

  Authored under DUAL BLACKOUT: Aristotle MCP `prove` returns 404
  ("Resource not found"); `docker run` hangs (rc=124, wedged daemon) so
  `docker-build.sh` is unavailable. No local compile possible. Every bearer
  below was re-checked against the offline Mathlib checkout
  `/Users/rwalters/GitHub/mathlib4` at the lake-pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

  Inline confidence: ★ = source-verified name+signature / very standard;
  ? = medium (elaboration / instance-resolution detail wants a first build).

  Bearer table (all confirmed present at the pin):
    ★ `derivedSeries_zero/_succ/_normal`              Solvable.lean:45,49,53
    ★ `derivedSeries_characteristic` (instance)       Solvable.lean:65
    ★ `IsSolvable.solvable` (∃ n, derivedSeries = ⊥)  Solvable.lean:104
    ★ `Subgroup.commutator_eq_bot_iff_le_centralizer` Commutator/Basic.lean:88
    ★ `Subgroup.le_centralizer_iff_isMulCommutative`  Subgroup/Centralizer.lean:89
    ★ `CommGroup.ofIsMulCommutative` (instance)       Algebra/Group/Defs.lean
    ★ `Subgroup.normal_of_comm` (instance)            Algebra/Group/Subgroup/Defs.lean:635
    ★ `Subgroup.nontrivial_iff_ne_bot`                Subgroup/Lattice.lean:200
    ★ `IsBlock.orbit_of_normal`                       GroupAction/Blocks.lean:475
    ★ `IsBlock.subsingleton_or_eq_univ`               GroupAction/Primitive.lean:115
    ★ `isPretransitive_iff_orbit_eq_univ`             GroupAction/Transitive.lean:54
    ★ `card_orbit_mul_card_stabilizer_eq_card_group`  GroupAction/Quotient.lean:180
    ★ `Sylow.characteristic_of_normal`                Sylow.lean:728
    ★ `ConjAct.normal_of_characteristic_of_normal`    GroupAction/ConjAct.lean:260
    ★ `Sylow.ofCard` / `Sylow.coe_ofCard`             Sylow.lean:102,108
    ★ `Sylow.unique_of_normal`                        Sylow.lean:710

  See `research/problems/.../knowledge.md` Risk R4 (§S7/§S8/§S10) for the route
  narrative and the shared `|P| = p` kernel common to Steps 1 and 3.
-/
import Mathlib

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep1

variable {p : ℕ} [Fact p.Prime]

/-- Legendre at the prime `p` itself: `v_p(p!) = 1`.  (★ copied verbatim from the
    S17-source-verified Step 3 orphan; shared kernel of step 5.) -/
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
  have hex : ∃ m : ℕ, derivedSeries G m = ⊥ := IsSolvable.solvable        -- ★
  set d := Nat.find hex with hd_def
  have hd : derivedSeries G d = ⊥ := Nat.find_spec hex                      -- ★
  -- `d > 0`: else `derivedSeries G 0 = ⊤ = ⊥`, contradicting `Nontrivial G`.
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exfalso
      have htop : (⊤ : Subgroup G) = ⊥ := by
        rw [← derivedSeries_zero G, ← h0]; exact hd                         -- ★
      exact top_ne_bot htop                                                 -- ? (Nontrivial (Subgroup G) instance)
    · exact hpos
  -- `A := derivedSeries G (d-1)`.
  refine ⟨derivedSeries G (d - 1), inferInstance, ?_, ?_⟩                   -- ★ derivedSeries_characteristic instance
  · -- nontrivial: `derivedSeries G (d-1) ≠ ⊥` by minimality of `d`.
    rw [Subgroup.nontrivial_iff_ne_bot]                                     -- ★
    exact Nat.find_min hex (Nat.pred_lt hdpos.ne')                          -- ? (d-1 < d)
  · -- abelian: `⁅A,A⁆ = derivedSeries G d = ⊥` ⇒ `A ≤ centralizer A` ⇒ comm.
    have hcomm : ⁅derivedSeries G (d - 1), derivedSeries G (d - 1)⁆ = ⊥ := by
      have hsucc : derivedSeries G (d - 1 + 1)
          = ⁅derivedSeries G (d - 1), derivedSeries G (d - 1)⁆ :=
        derivedSeries_succ G (d - 1)                                        -- ★
      rw [Nat.sub_add_cancel hdpos] at hsucc
      rw [← hsucc]; exact hd
    have hle : derivedSeries G (d - 1) ≤ Subgroup.centralizer (derivedSeries G (d - 1)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm             -- ★
    exact (Subgroup.le_centralizer_iff_isMulCommutative).mp hle            -- ★

/-- **Lemma B (normal ⇒ transitive).** A nontrivial subgroup `A ⊴ H` of a
    faithful primitive action of `H` on the `p`-point set `ZMod p` is transitive.

    Route (bearers in scope): for any `a`, `orbit A a` is a block
    (`IsBlock.orbit_of_normal`), hence subsingleton or univ
    (`IsBlock.subsingleton_or_eq_univ`, using `_hPrim`). `A` nontrivial + faithful
    moves some point `a₀`, so `orbit A a₀` is not subsingleton ⇒ `= univ` ⇒
    `IsPretransitive ↥A (ZMod p)` (`isPretransitive_iff_orbit_eq_univ`).

    ? BUILD-PENDING: the only nontrivial wiring is exhibiting the moved point from
    `Nontrivial ↥A` + `FaithfulSMul ↥H (ZMod p)` (`H ≤ S_p` is faithful). -/
theorem normalSubgroup_isTransitive_of_nontrivial
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (A : Subgroup H) [A.Normal] (_hAnt : Nontrivial A) :
    MulAction.IsPretransitive A (ZMod p) := by
  haveI := _hPrim
  haveI := _hAnt
  -- `A` nontrivial: pick `g ≠ 1` in `A`.
  obtain ⟨g, hg⟩ := exists_ne (1 : A)
  -- Faithfulness of the `A`-action (`A ≤ H ≤ S_p`, faithful via
  -- `Perm.applyFaithfulSMul` and the subgroup instance) yields a moved point.
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
    forces `p ∣ Nat.card A`. Orbit–stabilizer; mirrors the Step 3 orphan's Step A
    transported from `↥H` to `↥A`. -/
theorem prime_dvd_card_of_isPretransitive
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (A : Subgroup H) [MulAction.IsPretransitive A (ZMod p)] :
    p ∣ Nat.card A := by
  -- Orbit–stabilizer in `Nat.card`/index form (mirrors the registered Step 3
  -- `sylow_p_is_pcycle` Step A, transported from `↥H` to `↥A`), avoiding the
  -- `Fintype`-typed orbit-count lemma.
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

/-- **Step 1 (Sylow uniqueness).** Inside a primitive solvable subgroup
    `H ≤ S_p`, the Sylow-`p` subgroup of `H` is unique.

    Assembly from Lemmas A–C + the Legendre/transport step (the residual
    `sorry`):
    1. trivial `H` ⇒ `Subsingleton (Sylow p H)` outright;
    2. else Lemma A gives a nontrivial abelian characteristic `A ⊴ ↥H`;
    3. Lemma B ⇒ `A` transitive; Lemma C ⇒ `p ∣ |A|`;
    4. `A` abelian ⇒ its Sylow `Q` is normal in `↥A`
       (`CommGroup.ofIsMulCommutative` + `normal_of_comm`) ⇒ characteristic
       (`Sylow.characteristic_of_normal`); with `A` characteristic ⇒ normal in
       `↥H`, the instance `ConjAct.normal_of_characteristic_of_normal` gives
       `(Q.map A.subtype).Normal`;
    5. `v_p(|H|) ≤ v_p(p!) = 1` (Legendre) and `p ∣ |A| ∣ |H|` ⇒ `|Q| = p
       = p^(v_p|H|)` ⇒ `Sylow.ofCard` packages `Q.map A.subtype` as `Sylow p ↥H`;
       normal ⇒ `Sylow.unique_of_normal` ⇒ `Subsingleton (Sylow p ↥H)`. -/
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

end AbelRuffiniGaloisExtensionsOQ06GaloisDirectionStep1
