/-
  Primitive Solvable Permutation Groups of Prime Degree — Galois Direction
  (sub-OQ-06)

  This file scaffolds the **Galois direction** of the AGL(1, p) classification:
  every primitive solvable subgroup `H ≤ S_p` embeds into the affine group
  `AGL(1, p) = ℤ/pℤ ⋊ (ℤ/pℤ)ˣ`. The forward direction (that AGL(1, p)
  itself is solvable, primitive, faithful, and of order p(p-1)) is supplied
  by the parent file `Proofs.AbelRuffiniGaloisExtensionsOQ06` (530 LOC,
  0 sorries, 0 axioms, Docker-verified by parent S7 ACT PR #19071).

  ## S2 ORIENT status (researcher-1, 2026-06-04)

  This iteration is the S2 ORIENT scaffold: file-level theorem stub plus
  the 5-step proof skeleton (Sylow uniqueness → P normal → P is p-cycle
  → N_{S_p}(P) ≅ AGL(1, p) → H ≤ N_{S_p}(P)), each step exposed as its
  own intermediate lemma stub with `sorry`. Discharge of the stubs is
  deferred to S3-S6 ACT iterations per `research/problems/.../state.md`.

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
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Type

namespace AbelRuffiniGaloisExtensionsOQ06GaloisDirection

open AbelRuffiniGaloisExtensionsOQ06

variable {p : ℕ} [Fact p.Prime]

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
       `Subgroup.normal_of_characteristic_of_normal`
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
    `Subgroup.normal_of_characteristic_of_normal` cited in step 4. Risk R4
    accordingly stays MEDIUM but the budget shrinks (see knowledge.md R4 §S10).
    Discharge deferred to a Docker-up ACT session. -/
theorem sylow_p_unique
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H) :
    Subsingleton (Sylow p H) := by
  sorry

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

/-- **Step 3 (p-cycle structure).** The Sylow-p subgroup `P` is
    generated by a `p`-cycle in `S_p`. Bearer:
    `Equiv.Perm.isCycle_of_prime_order''` specialized to prime degree. -/
theorem sylow_p_is_pcycle
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H)
    (P : Sylow p H) :
    ∃ σ : Equiv.Perm (ZMod p), σ.IsCycle ∧ σ.support.card = p ∧
      ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈
        Subgroup.zpowers σ := by
  sorry

/-- **Step 4 (Normalizer ≅ AGL(1, p)).** The normalizer of any
    Sylow-p subgroup of `S_p` (generated by a `p`-cycle) is isomorphic
    to `AGL(1, p)` via the conjugation action of `(ℤ/pℤ)ˣ` on `ℤ/pℤ`.

    The isomorphism `N_{S_p}(P) ≅ AGL1Z p` factors through the parent
    file's `AGL1Z.toPerm : AGL1Z p →* Equiv.Perm (ZMod p)`. -/
theorem normalizer_iso_AGL1Z
    (σ : Equiv.Perm (ZMod p)) (_hσ : σ.IsCycle) (_hσ_card : σ.support.card = p) :
    ∃ φ : (Subgroup.zpowers σ).normalizer →* AGL1Z p,
      Function.Injective φ ∧ Function.Surjective φ := by
  sorry

/-- **Step 5 (H ≤ N_{S_p}(P)).** Since the Sylow-p subgroup `P` is
    normal in `H`, the group `H` is contained in the normalizer of `P`
    in `S_p`. Composition with the step-4 isomorphism gives the desired
    embedding `H ↪ AGL(1, p)`.

    ⚠ **UNSOUND STATEMENT — DO NOT DISCHARGE AS WRITTEN** (researcher-5,
    S5 OBSERVE 2026-06-13). The current hypothesis `σ ∈ H` is far too
    weak: it does NOT entail `H ≤ N_{S_p}(⟨σ⟩)`. The conclusion requires
    `⟨σ⟩` to be *normalised* by `H`, which the proof obtains from Step 2
    (`P ⊴ H`) together with Step 3 (`⟨σ⟩ = image of P`) — i.e. `σ` must
    generate the image of the **normal Sylow-p** `P`, not be an arbitrary
    element of `H`. Note the statement does not even require `σ` to be a
    `p`-cycle.

    Explicit counterexample (`p = 5`): let `H = (AGL1Z.toPerm 5).range`
    (primitive + solvable, supplied by the parent file) and `σ = (x ↦ 2x)`,
    the scaling-by-2 map `= (1 2 4 3)`, a 4-cycle fixing `0`, with `σ ∈ H`.
    Take `h = (x ↦ x+1) = (0 1 2 3 4) ∈ H`. Then `h σ h⁻¹ : y ↦ 2y - 1`
    sends `0 ↦ 4`, so it does not fix `0`; but every element of `⟨σ⟩`
    fixes `0`. Hence `h σ h⁻¹ ∉ ⟨σ⟩`, so `h ∉ N_{S_p}(⟨σ⟩)` and
    `H ⊄ N_{S_p}(⟨σ⟩)`. The lemma as stated is therefore false.

    **Corrected signature** (to discharge in a future Docker-up session):
    thread the normal Sylow-p `P` and its `p`-cycle generator through, e.g.
    `(P : Sylow p H) (hPnorm : (P : Subgroup H).Normal)`
    `(hσ_card : σ.support.card = p)`
    `(hgen : ∀ g : P, (H.subtype.comp (P : Subgroup H).subtype) g ∈`
    `  Subgroup.zpowers σ) (hσH : σ ∈ H) ⊢ H ≤ (Subgroup.zpowers σ).normalizer`,
    matching the outputs of Steps 2 (`sylow_p_normal`) and 3
    (`sylow_p_is_pcycle`).

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
    The S5 corrected-signature sketch (and `knowledge.md` Risk R2) omitted
    this hypothesis. Discharge plan once threaded: from `hPnorm`, every
    `h ∈ H` conjugates `ι(P)` to itself; rewrite `ι(P) = ⟨σ⟩` and close with
    `Subgroup.le_normalizer`-style reasoning (~5–15 LOC). See `knowledge.md`
    Risk R2. -/
theorem H_le_normalizer
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H)
    (σ : Equiv.Perm (ZMod p))
    (_hσ_in_H : σ ∈ H) :
    H ≤ (Subgroup.zpowers σ).normalizer := by
  sorry

/-- **Main theorem (file-level stub).** Every primitive solvable subgroup
    of `S_p = Equiv.Perm (ZMod p)` embeds into `AGL(1, p)`.

    Discharge plan: compose
    `sylow_p_unique` → `sylow_p_normal` → `sylow_p_is_pcycle` →
    `normalizer_iso_AGL1Z` → `H_le_normalizer`. See `problem.md` §"Proof
    plan" for the classical (Galois 1832 / Rotman 9.11) recipe. -/
theorem primitive_solvable_subgroup_embeds_AGL1Z
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (_hPrim : MulAction.IsPreprimitive H (ZMod p))
    (_hSolv : IsSolvable H) :
    ∃ φ : H →* AGL1Z p, Function.Injective φ := by
  sorry

end AbelRuffiniGaloisExtensionsOQ06GaloisDirection
