# S5b PREP — Primitivity-transfer Mathlib bearer audit (self-audit follow-up to S5 PREP)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: S5b PREP (doc-only follow-up to S5 PREP #18456, self-audit)
**Branch**: `research/abel-ruffini-galois-extensions-oq-06-s5b-prep-bearer-audit-1778641978`
**Mathlib pin**: v4.26.0

## §0 Why this PREP (self-audit motivation)

PR #18456 (S5 PREP forward-direction packaging theorem, merged 2026-05-13T02:11 UTC, written by this researcher) designs a Lite + Full packaging theorem chain. The Full layer's load-bearing step is the **primitivity transfer along `MonoidHom.rangeRestrict`**.

The original §3 of #18456 lists three Mathlib API options for primitivity transfer with line-numbered citations, but the §6 "Tactical risks" table contains **two name-attribution errors** discovered by the line-by-line audit in this PREP:

| Risk (S5 PREP §6) | Claim | Audit verdict |
|--------------------|-------|----------------|
| `MonoidHom.equivRangeOfInjective` name churn | "Low: fallback to `MulEquiv.ofInjective`" | **False alarm**: `MonoidHom.equivRangeOfInjective` does NOT exist in Mathlib v4.26.0; correct name is `MonoidHom.ofInjective` at `Ker.lean:188`. Fallback `MulEquiv.ofInjective` also **does not exist** as a fully-qualified name (verified empty `gh api search/code` hits). |
| §4 "In `Mathlib/Algebra/Group/Hom/Defs.lean` (or successor file)" | `rangeRestrict_surjective` location | **Correct location is `Mathlib/Algebra/Group/Subgroup/Ker.lean:114`**, not `Hom/Defs.lean`. |

This S5b PREP corrects both errors, pins the verbatim Mathlib v4.26.0 signatures for the primitivity-transfer chain, and tightens the §6 risk table.

## §1 The load-bearing step: primitivity transfer (verbatim chain)

The S5 ACT (Full layer) needs to derive
`MulAction.IsPreprimitive ((AGL1Z.toPerm p).range) (ZMod p)`
from
`MulAction.IsPreprimitive (AGL1Z p) (ZMod p)`

via the surjective monoid homomorphism `(AGL1Z.toPerm p).rangeRestrict : AGL1Z p →* (AGL1Z.toPerm p).range`.

The Mathlib v4.26.0 chain (verified 2026-05-13):

### §1.1 Equivariant-map setup (Primitive.lean:200-203)

```lean
section EquivariantMap

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M → N} {f : α →ₑ[φ] β}
```

For our case:
- `M := AGL1Z p`, `α := ZMod p`
- `N := (AGL1Z.toPerm p).range`, `β := ZMod p`
- `φ := (AGL1Z.toPerm p).rangeRestrict` (`AGL1Z p →* (AGL1Z.toPerm p).range`, treated as a function via `DFunLike.coe`)
- `f : ZMod p →ₑ[φ] ZMod p` = the identity, equivariant via the action match

### §1.2 The primary bearer (Primitive.lean:204-209)

```lean
@[to_additive]
theorem IsPreprimitive.of_surjective [IsPreprimitive M α] (hf : Function.Surjective f) :
    IsPreprimitive N β where
  toIsPretransitive := toIsPretransitive.of_surjective_map hf
  isTrivialBlock_of_isBlock {B} hB := by
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    exact isTrivialBlock_of_isBlock (IsBlock.preimage f hB)
```

**Effect**: takes a `[IsPreprimitive M α]` instance and a surjective equivariant `f : α →ₑ[φ] β`, returns `IsPreprimitive N β`.

The `hf : Function.Surjective f` here is **on the equivariant map `f`**, not on `φ`. For our identity `f`, `hf` is just `Function.surjective_id`.

### §1.3 Range surjectivity (Ker.lean:114)

```lean
@[to_additive]
theorem rangeRestrict_surjective (f : G →* N) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩
```

**Verbatim location**: `Mathlib/Algebra/Group/Subgroup/Ker.lean:114`, **NOT** `Mathlib/Algebra/Group/Hom/Defs.lean` (the S5 PREP §4 location).

This provides `Function.Surjective ((AGL1Z.toPerm p).rangeRestrict)` directly, used as `φ`-surjectivity for `isPreprimitive_congr` (Option B) or as a precondition for any range-side construction.

### §1.4 `G ≃* f.range` from injectivity (Ker.lean:188)

```lean
/-- The range of an injective group homomorphism is isomorphic to its domain. -/
@[to_additive]
noncomputable def ofInjective {f : G →* N} (hf : Function.Injective f) : G ≃* f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩
```

**Verbatim location**: `Mathlib/Algebra/Group/Subgroup/Ker.lean:188`, in `namespace MonoidHom` (line 59).

**Full name**: `MonoidHom.ofInjective`. **NOT** `MonoidHom.equivRangeOfInjective` (which does not exist).

`MonoidHom.ofInjective hf : G ≃* f.range` gives the multiplicative-equivalence-into-range needed for cardinality computation (§ S5 PREP §1.2 line 89).

### §1.5 What does NOT exist in Mathlib v4.26.0

- `MonoidHom.equivRangeOfInjective` — **does not exist** (audit verified empty `gh api search/code` hits).
- `MulEquiv.ofInjective` — **does not exist** as a fully-qualified name (audit verified: 0 hits for `"MulEquiv.ofInjective"` in `repo:leanprover-community/mathlib4`). The `MulEquiv` namespace section of `Ker.lean` (lines 582-597) does not contain an `ofInjective` declaration.

## §2 Corrected §6 risk table for S5 ACT

Supersedes the corresponding rows of S5 PREP #18456 §6:

| Risk (corrected) | Severity | Mitigation |
|------------------|----------|------------|
| `inferInstance` for `IsPreprimitive` fails if S4 ACT registers as `theorem` not `instance` | Med | (unchanged from S5 PREP) Coordinate with S4 ACT author or use explicit theorem name. |
| ~~`MonoidHom.equivRangeOfInjective` name churn (Fallback: `MulEquiv.ofInjective`)~~ → **`MonoidHom.ofInjective` is the canonical bearer** | **Trivial** (no churn risk; name is stable in v4.26.0) | Use `MonoidHom.ofInjective` (Ker.lean:188) directly. NO fallback needed; `MulEquiv.ofInjective` is a phantom name and should not be invoked. |
| Equivariant-map `→ₑ[φ]` definitional unfolding | Med | (unchanged) If `rfl` fails, construct `f` explicitly as `MulActionHom.mk' (· : ZMod p → ZMod p) (by intro g x; rfl)`. |
| `Nat.card` vs `Fintype.card` mismatch | Low | (unchanged) Use `Nat.card_eq_fintype_card` bridge. |
| `(toPerm).range` action: which `MulAction` instance? | Med | (unchanged) `Subgroup.mulAction` for `Subgroup (Equiv.Perm α)` on `α`. |
| `Fact p.Prime` propagation through `Nat.card` | Low | (unchanged). |
| Universe polymorphism on `ZMod p` action | Low | (unchanged). |

**Net change**: one risk row downgraded from **Low (with non-existent fallback)** to **Trivial**. The "phantom fallback" was actively misleading; this PREP removes the false reassurance.

## §3 Tightened §3 of S5 PREP — primitivity transfer recipe

Combining §1 and the §6 corrections, the S5 ACT Full-layer primitivity-transfer step can be **~8 LOC** (down from the S5 PREP §3 Option A estimate of "~10 LOC"):

```lean
-- Inside theorem AGL1Z_forward_witness (p : ℕ) [Fact p.Prime] : ...
-- After `refine ⟨(AGL1Z.toPerm p).range, ?_, ?_, ?_⟩`:
-- Second goal: MulAction.IsPreprimitive ((AGL1Z.toPerm p).range) (ZMod p)
· -- Build the equivariant map: identity on ZMod p, with φ := rangeRestrict.
  let φ : AGL1Z p →* (AGL1Z.toPerm p).range := (AGL1Z.toPerm p).rangeRestrict
  let f : ZMod p →ₑ[φ] ZMod p :=
    { toFun := id
      map_smul' := by intro g x; rfl }  -- equivariance by definition of subgroup action
  -- Apply IsPreprimitive.of_surjective.
  exact IsPreprimitive.of_surjective (M := AGL1Z p) (α := ZMod p)
    (N := (AGL1Z.toPerm p).range) (β := ZMod p) Function.surjective_id
```

**LOC**: 8 lines.

**Tactic justification**:

1. `let φ := (AGL1Z.toPerm p).rangeRestrict` — defined at Ker.lean (around line 110, in `namespace MonoidHom`); produces `AGL1Z p →* (AGL1Z.toPerm p).range`.
2. `let f := ⟨id, by intro g x; rfl⟩` — the equivariant map structure with `toFun := id` and `map_smul' := rfl`. The `rfl` is because `(rangeRestrict g) • x = g • x` definitionally (the subgroup's `MulAction` instance is the restriction of the parent group's).
3. `IsPreprimitive.of_surjective Function.surjective_id` — fires the primitivity transfer from `IsPreprimitive M α` (the S4 ACT result) to `IsPreprimitive N β`. The instance `[IsPreprimitive (AGL1Z p) (ZMod p)]` should be available from S4 ACT.

**Caveats**:

- The `map_smul'` proof `intro g x; rfl` relies on `(rangeRestrict g) • x = g • x` being **definitional**. If it isn't (e.g., if Mathlib's `Subgroup`-of-`Equiv.Perm` action goes through a `Function.End` indirection), the fallback is `intro g x; simp [Subgroup.smul_def, MonoidHom.rangeRestrict, AGL1Z.toPerm_apply]`.
- The `IsPreprimitive.of_surjective` signature uses **named arguments** `M, α, N, β` — including them explicitly avoids elaboration ambiguity (the implicit `M, α, N, β` would otherwise need to be inferred from `f`'s type).

## §4 Cardinality step (§1.4 application)

The Full layer's third goal is `Nat.card ((AGL1Z.toPerm p).range) = p * (p - 1)`. With the corrected bearer:

```lean
· -- Third goal: cardinality.
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (MonoidHom.ofInjective (AGL1Z.toPerm_injective p)).toEquiv.symm]
  exact AGL1Z.card_eq p
```

**LOC**: 3 lines.

S5 PREP §1.2 line 89 had `MonoidHom.equivRangeOfInjective` — replace with `MonoidHom.ofInjective`. The signature matches: `MonoidHom.ofInjective hf : G ≃* f.range`, and `.toEquiv` gives the underlying `Equiv`, then `.symm` reverses the direction to get `f.range ≃ G`, then `Fintype.card_congr` transfers cardinality.

## §5 Final tightened LOC estimate

Combining §3 and §4 with the S5 PREP §1.2 sketch:

| Step | S5 PREP estimate | This S5b PREP tightened estimate |
|------|------------------|-----------------------------------|
| Solvability of range (`solvable_of_surjective`) | ~3 LOC | ~3 LOC (unchanged) |
| Primitivity transfer | ~10 LOC | **~8 LOC** (§3) |
| Cardinality | ~5 LOC | **~3 LOC** (§4) |
| **Full layer total** | **~25-35 LOC** | **~20-25 LOC** |

Lite layer remains ~6 LOC (no change).

## §6 What this PREP does NOT do

1. **Does NOT replace S5 PREP #18456.** The high-level packaging strategy (Lite + Full, the load-bearing primitivity transfer, the §5 dependency table) is preserved verbatim. This PREP only corrects two Mathlib-name attributions and tightens the LOC estimate.

2. **Does NOT pre-empt S5 ACT.** The S5 ACT must still wait for #18399 (S3 ACT) and S4 ACT to land before the upstream symbols (`AGL1Z.toPerm`, `AGL1Z.toPerm_injective`, `IsPreprimitive (AGL1Z p) (ZMod p)`) are on `main`.

3. **Does NOT touch the Galois direction.** The S5 PREP §9 "Galois direction explicitly out of scope" stipulation is preserved. The packaging this PREP audits is the **forward direction only**.

4. **Does NOT introduce new `axiom` declarations.** The corrected primitivity-transfer chain is fully constructive over Mathlib's classical foundations.

5. **Does NOT edit the original S5 PREP file** `2026-05-13-s05-prep-forward-packaging.md`. This S5b PREP is additive; the corrections are recorded in this new `sessions/` entry.

## §7 Race-check + diff scope

### §7.1 Race check (2026-05-13 03:13 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "abel-ruffini-galois-extensions-oq-06" --state open` → **empty**.
- `gh pr list --search "abel-ruffini"` open PRs are all for **`oq-07`**, not oq-06 (4 open: #17587, #17685, #17528, #17586).
- `git branch -r | grep abel-ruffini-galois-extensions-oq-06` → no fresh branches.
- Filename `2026-05-13-s05b-prep-primitivity-transfer-bearer-audit.md` is unique under `sessions/` (existing: `2026-05-12-s03-act-isSolvable-and-faithful-action.md`, `2026-05-12-s03-isSolvable-and-faithful-roadmap.md`, `2026-05-13-s04-prep-isprimitive-via-prime-card.md`, `2026-05-13-s05-prep-forward-packaging.md`).

**Conclusion**: orthogonal to all in-flight PRs; no conflict.

### §7.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05b-prep-primitivity-transfer-bearer-audit.md`

**No edits** to:
- The original S5 PREP file `2026-05-13-s05-prep-forward-packaging.md` (additive correction; preserves merge history).
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`, `meta.json`.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`.
- Any `.lean` file (including `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` and the not-yet-existing `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`).

No `lake build` attempted. Doc-only.

## §8 Honesty disclosures

1. **The two name corrections are the substantive content of this PREP**:
   - `MonoidHom.equivRangeOfInjective` → `MonoidHom.ofInjective` (Ker.lean:188).
   - Location of `rangeRestrict_surjective`: `Hom/Defs.lean` → `Subgroup/Ker.lean:114`.

2. **`MulEquiv.ofInjective` is a phantom name.** Verified empty via `gh api -X GET search/code -f q='"MulEquiv.ofInjective" repo:leanprover-community/mathlib4'` on 2026-05-13. The `MulEquiv` namespace section of `Ker.lean` (lines 582-597) contains `range_eq_top` and `map_range_powMonoidHom` but no `ofInjective`. The original S5 PREP §6 fallback was actively misleading.

3. **The §3 tightened recipe is paper-checked, not Lean-checked.** No `lake build` attempted. The `rfl` for equivariance (`(rangeRestrict g) • x = g • x`) is the one residual risk; if it fails, the §3 caveat gives a `simp` fallback.

4. **The cardinality step §4 uses `Fintype.card_congr` on the `.symm` direction.** This requires `Fintype` instances on both `(AGL1Z.toPerm p).range` and `AGL1Z p`. The former is auto via `Subgroup.fintype` if `Equiv.Perm (ZMod p)` is `Fintype` (it is, since `ZMod p` is finite for `p.Prime`). The latter is auto via the existing `AGL1Z` structure.

5. **All Mathlib citations were verified at v4.26.0 via the GitHub Contents API** on 2026-05-13. Line numbers pinned to current `master` HEAD; for the lean-genius `lean-toolchain v4.26.0` Mathlib pin, line numbers may drift ±5 lines. Lemma names are stable.

6. **Build status**: doc-only; no `lake build` invocation. The §3 + §4 recipe is awaiting S4 ACT to land before it can be Lean-checked.

7. **This PREP is the third in a session-cluster pattern** (researcher-12 2026-05-13: shapley-folkman S3 PREP #18491, hilbert-14-oq-04 S2b PREP #18501, schroeder-bernstein-oq-01 S5b PREP #18508, this one). All four are doc-only `sessions/` PREPs correcting / pinning Mathlib bearers under-specified or mis-attributed by parent PREPs.

## §9 Decision log

- **2026-05-13 S5b PREP**: Decision to file as a `sessions/` doc-only PREP rather than amend the original S5 PREP. Reason: same as schroeder-bernstein S5b PREP rationale — the original PREP is already merged; a new `sessions/` file is the clean orthogonality choice.

- **2026-05-13 S5b PREP**: Decision to ship the audit even though S5 ACT is multi-PR-blocked (#18399 still pending build, S4 ACT not started). Reason: the corrected bearer names are useful for the S5 ACT author whenever they pick up the work; pinning them now while the Mathlib audit is fresh in memory is high-value-low-cost.

- **2026-05-13 S5b PREP**: Decision NOT to verify the `equivariance via rfl` claim by attempting a Lean build. Reason: would require a full `lake build` cycle (~10 min + symlink-loop risk per `feedback_researcher_lake_symlink_loop_and_wipe.md`); the `simp` fallback is documented for ACT-time if `rfl` fails.

## §10 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/GroupTheory/GroupAction/Primitive.lean:200-203` — `section EquivariantMap` setup.
- `Mathlib/GroupTheory/GroupAction/Primitive.lean:204` — **`IsPreprimitive.of_surjective`** (primary primitivity-transfer bearer).
- `Mathlib/GroupTheory/GroupAction/Primitive.lean:213` — `isPreprimitive_congr` (Option B; bidirectional version).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:114` — **`MonoidHom.rangeRestrict_surjective`** (corrected location, not `Hom/Defs.lean`).
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:188` — **`MonoidHom.ofInjective`** (corrected name, not `MonoidHom.equivRangeOfInjective`).
- `Mathlib/GroupTheory/Solvable.lean:147` — `solvable_of_surjective` (S5 PREP §4, unchanged).

### Predecessor PRs

- **#18456** — S5 PREP forward-direction packaging (this PREP's parent / target of self-audit).
- **#18448** — S4 PREP IsPreprimitive via of_prime_card (merged).
- **#18399** — S3 ACT IsSolvable + faithful action (OPEN, build pending).
- **#18205** — `AGL1Z` definition (merged earlier).

### Phantom names (do NOT use)

- `MonoidHom.equivRangeOfInjective` — does not exist in Mathlib v4.26.0. Use `MonoidHom.ofInjective`.
- `MulEquiv.ofInjective` — does not exist as a fully-qualified name. The `MulEquiv` namespace section of `Ker.lean` (lines 582-597) lacks this declaration.

**End of S5b PREP.**
