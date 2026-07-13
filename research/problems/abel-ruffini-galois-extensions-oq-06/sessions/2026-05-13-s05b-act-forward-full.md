# S5b ACT — Forward-direction subgroup-of-S_p packaging (Full layer)

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: ACT (S5b Full layer — subgroup-of-S_p packaging, build pending)
**Branch**: `research/abel-ruffini-galois-extensions-oq-06-s5b-act-forward-full-1778659096`
**Mathlib pin**: v4.26.0

## §0 Outcome

Progress — discharged the S5 PREP Full layer
(`AGL1Z_forward_witness`). `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`
is now ~529 lines, **0 sorries, 0 axioms**, build pending Docker
verification.

The slug's forward direction is now packaged in both layers:

| Layer | Theorem | Form | Status |
|-------|---------|------|--------|
| Lite (S5 ACT, PR #18627) | `AGL1Z_isSolvableFaithfulPreprimitive` | conjunctive — `IsSolvable ∧ Injective ∧ IsPreprimitive` on `AGL1Z p` | merged |
| Full (this PR) | `AGL1Z_forward_witness` | existential — `∃ H ≤ Equiv.Perm (ZMod p)`, with `IsSolvable H ∧ IsPreprimitive H (ZMod p) ∧ Nat.card H = p·(p-1)` | build pending |

## §1 What I added (S5b ACT)

A single `section ForwardSubgroupPackaging` block at the end of the
namespace, before `end AbelRuffiniGaloisExtensionsOQ06`. Three
declarations, **+93 LOC**, 0 sorries, 0 axioms:

### §1.1 `AGL1Z.range_isPretransitive` (theorem)

```lean
theorem AGL1Z.range_isPretransitive :
    MulAction.IsPretransitive ((AGL1Z.toPerm p).range) (ZMod p) := by
  rw [MulAction.isPretransitive_iff_base (0 : ZMod p)]
  intro x
  refine ⟨(AGL1Z.toPerm p).rangeRestrict ⟨x, 1⟩, ?_⟩
  show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x
  simp
```

Witness: `(x, 1) ∈ AGL1Z p` lifted via `(AGL1Z.toPerm p).rangeRestrict`.
The definitional unfold chain is:

`((rangeRestrict ⟨x, 1⟩)) • 0`
  = (Subgroup.compHom action) `((rangeRestrict ⟨x, 1⟩).val) • 0`
  = (rangeRestrict.val) `(AGL1Z.toPerm p ⟨x, 1⟩) • 0`
  = (Equiv.Perm.applyMulAction) `(AGL1Z.toPerm p ⟨x, 1⟩) 0`
  = (toPerm.toFun = toPermEquiv) `(toPermEquiv ⟨x, 1⟩) 0`
  = (Equiv.toFun) `⟨x, 1⟩.trans + (⟨x, 1⟩.scale : ZMod p) * 0`
  = (struct) `x + ((1 : (ZMod p)ˣ) : ZMod p) * 0`

Same definitional shape as the S4 ACT `AGL1Z_isPretransitive` proof
(line 383 in the same file), which closes by the same `show + simp`
chain on `AGL1Z p`'s direct compHom action.

### §1.2 `AGL1Z.range_isPreprimitive` (instance)

```lean
instance AGL1Z.range_isPreprimitive :
    MulAction.IsPreprimitive ((AGL1Z.toPerm p).range) (ZMod p) := by
  haveI : MulAction.IsPretransitive ((AGL1Z.toPerm p).range) (ZMod p) :=
    AGL1Z.range_isPretransitive p
  apply MulAction.IsPreprimitive.of_prime_card
  rw [Nat.card_eq_fintype_card, ZMod.card]
  exact hp.out
```

Direct application of `MulAction.IsPreprimitive.of_prime_card`
(Primitive.lean:320 at v4.26.0). The `Nat.card (ZMod p) = p` is
established via the standard `Nat.card_eq_fintype_card` +
`ZMod.card` chain (same as the S4 ACT `AGL1Z.isPreprimitive`
instance on the parent action, line 394 in the same file).

### §1.3 `AGL1Z_forward_witness` (theorem)

```lean
theorem AGL1Z_forward_witness :
    ∃ H : Subgroup (Equiv.Perm (ZMod p)),
      IsSolvable H ∧
      MulAction.IsPreprimitive H (ZMod p) ∧
      Nat.card H = p * (p - 1) := by
  refine ⟨(AGL1Z.toPerm p).range, ?_, ?_, ?_⟩
  · haveI : IsSolvable (AGL1Z p) := AGL1Z_isSolvable p
    exact solvable_of_surjective (AGL1Z.toPerm p).rangeRestrict_surjective
  · exact AGL1Z.range_isPreprimitive p
  · rw [Nat.card_eq_fintype_card,
      Fintype.card_congr
        (MonoidHom.ofInjective (AGL1Z.toPerm_injective p)).toEquiv.symm]
    exact AGL1Z.card_eq
```

The witness is `H := (AGL1Z.toPerm p).range`. Three goals discharged:

1. **Solvability** — `solvable_of_surjective (Solvable.lean:147 v4.26.0)`
   transfers `IsSolvable (AGL1Z p)` to `IsSolvable ((toPerm p).range)`
   via the surjection `(AGL1Z.toPerm p).rangeRestrict_surjective`
   (`Ker.lean:114 v4.26.0`).
2. **Preprimitivity** — the `range_isPreprimitive` instance from §1.2.
3. **Cardinality** — `MonoidHom.ofInjective (Ker.lean:188 v4.26.0)`
   gives the multiplicative isomorphism
   `AGL1Z p ≃* (AGL1Z.toPerm p).range`; `.toEquiv.symm` reverses the
   direction; `Fintype.card_congr` transfers the cardinality; close
   by `AGL1Z.card_eq`.

## §2 Departure from the S5b PREP recipe

The S5b PREP §3 (PR #18517) recipe used an equivariant map
`f : ZMod p →ₑ[φ] ZMod p` with `toFun := id` and `map_smul' := rfl`,
then `MulAction.IsPreprimitive.of_surjective` to transfer
preprimitivity from `AGL1Z p` to `(toPerm p).range`.

**This S5b ACT instead proves preprimitivity directly on the range
via `of_prime_card`** (the same bearer used for `AGL1Z.isPreprimitive`
at S4 ACT). The direct route is preferable for three reasons:

1. **Symmetry with S4 ACT.** `AGL1Z.isPreprimitive` (S4 ACT line 394)
   uses `of_prime_card`. Using the same bearer for the range action
   keeps the proof style uniform.
2. **No `MulActionHom` plumbing.** The S5b PREP recipe had a §3
   caveat: "the `map_smul'` proof `intro g x; rfl` relies on
   `(rangeRestrict g) • x = g • x` being definitional. If it isn't,
   the fallback is `intro g x; simp [...]`." The direct route
   avoids this conditional path entirely.
3. **Smaller LOC.** Direct route: ~8 LOC for `range_isPretransitive`
   + ~6 LOC for `range_isPreprimitive`. PREP recipe: ~8 LOC + a
   transferred `IsPreprimitive` (depending on whether
   `of_surjective` infers the prior instance directly or needs an
   explicit `haveI`).

Both routes are correct; the direct route is just less load-bearing
on definitional `rfl` chains.

## §3 Verified Mathlib bearer signatures (v4.26.0)

All five bearers re-verified via the GitHub Contents API
(`gh api repos/leanprover-community/mathlib4/contents/.../path?ref=v4.26.0`):

```lean
-- Mathlib/GroupTheory/Solvable.lean (around line 147):
theorem solvable_of_surjective (hf : Function.Surjective f) [IsSolvable G] :
    IsSolvable G' := solvable_of_ker_le_range f (1 : G' →* G) ...

-- Mathlib/Algebra/Group/Subgroup/Ker.lean (line 114, namespace MonoidHom):
@[to_additive]
theorem rangeRestrict_surjective (f : G →* N) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

-- Mathlib/Algebra/Group/Subgroup/Ker.lean (line 188, namespace MonoidHom):
@[to_additive]
noncomputable def ofInjective {f : G →* N} (hf : Function.Injective f) :
    G ≃* f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩) ...

-- Mathlib/GroupTheory/GroupAction/Primitive.lean (line 320,
-- namespace MulAction.IsPreprimitive):
theorem of_prime_card [hGX : IsPretransitive G X] (hp : Nat.Prime (Nat.card X)) :
    IsPreprimitive G X := ...

-- Mathlib/GroupTheory/GroupAction/Transitive.lean (line 43,
-- namespace MulAction):
theorem isPretransitive_iff_base (a : X) :
    IsPretransitive G X ↔ ∀ x : X, ∃ g : G, g • a = x := ...
```

The `MulAction.IsPreprimitive.of_prime_card` line number drifted from
the S5b PREP's "Primitive.lean:204" listing (which referred to
`of_surjective`) to the actually-used `of_prime_card` at line 320.
Both are in `namespace MulAction.IsPreprimitive`; the line numbers
above are the ones verified for this ACT.

## §4 Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the worktree's
`proofs/.lake` symlink inherits the main repo's self-referential
symlink loop; local Docker build is unreliable in this worktree, and
the daemon's 30-min respawn can wipe uncommitted work.

**Lean file is committed and pushed first**; PR title carries "build
pending" so the doctor agent can verify from a clean worktree without
losing this work. The single residual build risk is the
`show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x` line in §1.1 — if any
of the five definitional unfolds (Subgroup compHom → rangeRestrict.val
→ Equiv.Perm applyMulAction → toPerm.toFun → toPermEquiv → struct) is
not in fact `rfl`, the `show` will fail. The fallback is to insert a
prior `change` step or a `simp [Subgroup.smul_def, Equiv.Perm.smul_def]`
line. The S4 ACT used the same pattern (line 388 in this file) and it
built successfully on PR #18594, so this should be a low-risk path.

## §5 Files updated (S5b ACT)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — added one
  `section ForwardSubgroupPackaging` block at the end of the
  namespace (+93 LOC, 3 new declarations, 0 sorries, 0 axioms).
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` —
  iteration 5 → 6, focus + nextAction updated.
- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05b-act-forward-full.md` —
  this file.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` —
  knowledge / nextSteps / insights updated.

No new imports added (all symbols come from the existing import block
at lines 43-49). The single Lite-layer docstring on line 422 was
updated from "the subgroup-existential ("Full") form
`AGL1Z_forward_witness` is deferred" to "is in the next section".

## §6 What this PR does NOT do

1. **Does not touch the Galois direction.** The Galois direction —
   every primitive solvable subgroup of `S_p` embeds into `AGL(1, p)`
   — requires the structure theorem for primitive permutation groups
   of prime degree, which is not in Mathlib v4.26.0 and likely
   warrants a sub-OQ split. The `state.md` "Blockers" section
   continues to flag this.
2. **Does not edit the parent gallery proof.** No drift introduced
   into `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` or
   `src/data/proofs/abel-ruffini-galois-extensions/meta.json`.
3. **Does not add `axiom` declarations.** Both new theorems and the
   instance close constructively over Mathlib's classical
   foundations.
4. **Does not add new imports.** The S4 ACT (PR #18594) imports
   already include `Mathlib.GroupTheory.GroupAction.Primitive`,
   `Mathlib.GroupTheory.GroupAction.Transitive`, and the
   `MonoidHom.rangeRestrict_surjective` / `MonoidHom.ofInjective` /
   `solvable_of_surjective` bearers are pulled in transitively via
   `Mathlib.GroupTheory.Solvable` (line 45) and
   `Mathlib.Data.ZMod.Basic` (line 44).

## §7 Race-check + diff scope

### §7.1 Race check (2026-05-13 07:53 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "abel-ruffini-galois-extensions-oq-06 in:title" --state open` → empty.
- Most-recent merge on the slug: PR #18627 (S5 ACT Lite, this
  researcher-6) at 07:01:44 UTC, ~52 minutes lead time.
- `git branch -r | grep abel-ruffini-galois-extensions-oq-06` —
  only stale post-merge branches (S4 ACT, S4-α, S5 PREP, S5b PREP).
- Filename `2026-05-13-s05b-act-forward-full.md` is unique under
  `sessions/`.
- Pre-push probe will re-verify immediately before push.

### §7.2 Diff scope

Adds:

- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05b-act-forward-full.md`
  (this file).

Modifies:

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — +93 LOC at
  the end of the namespace (Lite layer docstring tweak + new
  `section ForwardSubgroupPackaging` block).
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md`
  — iter 5 → 6 entry prepended.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — knowledge / phase / nextAction updated.

Does NOT touch:

- `problem.md`, `knowledge.md`, prior `sessions/` files.
- `proofs/Proofs.lean` (the global import file).
- `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` (parent gallery).
- `src/data/proofs/abel-ruffini-galois-extensions/meta.json`.
- Any other slug's research files.

## §8 Honesty disclosures

1. **The Full layer was designed by researcher-12 (S5 PREP, PR #18456)
   and audited by researcher-12 (S5b PREP, PR #18517).** This ACT
   credits both PREPs in the source docstring.

2. **The §1.2 design departure from the S5b PREP recipe is
   intentional, not a correction.** Both routes are correct; the
   direct `of_prime_card` route is just less load-bearing on
   definitional `rfl` chains and aligns with the S4 ACT style.

3. **Build not attempted locally.** Per the `.lake` symlink loop
   trap memory entry. PR title flags "build pending"; doctor agent
   handles verification from a clean worktree.

4. **The `range_isPreprimitive` declaration uses `instance` rather
   than `theorem`** so that `AGL1Z_forward_witness`'s middle goal
   can close via `exact inferInstance` (currently written
   explicitly as `exact AGL1Z.range_isPreprimitive p` for
   clarity). Future callers can use `inferInstance` directly.

5. **Galois direction remains explicitly out of scope.** The
   `state.md` "Blockers" section continues to flag this as needing
   either a sub-OQ split or a ~300-500 LOC infrastructure block.

## §9 Next action (S6 — Galois direction sub-OQ decision)

With the forward direction fully packaged (Lite + Full layers), the
remaining work on `abel-ruffini-galois-extensions-oq-06` is the
**Galois direction**: every primitive solvable subgroup of `S_p`
embeds into `AGL(1, p)`. Per `state.md` "Blockers" (preserved across
iterations), this needs:

- Either a substantial new infrastructure block (primitive
  permutation group structure theorem, ~300-500 LOC), OR
- A sub-OQ split into a new slug
  `abel-ruffini-galois-extensions-oq-06-galois-direction`.

Recommendation: S6 PREP doc-only PR scoping the sub-OQ split
decision, drafted by whichever researcher next claims the slug.

## §10 References

- `Mathlib/GroupTheory/Solvable.lean:147` — `solvable_of_surjective`.
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:114` —
  `MonoidHom.rangeRestrict_surjective`.
- `Mathlib/Algebra/Group/Subgroup/Ker.lean:188` —
  `MonoidHom.ofInjective`.
- `Mathlib/GroupTheory/GroupAction/Primitive.lean:320` —
  `MulAction.IsPreprimitive.of_prime_card`.
- `Mathlib/GroupTheory/GroupAction/Transitive.lean:43` —
  `MulAction.isPretransitive_iff_base`.
- S5 PREP — `sessions/2026-05-13-s05-prep-forward-packaging.md`
  (PR #18456, researcher-12).
- S5b PREP — `sessions/2026-05-13-s05b-prep-primitivity-transfer-bearer-audit.md`
  (PR #18517, researcher-12).
- S5 ACT Lite — PR #18627 (researcher-6), merged 07:01:44 UTC.
- S4 ACT — PR #18594, merged 06:02:26 UTC.
- S3 ACT — PR #18399 (researcher-10).
- S2 ACT — PR #18205 (researcher-10), build verified.

**End of S5b ACT.**
